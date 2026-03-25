import Jar.Commitment.Field
import Jar.Commitment.Proof
import Jar.Commitment.Merkle

/-!
# Verifiable Execution Types

Data structures for the trace commitment + grand product memory proof.

## Architecture

The guarantor produces two artifacts per work report:
1. **Trace commitment**: Merkle root over basic block boundary states
2. **Memory proof**: Ligerito grand product proving memory access logs
   are a permutation (original order ↔ sorted order)

The ELVES committee verifies:
- Sorted ordering of the memory log (linear scan)
- Read-after-write consistency (linear scan)
- ALU correctness (basic block re-execution)

## Polynomial layout

The polynomial contains ONLY memory access logs (block boundaries
are committed via Merkle tree, NOT in the polynomial):

  Original access log: N entries × 6 GF(2^32) elements
  Sorted access log:   N entries × 6 GF(2^32) elements
  Total: 12N elements

Each entry is 6 GF(2^32) elements:
  addr(1) + value_lo(1) + value_hi(1) + seq(1) + width(1) + flags(1)

For 50K accesses: 12 × 50K = 600K ≈ 2^20.

## Security model

- Permutation: unconditional (Ligerito grand product, all validators)
- Sorted ordering + read consistency: ELVES (rational adversary)
- ALU correctness: ELVES (rational adversary)
- State continuity: ELVES (Merkle proof + re-execution)

Note: "unconditional" applies only to the permutation check.
Sorting and read-consistency depend on ELVES committee honesty.
-/

namespace Jar.Verifiable

open Jar.Commitment.Field
open Jar.Commitment.Proof
open Jar.Commitment.CMerkle

-- ============================================================================
-- PVM State Snapshots
-- ============================================================================

/-- Number of PVM registers (rv64em: ra, sp, t0-t2, s0-s1, a0-a5). -/
def NUM_REGS : Nat := 13

/-- PVM state at a basic block boundary.
    Captured at block entry and exit during execution. -/
structure PvmSnapshot where
  /-- Program counter (ı). -/
  pc : UInt32
  /-- Register file (13 registers). -/
  regs : Array UInt64
  /-- Remaining gas (ϱ). -/
  gas : UInt64
  deriving BEq, Inhabited

namespace PvmSnapshot

def valid (s : PvmSnapshot) : Bool := s.regs.size == NUM_REGS

end PvmSnapshot

-- ============================================================================
-- Basic Block Boundary
-- ============================================================================

/-- A single basic block execution record.

    A basic block is a straight-line instruction sequence ending at a
    terminator. Given `entry` state AND memory read values, the `exit`
    state is deterministic. Note: refinement CAN invoke host calls
    (peek, poke, fetch, etc. per GP §14.3), so determinism requires
    the memory access log as input, not just the entry register state. -/
structure BlockBoundary where
  /-- PVM state at block entry. -/
  entry : PvmSnapshot
  /-- PVM state at block exit. -/
  exit : PvmSnapshot
  /-- Number of instructions in this block. -/
  instructionCount : UInt32
  deriving BEq, Inhabited

namespace BlockBoundary

/-- Gas consumed by this block (derived, not stored). -/
def gasCost (b : BlockBoundary) : UInt64 := b.entry.gas - b.exit.gas

end BlockBoundary

-- ============================================================================
-- Memory Access Log
-- ============================================================================

/-- Access width in bytes (1, 2, 4, or 8). Matches PVM load/store
    instruction widths (lb/lh/lw/ld, sb/sh/sw/sd). -/
inductive AccessWidth where
  | byte1 | byte2 | byte4 | byte8
  deriving BEq, Inhabited

/-- A single memory access during PVM execution.
    Recorded for the grand product permutation proof.

    The `seq` field is a monotonic counter (0, 1, 2, ...) encoding
    execution order. The polynomial constrains seq_i == i for uniqueness.
    Without this, the grand product (multiset equality) would allow
    the guarantor to duplicate entries. -/
structure MemoryAccess where
  /-- Memory address accessed. -/
  address : UInt32
  /-- Value read or written (up to 8 bytes, little-endian). -/
  value : UInt64
  /-- Monotonic sequence number (execution order). -/
  seq : UInt32
  /-- Access width (1, 2, 4, or 8 bytes). -/
  width : AccessWidth
  /-- True if store, false if load. -/
  isWrite : Bool
  deriving BEq, Inhabited

-- ============================================================================
-- Trace Commitment
-- ============================================================================

/-- Trace commitment: Merkle root over basic block boundary states.
    Produced by the guarantor during execution.
    Goes into the work report's availability segment. -/
structure TraceCommitment where
  /-- Merkle root over serialized BlockBoundary entries.
      Leaf i = serialized BlockBoundary for block i (ordered). -/
  root : ByteArray
  /-- Number of basic blocks in the trace. -/
  numBlocks : UInt32
  deriving BEq, Inhabited

namespace TraceCommitment

def valid (tc : TraceCommitment) : Bool :=
  tc.root.size == 32 && tc.numBlocks > 0

end TraceCommitment

-- ============================================================================
-- Memory Consistency Proof
-- ============================================================================

/-- Maximum log₂ polynomial size accepted by validators.
    Limits verifier work. Programs exceeding this must split proofs
    or fall back to pure ELVES re-execution. -/
def MAX_LOG_SIZE : Nat := 24  -- 2^24 = 16M elements

/-- Grand product memory permutation proof (Ligerito).

    Proves that the original access log (execution order) and the
    sorted access log (by address, then seq) are the SAME multiset.

    Grand product: Π(α - original_i) = Π(α - sorted_i)

    The polynomial contains ONLY the two access logs. Block boundaries
    are in the Merkle tree (TraceCommitment), NOT in the polynomial.

    What the proof does NOT cover (verified by ELVES committee):
    - Sorted ordering (integer comparison in GF(2^32) is expensive)
    - Read-after-write consistency
    - State continuity (Merkle tree + re-execution) -/
structure MemoryProof where
  /-- Ligerito proof over the permutation polynomial. -/
  proof : LigeritoProof
  /-- log₂ of polynomial size. -/
  logSize : Nat := 20
  /-- Number of memory accesses covered. -/
  numAccesses : UInt32
  /-- Program hash (binds proof to specific code). -/
  programHash : ByteArray
  /-- Ligerito commitment root. This is NOT the erasure_root —
      it is a separate commitment over the GF(2^32) polynomial.
      Must be verified independently from the DA erasure root. -/
  commitmentRoot : ByteArray

instance : Inhabited MemoryProof where
  default := {
    proof := {
      initialCommitment := default
      initialOpening := { openedRows := #[], merkleProof := #[] }
      recursiveCommitments := #[]
      recursiveOpenings := #[]
      finalOpening := { yr := #[], openedRows := #[], merkleProof := #[] }
      sumcheckRounds := { transcript := #[] }
    }
    logSize := 20
    numAccesses := 0
    programHash := ByteArray.mk #[]
    commitmentRoot := ByteArray.mk #[]
  }

namespace MemoryProof

def valid (mp : MemoryProof) : Bool :=
  mp.programHash.size == 32
  && mp.commitmentRoot.size == 32
  && mp.logSize >= 20
  && mp.logSize <= MAX_LOG_SIZE

end MemoryProof

-- ============================================================================
-- Work Report Extension
-- ============================================================================

/-- New fields for verifiable execution, carried in the work report's
    availability segment (NOT overloading erasure_root). -/
structure VerifiableFields where
  /-- Merkle root over basic block boundary states. -/
  traceRoot : ByteArray
  /-- BLAKE2b hash of the serialized MemoryProof. -/
  proofHash : ByteArray
  /-- Ligerito commitment root (separate from erasure_root). -/
  commitmentRoot : ByteArray
  deriving BEq, Inhabited

namespace VerifiableFields

def valid (vf : VerifiableFields) : Bool :=
  vf.traceRoot.size == 32
  && vf.proofHash.size == 32
  && vf.commitmentRoot.size == 32

end VerifiableFields

-- ============================================================================
-- ELVES Committee Assignment
-- ============================================================================

/-- Domain tag for committee member selection hashes. -/
def ELVES_COMMITTEE_TAG : UInt8 := 0x01

/-- Domain tag for block assignment hashes. -/
def ELVES_BLOCK_TAG : UInt8 := 0x02

/-- ELVES committee assignment for a work report.
    Determined by VRF from the NEXT slot's block — the committee is
    unknown when the guarantor commits to the trace. -/
structure ELVESAssignment where
  /-- Validator indices assigned to this work report. -/
  auditors : Array UInt32
  /-- Basic block indices each auditor must re-execute. -/
  assignedBlocks : Array (Array UInt32)
  /-- VRF output that generated this assignment (32 bytes). -/
  vrfOutput : ByteArray
  deriving Inhabited

namespace ELVESAssignment

/-- Derive an ELVES committee assignment deterministically from VRF.

    Domain separation: committee selection uses tag 0x01, block
    assignment uses tag 0x02, preventing hash input collisions
    (Komlo review). -/
def derive (vrfOutput : ByteArray) (coreIndex : UInt32)
    (numValidators numBlocks : UInt32)
    (committeeSize blocksPerAuditor : UInt32)
    : ELVESAssignment := Id.run do
  if vrfOutput.size != 32 then return default
  if numValidators == 0 then return default
  if numBlocks == 0 then return default
  -- Derive per-core seed: BLAKE2b("jar-elves-v1" || vrfOutput || coreIndex)
  let mut seedInput := "jar-elves-v1".toUTF8
  seedInput := seedInput ++ vrfOutput
  seedInput := seedInput ++ ByteArray.mk #[
    (coreIndex &&& 0xFF).toUInt8,
    ((coreIndex >>> 8) &&& 0xFF).toUInt8,
    ((coreIndex >>> 16) &&& 0xFF).toUInt8,
    ((coreIndex >>> 24) &&& 0xFF).toUInt8
  ]
  let coreSeed := (Jar.Crypto.blake2b seedInput).data

  -- Select committee members (domain tag 0x01)
  let mut auditors : Array UInt32 := #[]
  let mut counter : UInt32 := 0
  while auditors.size < committeeSize.toNat && counter < numValidators * 3 do
    let mut input := coreSeed
    input := input ++ ByteArray.mk #[
      ELVES_COMMITTEE_TAG,
      (counter &&& 0xFF).toUInt8,
      ((counter >>> 8) &&& 0xFF).toUInt8,
      ((counter >>> 16) &&& 0xFF).toUInt8,
      ((counter >>> 24) &&& 0xFF).toUInt8
    ]
    let hash := (Jar.Crypto.blake2b input).data
    let idx := (hash[0]!.toUInt32 ||| (hash[1]!.toUInt32 <<< 8)
      ||| (hash[2]!.toUInt32 <<< 16) ||| (hash[3]!.toUInt32 <<< 24))
      % numValidators
    if !auditors.contains idx then
      auditors := auditors.push idx
    counter := counter + 1

  -- Assign blocks to each auditor (domain tag 0x02)
  let mut assignedBlocks : Array (Array UInt32) := #[]
  for i in [:auditors.size] do
    let auditorIdx := auditors[i]!
    let mut blocks : Array UInt32 := #[]
    let mut bCounter : UInt32 := 0
    while blocks.size < blocksPerAuditor.toNat && bCounter < numBlocks do
      let mut input := coreSeed
      input := input ++ ByteArray.mk #[
        ELVES_BLOCK_TAG,
        (auditorIdx &&& 0xFF).toUInt8,
        ((auditorIdx >>> 8) &&& 0xFF).toUInt8,
        (bCounter &&& 0xFF).toUInt8,
        ((bCounter >>> 8) &&& 0xFF).toUInt8
      ]
      let hash := (Jar.Crypto.blake2b input).data
      let blockIdx := (hash[0]!.toUInt32 ||| (hash[1]!.toUInt32 <<< 8)
        ||| (hash[2]!.toUInt32 <<< 16) ||| (hash[3]!.toUInt32 <<< 24))
        % numBlocks
      if !blocks.contains blockIdx then
        blocks := blocks.push blockIdx
      bCounter := bCounter + 1
    assignedBlocks := assignedBlocks.push blocks

  { auditors, assignedBlocks, vrfOutput }

/-- Verify that an assignment was correctly derived from the VRF output. -/
def verify (a : ELVESAssignment) (coreIndex numValidators numBlocks
    committeeSize blocksPerAuditor : UInt32) : Bool :=
  let expected := derive a.vrfOutput coreIndex numValidators numBlocks
    committeeSize blocksPerAuditor
  a.auditors == expected.auditors && a.assignedBlocks == expected.assignedBlocks

end ELVESAssignment

end Jar.Verifiable
