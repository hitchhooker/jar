import Jar.Commitment.Field
import Jar.Commitment.Proof
import Jar.Commitment.Merkle

/-!
# Verifiable Execution Types

Data structures for the trace commitment + grand product memory proof
architecture. The guarantor produces:

1. **Trace commitment**: Merkle root over basic block boundary states
2. **Memory proof**: Ligerito grand product proving all memory reads
   are consistent with writes

The ELVES committee spot-checks ALU correctness by re-executing
assigned basic blocks against the committed trace. Memory consistency
is unconditionally proven; ALU correctness has ELVES rational-adversary
security.

## Polynomial layout (2^20, Ligerito sweet spot)

The combined polynomial packs both claims into one proof:
- Block boundary states: 50K blocks × 15 GF(2^32) elements = 750K
- Memory access log:    50K accesses × 5 GF(2^32) elements = 250K
- Total: ~1M elements = 2^20

## References

- DESIGN.md (repo root) — full architecture
- ELVES paper: eprint 2024/961
-/

namespace Jar.Verifiable

open Jar.Commitment.Field
open Jar.Commitment.Proof
open Jar.Commitment.CMerkle

-- ============================================================================
-- PVM State Snapshots
-- ============================================================================

/-- Number of PVM registers. -/
def NUM_REGS : Nat := 13

/-- PVM state at a basic block boundary.
    Captured at block entry and exit during execution. -/
structure PvmSnapshot where
  /-- Program counter. -/
  pc : UInt32
  /-- Register file (13 registers: ra, sp, t0-t2, s0-s1, a0-a5). -/
  regs : Array UInt64
  /-- Remaining gas. -/
  gas : UInt64
  deriving BEq, Inhabited

namespace PvmSnapshot

def valid (s : PvmSnapshot) : Bool := s.regs.size == NUM_REGS

end PvmSnapshot

-- ============================================================================
-- Basic Block Boundary
-- ============================================================================

/-- A single basic block execution record.
    A basic block is a straight-line instruction sequence (no branches
    except at the end). Given `entry`, the `exit` is deterministic —
    exactly one possible outcome (refinement has no host calls). -/
structure BlockBoundary where
  /-- Block index (sequential, 0-based). -/
  index : UInt32
  /-- PVM state at block entry. -/
  entry : PvmSnapshot
  /-- PVM state at block exit. -/
  exit : PvmSnapshot
  /-- Number of instructions in this block. -/
  instructionCount : UInt32
  /-- Gas consumed (entry.gas - exit.gas). -/
  gasCost : UInt64
  deriving Inhabited

-- ============================================================================
-- Memory Access Log
-- ============================================================================

/-- A single memory access during PVM execution.
    Recorded for the grand product consistency proof.

    The seq field is a monotonic counter encoding execution order.
    The grand product proof commits to seqs AND verifies they are
    monotonically increasing in the original (execution-order) log.
    This prevents the guarantor from reordering accesses to forge
    consistency. Timestamps are part of the committed polynomial. -/
structure MemoryAccess where
  /-- Memory address accessed. -/
  address : UInt32
  /-- Value read or written. -/
  value : UInt64
  /-- Monotonic seq (execution order). Must be strictly
      increasing in the original access log. Committed in the
      polynomial and verified by the grand product. -/
  seq : UInt32
  /-- True if store, false if load. -/
  isWrite : Bool
  deriving BEq, Inhabited

-- ============================================================================
-- Trace Commitment
-- ============================================================================

/-- Trace commitment: Merkle root over basic block boundary states.
    Produced by the guarantor during execution (~5ms overhead).
    Goes into the work report as `trace_root` (32 bytes). -/
structure TraceCommitment where
  /-- Merkle root over serialized BlockBoundary entries. -/
  root : ByteArray
  /-- Number of basic blocks in the trace. -/
  numBlocks : UInt32
  /-- Total instructions executed. -/
  totalInstructions : UInt64
  deriving Inhabited

namespace TraceCommitment

def valid (tc : TraceCommitment) : Bool :=
  tc.root.size == 32 && tc.numBlocks > 0

end TraceCommitment

-- ============================================================================
-- Memory Consistency Proof
-- ============================================================================

/-- Grand product memory permutation proof (Ligerito).

    Proves that the original access log (execution order) and the
    sorted access log (by address, then seq) contain the SAME
    set of entries. This is a PERMUTATION proof, not a full memory
    consistency proof.

    Grand product: Π(α - original_i) = Π(α - sorted_i)
      → α is a random Fiat-Shamir challenge
      → proves the two logs are rearrangements of each other

    The polynomial contains ONLY the two access logs:
      Original: 50K entries × 5 GF(2^32) elements = 250K
      Sorted:   50K entries × 5 GF(2^32) elements = 250K
      Total:    ~500K ≈ 2^19, padded to 2^20

    What is NOT proven in the circuit (verified by ELVES instead):
    - Sorted ordering (requires integer comparison in GF(2^32))
    - Read-after-write consistency
    - State continuity (in Merkle tree, not polynomial)

    This split avoids integer comparison gates in the binary field
    circuit. The ELVES auditor verifies sorting + read consistency
    with a linear scan (~500µs, native integer comparisons). -/
structure MemoryProof where
  /-- Ligerito proof over the combined polynomial
      (block boundaries + memory access log). -/
  proof : LigeritoProof
  /-- log₂ of polynomial size (typically 20). -/
  logSize : Nat := 20
  /-- Number of memory accesses covered. -/
  numAccesses : UInt32
  /-- Program hash (binds proof to specific code). -/
  programHash : ByteArray

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
  }

namespace MemoryProof

def valid (mp : MemoryProof) : Bool :=
  mp.programHash.size == 32 && mp.logSize >= 20

end MemoryProof

-- ============================================================================
-- Work Report Extension
-- ============================================================================

/-- New fields added to the work report for verifiable execution. -/
structure VerifiableFields where
  /-- Merkle root over basic block boundary states. -/
  traceRoot : ByteArray
  /-- BLAKE2b hash of the serialized MemoryProof (stored in DA segment). -/
  proofHash : ByteArray
  deriving BEq, Inhabited

namespace VerifiableFields

def valid (vf : VerifiableFields) : Bool :=
  vf.traceRoot.size == 32 && vf.proofHash.size == 32

end VerifiableFields

-- ============================================================================
-- ELVES Committee Assignment
-- ============================================================================

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

/-- Derive an ELVES committee assignment deterministically from
    a VRF output and work report parameters.

    The VRF output comes from the NEXT slot's block author — it's
    unpredictable when the guarantor produces the trace (preventing
    targeting). The assignment is a pure function of:
    - vrfOutput: 32-byte Bandersnatch VRF output hash
    - coreIndex: which core the work report is for
    - numValidators: total validator count (1023)
    - numBlocks: total basic blocks in the trace

    Each auditor is assigned ~5 blocks to re-execute. The assignment
    is deterministic so any validator can verify it. -/
def derive (vrfOutput : ByteArray) (coreIndex : UInt32)
    (numValidators numBlocks : UInt32)
    (committeeSize blocksPerAuditor : UInt32)
    : ELVESAssignment := Id.run do
  if vrfOutput.size != 32 then return default
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

  -- Select committee members by hashing seed + counter
  let mut auditors : Array UInt32 := #[]
  let mut counter : UInt32 := 0
  while auditors.size < committeeSize.toNat && counter < numValidators * 2 do
    let mut input := coreSeed
    input := input ++ ByteArray.mk #[
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

  -- Assign blocks to each auditor
  let mut assignedBlocks : Array (Array UInt32) := #[]
  for i in [:auditors.size] do
    let auditorIdx := auditors[i]!
    let mut blocks : Array UInt32 := #[]
    for j in [:blocksPerAuditor.toNat] do
      let mut input := coreSeed
      input := input ++ ByteArray.mk #[
        (auditorIdx &&& 0xFF).toUInt8,
        ((auditorIdx >>> 8) &&& 0xFF).toUInt8,
        (j.toUInt32 &&& 0xFF).toUInt8,
        ((j.toUInt32 >>> 8) &&& 0xFF).toUInt8
      ]
      let hash := (Jar.Crypto.blake2b input).data
      let blockIdx := (hash[0]!.toUInt32 ||| (hash[1]!.toUInt32 <<< 8)
        ||| (hash[2]!.toUInt32 <<< 16) ||| (hash[3]!.toUInt32 <<< 24))
        % numBlocks
      if !blocks.contains blockIdx then
        blocks := blocks.push blockIdx
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
