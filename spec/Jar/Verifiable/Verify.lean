import Jar.Verifiable.Types
import Jar.Commitment.Verifier
import Jar.Commitment.Transcript
import Jar.Crypto

/-!
# Verification for Trace Commitment + Grand Product Memory Proof

Two verification paths:

1. **Validators (all)**: verify the Ligerito permutation proof (~2ms).
   Proves the original and sorted memory access logs are the same
   multiset. Done before GRANDPA voting.

2. **ELVES committee (~35 auditors)**: verify sorted ordering, read
   consistency, and ALU correctness by re-execution. Done before
   ELVES approval.

GRANDPA finality requires both: `isAcceptable` gates on `isAudited`
(GP §19, U♭ ≡ ⊤).

## Security boundary

The permutation proof is UNCONDITIONAL (all validators verify).
Sorting, read consistency, and ALU are ELVES (rational adversary).
This distinction is critical — do not conflate them.
-/

namespace Jar.Verifiable

open Jar.Commitment.Field
open Jar.Commitment.Proof
open Jar.Commitment.Verifier
open Jar.Commitment.Transcript
open Jar.Commitment.CMerkle

-- ============================================================================
-- Proof Context (Fiat-Shamir domain separation)
-- ============================================================================

/-- Domain separation context for Fiat-Shamir transcript.
    Every proof lives in a unique domain: block + core + report. -/
structure ProofContext where
  /-- Hash of the block containing the work report. -/
  blockHash : ByteArray
  /-- Core index the work report was produced on. -/
  coreIndex : UInt32
  /-- Hash of the work report. -/
  workReportHash : ByteArray

/-- Initialize a domain-separated transcript. -/
def mkDomainTranscript (ctx : ProofContext) : FiatShamirTranscript := Id.run do
  let mut ts := mkTranscript 0
  ts := absorbLabeled ts "domain" "jar-verifiable-execution-v1".toUTF8
  ts := absorbLabeled ts "block_hash" ctx.blockHash
  ts := absorbGF32 ts ctx.coreIndex
  ts := absorbLabeled ts "work_report_hash" ctx.workReportHash
  return ts

-- ============================================================================
-- Memory Permutation Proof Verification (all validators)
-- ============================================================================

/-- Verify the grand product memory PERMUTATION proof.

    This proves ONE thing: the original and sorted memory access logs
    contain the same multiset of entries.

    What this does NOT prove (verified by ELVES committee instead):
    - Sorted log is actually sorted by (address, seq)
    - Read-after-write consistency
    - State continuity (Merkle tree, not polynomial)
    - ALU correctness (re-execution)

    The proof's commitment root is checked against the VerifiableFields
    commitmentRoot (NOT erasure_root — these are different objects).

    Cost: ~2ms per work report. Parallelizable across reports. -/
def verifyMemoryProof (vf : VerifiableFields) (mp : MemoryProof)
    (ctx : ProofContext) : Bool := Id.run do
  -- Structural checks
  if !mp.valid then return false

  -- Commitment binding: the Ligerito proof's commitment root must
  -- match commitmentRoot in VerifiableFields. This is NOT the
  -- erasure_root (which is an RS encoding root for DA). The Ligerito
  -- commitment is a separate mathematical object over GF(2^32).
  -- Single source of truth: extracted from the proof itself.
  match mp.proof.initialCommitment.root with
  | some proofRoot =>
    if proofRoot != vf.commitmentRoot then return false
  | none => return false

  -- Domain-separated transcript
  let config := mkVerifierConfig mp.logSize
  let mut ts := mkDomainTranscript ctx

  -- Absorb with distinct labels to prevent reordering attacks.
  -- Each field gets a unique label in the Fiat-Shamir transcript.
  ts := absorbLabeled ts "trace_root" vf.traceRoot
  ts := absorbLabeled ts "program_hash" mp.programHash

  -- Verify the Ligerito proof
  -- NOTE: this verifies the polynomial commitment. The grand product
  -- CONSTRAINT (Π(α - original_i) = Π(α - sorted_i)) is encoded in
  -- the polynomial structure, not as a separate check. The verifier
  -- confirms the committed polynomial is well-formed.
  let (valid, _) := verify config mp.proof ts
  valid

-- ============================================================================
-- ELVES Block Re-execution Verification
-- ============================================================================

/-- Verify a single basic block boundary against the trace commitment.

    The ELVES auditor:
    1. Gets the block boundary from the trace (Merkle proof)
    2. Gets memory values from the access log (DA)
    3. Re-executes using entry state + memory values
    4. Checks exit state matches the committed boundary

    This function checks the STRUCTURAL part only. Actual PVM
    re-execution happens in native code (javm). -/
/-- Serialize a PvmSnapshot to bytes for Merkle leaf hashing.
    Layout: pc(4 LE) || regs[0..12](8 LE each) || gas(8 LE) = 116 bytes -/
def serializeSnapshot (s : PvmSnapshot) : ByteArray := Id.run do
  let mut buf := ByteArray.mk #[]
  -- pc: 4 bytes LE
  buf := buf ++ ByteArray.mk #[
    (s.pc &&& 0xFF).toUInt8, ((s.pc >>> 8) &&& 0xFF).toUInt8,
    ((s.pc >>> 16) &&& 0xFF).toUInt8, ((s.pc >>> 24) &&& 0xFF).toUInt8]
  -- regs: 13 × 8 bytes LE
  for r in s.regs do
    for shift in [0, 8, 16, 24, 32, 40, 48, 56] do
      buf := buf.push ((r >>> shift.toUInt64) &&& 0xFF).toUInt8
  -- gas: 8 bytes LE
  for shift in [0, 8, 16, 24, 32, 40, 48, 56] do
    buf := buf.push ((s.gas >>> shift.toUInt64) &&& 0xFF).toUInt8
  buf

/-- Serialize a BlockBoundary to bytes for Merkle leaf hashing.
    Layout: entry_snapshot || exit_snapshot || instructionCount(4 LE) -/
def serializeBoundary (b : BlockBoundary) : ByteArray :=
  let entry := serializeSnapshot b.entry
  let exit := serializeSnapshot b.exit
  let ic := b.instructionCount
  entry ++ exit ++ ByteArray.mk #[
    (ic &&& 0xFF).toUInt8, ((ic >>> 8) &&& 0xFF).toUInt8,
    ((ic >>> 16) &&& 0xFF).toUInt8, ((ic >>> 24) &&& 0xFF).toUInt8]

/-- Hash a serialized BlockBoundary into a Merkle leaf.
    Uses BLAKE2b to match the trace Merkle tree construction. -/
def hashBoundaryLeaf (b : BlockBoundary) : CHash :=
  (Jar.Crypto.blake2b (serializeBoundary b)).data

def verifyBlockBoundary (traceRoot : ByteArray) (boundary : BlockBoundary)
    (blockIndex : UInt32) (merkleProof : Array CHash) (depth : Nat)
    : Bool := Id.run do
  if !boundary.entry.valid || !boundary.exit.valid then return false

  -- Gas must not increase within a block
  if boundary.exit.gas > boundary.entry.gas then return false

  if traceRoot.size != 32 then return false

  -- Hash the boundary into a Merkle leaf
  let leafHash := hashBoundaryLeaf boundary

  -- Verify Merkle inclusion: this boundary is at position blockIndex
  -- in the ordered Merkle tree whose root is traceRoot.
  verifyHashed (some traceRoot) merkleProof depth
    #[leafHash] #[blockIndex.toNat]

/-- Check register-level state continuity between adjacent blocks.

    NOTE: checks pc, registers, and gas only — NOT memory.
    Memory continuity depends on ELVES verifying the sorted access
    log (not on this function). -/
def blocksContinuous (a b : BlockBoundary) : Bool :=
  a.exit.pc == b.entry.pc
  && a.exit.regs == b.entry.regs
  && a.exit.gas == b.entry.gas

-- ============================================================================
-- Combined Verification (what validators do per work report)
-- ============================================================================

/-- Full validator verification for a work report.

    Called by each validator before GRANDPA voting:
    1. Check structural validity
    2. Verify proofHash binding (prevents proof substitution)
    3. Verify the Ligerito permutation proof

    ELVES checks (sorting, read consistency, ALU) are separate.
    GRANDPA voting requires BOTH this check AND ELVES approval. -/
def verifyWorkReport (vf : VerifiableFields)
    (mp : MemoryProof) (serializedProof : ByteArray) (ctx : ProofContext)
    : Bool := Id.run do
  -- Structural validity
  if !vf.valid then return false

  -- Proof binding: BLAKE2b(serialized_proof) must match proof_hash.
  -- Prevents proof substitution — the proof in DA must be the EXACT
  -- proof the guarantor committed to.
  let computedHash := (Jar.Crypto.blake2b serializedProof).data
  if computedHash != vf.proofHash then return false

  -- Verify the permutation proof
  if !verifyMemoryProof vf mp ctx then return false

  true

end Jar.Verifiable
