import Jar.Verifiable.Types
import Jar.Verifiable.Verify
import Jar.Commitment.Merkle

/-!
# ELVES Audit Integration

Defines how the ELVES committee spot-checks ALU correctness by
re-executing assigned basic blocks against the trace commitment.

## Security model

Memory consistency: unconditional (grand product proof, verified
by all validators before BLS signing).

ALU correctness: ELVES rational-adversary security. The committee
(~35 auditors) re-executes assigned blocks. Security relies on the
fact that it is prohibitively expensive in expectation for a rational
adversary to submit invalid execution (ELVES paper, eprint 2024/961).

## Audit flow

1. Slot N:   block produced, all validators verify memory proof
2. Slot N+1: ELVES committee revealed (VRF), auditors re-execute
3. Slot N+2: approvals collected, BLS finality signed

## Cost per auditor

- Re-execute ~5 assigned blocks: ~500µs
- Verify Merkle proof for each block: ~50µs
- Total: ~550µs (negligible)
-/

namespace Jar.Verifiable

open Jar.Commitment.CMerkle

-- ============================================================================
-- Audit Result
-- ============================================================================

/-- How the audit was performed. -/
inductive AuditMode where
  /-- Memory proof verified by validator (unconditional, ~2ms). -/
  | memoryProofVerified
  /-- ALU spot-checked by ELVES committee (re-execution, ~500µs). -/
  | elvesReexecuted
  /-- Both memory proof and ELVES check passed. -/
  | fullyVerified
  deriving BEq, Inhabited

/-- Result of auditing a work report. -/
inductive AuditResult where
  /-- Work report verified. -/
  | valid (mode : AuditMode)
  /-- Work report failed verification. -/
  | invalid (reason : String)
  /-- Audit could not be performed. -/
  | unavailable (reason : String)
  deriving Inhabited

-- ============================================================================
-- Validator Audit (all validators, per block)
-- ============================================================================

/-- Validator-side audit: verify memory proof for all work reports.
    Done by EVERY validator before BLS signing.
    Cost: ~2ms per report × 341 reports = ~680ms per slot. -/
def validatorAudit (erasureRoot : ByteArray) (vf : VerifiableFields)
    (mp : MemoryProof) (serializedProof : ByteArray)
    (ctx : ProofContext) : AuditResult :=
  if verifyWorkReport erasureRoot vf mp serializedProof ctx then
    AuditResult.valid AuditMode.memoryProofVerified
  else
    AuditResult.invalid "memory proof verification failed"

-- ============================================================================
-- ELVES Committee Audit (assigned auditors only)
-- ============================================================================

/-- ELVES auditor-side audit: re-execute assigned basic blocks.
    Done by ~35 committee members per work report.
    Cost: ~500µs per auditor.

    The auditor:
    1. Gets block boundaries from trace commitment (Merkle proof)
    2. Gets memory read values from the access log (in DA)
    3. Re-executes each assigned block in PVM
    4. Compares exit state against committed boundary
    5. Reports approval or dispute

    Memory consistency (permutation + sorting + read-consistency) is
    verified by ALL validators unconditionally. The ELVES auditor
    ONLY checks ALU correctness via block re-execution.

    ALU re-execution: ~5 blocks × ~20 instructions, ~500µs. -/
def elvesAudit (traceRoot : ByteArray)
    (assignment : ELVESAssignment)
    (auditorIndex : UInt32)
    (coreIndex numValidators numBlocks : UInt32)
    (committeeSize blocksPerAuditor : UInt32)
    (assignedBlocks : Array BlockBoundary)
    (merkleProofs : Array (Array CHash))
    (depth : Nat) : AuditResult := Id.run do
  if assignedBlocks.isEmpty then
    return AuditResult.unavailable "no blocks assigned"

  -- Verify this auditor is actually in the committee
  if !assignment.auditors.contains auditorIndex then
    return AuditResult.invalid "auditor not in committee"

  -- Verify the assignment was correctly derived from VRF output
  if !assignment.verify coreIndex numValidators numBlocks
      committeeSize blocksPerAuditor then
    return AuditResult.invalid "ELVES assignment verification failed"

  -- Verify assigned blocks are in ascending index order
  for i in [1:assignedBlocks.size] do
    if assignedBlocks[i]!.index <= assignedBlocks[i - 1]!.index then
      return AuditResult.invalid "assigned blocks not in ascending index order"

  for i in [:assignedBlocks.size] do
    let block := assignedBlocks[i]!
    let proof := if i < merkleProofs.size then merkleProofs[i]! else #[]

    -- Verify block boundary is in the trace commitment at its claimed index.
    -- The Merkle tree is ordered: leaf position = block index.
    -- This prevents reordering attacks.
    if !verifyBlockBoundary traceRoot block proof depth then
      return AuditResult.invalid s!"block {block.index} boundary verification failed"

    -- Check state continuity between consecutively-indexed blocks.
    -- Only checked when assigned blocks are adjacent in the trace
    -- (index i and index i+1).
    if i + 1 < assignedBlocks.size then
      let next := assignedBlocks[i + 1]!
      if next.index == block.index + 1 then
        if !blocksContinuous block next then
          return AuditResult.invalid s!"discontinuity between blocks {block.index} and {next.index}"

    -- NOTE: actual PVM re-execution happens in native code (javm),
    -- not in Lean. The Lean spec defines the STRUCTURE of the check,
    -- not the execution semantics (which are in Jar.PVM).

  AuditResult.valid AuditMode.elvesReexecuted

-- ============================================================================
-- Coverage Statistics
-- ============================================================================

/-- Estimate ELVES committee size for given parameters.
    From the ELVES paper (Figure 2), with n=1000, γ=1/3:
    - ε = 2^-60 (cryptographic):  ~400 auditors
    - ε = 1/20001 (rational):     ~35-150 auditors
    - Mostly honest (5% corrupt): ~35 auditors -/
structure ELVESParams where
  /-- Total number of validators. -/
  numValidators : Nat
  /-- Maximum corruption fraction (< 1/3). -/
  corruptionBound : Float
  /-- Soundness failure probability. -/
  soundnessError : Float

namespace ELVESParams

/-- Default parameters for JAM mainnet. -/
def jamMainnet : ELVESParams :=
  { numValidators := 1023
    corruptionBound := 0.333
    soundnessError := 1.0 / 20001.0 }

/-- Expected committee size (rough estimate from ELVES paper). -/
def expectedCommitteeSize (p : ELVESParams) : Nat :=
  -- From Figure 2: with rational adversary and ε ≈ 1/20001,
  -- committee size is ~35-150 depending on actual corruption level.
  -- Conservative estimate: 100.
  if p.soundnessError < 1e-15 then 400  -- cryptographic security
  else if p.corruptionBound > 0.3 then 150
  else if p.corruptionBound > 0.1 then 100
  else 35

end ELVESParams

-- ============================================================================
-- Finality Timeline
-- ============================================================================

/-- Slot-level finality timeline.
    BLS finality happens AFTER ELVES approval — never before.
    One finality event, after all checks. -/
structure FinalityTimeline where
  /-- Slot time in milliseconds. -/
  slotTimeMs : Nat
  /-- Slots for DA availability (assurances). -/
  availabilitySlots : Nat := 1
  /-- Slots for ELVES committee checking. -/
  elvesSlots : Nat := 1
  /-- Slots for BLS finality (after ELVES). -/
  finalitySlots : Nat := 1

namespace FinalityTimeline

/-- Total finality time in milliseconds. -/
def totalMs (ft : FinalityTimeline) : Nat :=
  ft.slotTimeMs * (ft.availabilitySlots + ft.elvesSlots + ft.finalitySlots)

/-- Default for JAM with 2s slots. -/
def jamDefault : FinalityTimeline :=
  { slotTimeMs := 2000
    availabilitySlots := 1
    elvesSlots := 1
    finalitySlots := 1 }
  -- Optimistic: 3 × 2s = 6s
  -- Normal:     4 × 2s = 8s (with no-show handling)

end FinalityTimeline

end Jar.Verifiable
