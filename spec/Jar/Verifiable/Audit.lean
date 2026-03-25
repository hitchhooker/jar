import Jar.Verifiable.Types
import Jar.Verifiable.Verify
import Jar.Commitment.Merkle

/-!
# ELVES Audit Integration

The ELVES committee spot-checks work reports by:
1. Verifying the sorted memory log is correctly ordered
2. Verifying read-after-write consistency
3. Re-executing assigned basic blocks for ALU correctness

## Security model

- Permutation: unconditional (Ligerito, all validators)
- Sorting + read consistency: ELVES (rational adversary)
- ALU correctness: ELVES (rational adversary)
- State continuity: ELVES (Merkle proof + re-execution)

GRANDPA finality requires `isAudited == true` (GP §19).
`isAudited` means ALL work reports in the block have sufficient
ELVES approvals. The aggregation logic that computes this boolean
from individual approvals is NOT specified here — it lives in the
consensus/approval-voting layer.
-/

namespace Jar.Verifiable

open Jar.Commitment.CMerkle

-- ============================================================================
-- Audit Result
-- ============================================================================

/-- Result of auditing a work report. -/
inductive AuditResult where
  /-- Work report passed all checks. -/
  | valid
  /-- Work report failed verification. -/
  | invalid (reason : String)
  /-- Audit could not be performed (data unavailable). -/
  | unavailable (reason : String)
  deriving Inhabited

-- ============================================================================
-- Validator Audit (all validators, per block)
-- ============================================================================

/-- Validator-side: verify the permutation proof for a work report.
    Done by EVERY validator before GRANDPA voting.
    This proves ONLY that the two memory logs are the same multiset.
    Cost: ~2ms per report × 341 reports = ~680ms sequential. -/
def validatorAudit (vf : VerifiableFields)
    (mp : MemoryProof) (serializedProof : ByteArray)
    (ctx : ProofContext) : AuditResult :=
  if verifyWorkReport vf mp serializedProof ctx then
    AuditResult.valid
  else
    AuditResult.invalid "permutation proof verification failed"

-- ============================================================================
-- ELVES Committee Audit (assigned auditors only)
-- ============================================================================

/-- ELVES auditor-side: validate audit inputs before re-execution.

    This function checks structural prerequisites:
    1. Auditor is in the committee
    2. Assignment matches VRF derivation
    3. Block boundaries pass Merkle verification
    4. Adjacent blocks have state continuity

    Actual PVM re-execution, sorted-log scanning, and read-consistency
    checking happen in native code (javm), not in this spec.
    This function validates INPUTS to that process. -/
def validateAuditInputs (traceRoot : ByteArray)
    (assignment : ELVESAssignment)
    (auditorIndex : UInt32)
    (coreIndex numValidators numBlocks : UInt32)
    (committeeSize blocksPerAuditor : UInt32)
    (assignedBlocks : Array BlockBoundary)
    (blockIndices : Array UInt32)
    (merkleProofs : Array (Array CHash))
    : AuditResult := Id.run do
  if assignedBlocks.isEmpty then
    return AuditResult.unavailable "no blocks assigned"

  if assignedBlocks.size != blockIndices.size then
    return AuditResult.invalid "block count mismatch with index count"

  -- Verify this auditor is in the committee
  if !assignment.auditors.contains auditorIndex then
    return AuditResult.invalid "auditor not in committee"

  -- Verify the assignment was correctly derived from VRF output
  if !assignment.verify coreIndex numValidators numBlocks
      committeeSize blocksPerAuditor then
    return AuditResult.invalid "ELVES assignment verification failed"

  -- Verify block indices are ascending (prevents reordering)
  for i in [1:blockIndices.size] do
    if blockIndices[i]! <= blockIndices[i - 1]! then
      return AuditResult.invalid "block indices not ascending"

  for i in [:assignedBlocks.size] do
    let block := assignedBlocks[i]!
    let idx := blockIndices[i]!
    let proof := if i < merkleProofs.size then merkleProofs[i]! else #[]

    -- Verify block boundary is in the trace at its claimed index
    if !verifyBlockBoundary traceRoot block idx proof then
      return AuditResult.invalid s!"block {idx} boundary verification failed"

    -- Check state continuity between consecutively-indexed blocks
    if i + 1 < assignedBlocks.size then
      let nextIdx := blockIndices[i + 1]!
      if nextIdx == idx + 1 then
        let next := assignedBlocks[i + 1]!
        if !blocksContinuous block next then
          return AuditResult.invalid s!"discontinuity between blocks {idx} and {nextIdx}"

  AuditResult.valid

end Jar.Verifiable
