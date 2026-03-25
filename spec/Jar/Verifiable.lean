import Jar.Verifiable.Types
import Jar.Verifiable.Verify
import Jar.Verifiable.Audit

/-!
# Verifiable Execution on JAM

Trace commitment + grand product memory proof + ELVES spot-checking.

## Architecture

The guarantor produces two artifacts per work report:
1. **Trace commitment**: Merkle root over basic block boundary states
2. **Memory proof**: Ligerito grand product proving memory consistency

The ELVES committee (~35 auditors) spot-checks ALU correctness by
re-executing assigned blocks. BLS finality follows ELVES approval.

## Modules

- `Types`: PvmSnapshot, BlockBoundary, MemoryAccess, TraceCommitment,
  MemoryProof, VerifiableFields, ELVESAssignment
- `Verify`: verifyMemoryProof, verifyBlockBoundary, verifyWorkReport,
  ProofContext (Fiat-Shamir domain separation)
- `Audit`: validatorAudit, elvesAudit, ELVESParams, FinalityTimeline

## Security

Memory consistency: unconditional (Ligerito grand product).
ALU correctness: ELVES rational-adversary (eprint 2024/961).
Finality: BLS aggregation after ELVES approval (6-12s at 2s slots).

See DESIGN.md (repo root) for full rationale.
-/
