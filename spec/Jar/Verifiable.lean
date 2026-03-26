import Jar.Verifiable.Types
import Jar.Verifiable.Verify
import Jar.Verifiable.Audit
import Jar.Verifiable.GrandProduct

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
- `Audit`: validateAuditInputs
- `GrandProduct`: logarithmic derivative permutation argument,
  tuple compression (β challenge), seq constraint, verifyGrandProduct

## Security

Memory permutation: unconditional (logarithmic derivative over GF(2^128)).
Sorting + read consistency: ELVES (rational adversary).
ALU correctness: ELVES rational-adversary (eprint 2024/961).
Finality: GRANDPA after ELVES approval (3-4.5s at 1.5s slots).

See DESIGN.md (repo root) for full rationale.
-/
