import Jar.Verifiable.Types
import Jar.Verifiable.Verify
import Jar.Verifiable.Audit
import Jar.Verifiable.GrandProduct
import Jar.Verifiable.ProximitySignature
import Jar.Verifiable.ServiceCircuit

/-!
# Verifiable Execution on JAM

Trace commitment + Lasso memory proof + proximity signatures + ELVES.

## Architecture

The guarantor produces per work report:
1. **Trace commitment**: Merkle root over block boundary states
2. **Proximity signature**: BLS signature covering the DA encoding
   (replaces proof_hash + commitment_root — binds guarantor identity
   to the encoded data, verified via ZODA reuse)
3. **Lasso memory proof**: lookup argument for memory consistency

## Modules

- `Types`: PvmSnapshot, BlockBoundary, MemoryAccess, TraceCommitment,
  MemoryProof, VerifiableFields, ELVESAssignment
- `Verify`: verifyMemoryProof, verifyBlockBoundary, verifyWorkReport,
  ProofContext (Fiat-Shamir domain separation)
- `Audit`: validateAuditInputs
- `GrandProduct`: logarithmic derivative permutation argument
- `ProximitySignature`: DA-bound signature verification (Angeris & Gurkan 2026)
- `ServiceCircuit`: programmable constraints over DA commitment

## Security

Memory permutation: unconditional (logarithmic derivative over GF(2^128)).
Sorting + read consistency: ELVES (rational adversary).
ALU correctness: ELVES rational-adversary (eprint 2024/961).
DA binding: proximity signature (many-slot unforgeability, AGM+ROM).
Finality: GRANDPA after ELVES approval (3-4.5s at 1.5s slots).

See DESIGN.md (repo root) for full rationale.
-/
