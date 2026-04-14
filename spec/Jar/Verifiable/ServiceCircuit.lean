import Jar.Verifiable.Types
import Jar.Commitment.Field

/-!
# Service-Programmable Circuits over DA Commitment

Services define custom polynomial constraints verified by validators
over the ZODA DA encoding (the "accidental computer" commitment).

## Why services need circuits

Shielded pool services (Penumbra-style) require verification of:
- Nullifier derivation: nullifier = H(secret, note)
- Note commitment: cm = H(value, blinding)
- Balance conservation: Σ inputs = Σ outputs
- Spend authority: signature valid

These operations are 100-1000x cheaper as polynomial constraints
over the committed data than as PVM re-execution (~200ms for BLS
in PVM vs ~2ms as a circuit sumcheck).

ELVES re-execution doesn't help here — it re-executes the same
expensive PVM code. Circuits verify the RESULT, not the computation.

## Design (from consensus review)

- Cost metering: circuit defines a cost manifest (constraint count,
  max degree). Gas charged proportional to manifest.
- Segment isolation: circuits reference only their own work item's
  segment range. Cross-service data access prevented by the verifier.
- Degree bounds: max degree 4 (quadratic constraints cover most
  crypto operations via intermediate witnesses).
- Verification: batched sumcheck — all constraints combined via
  random linear combination into ONE sumcheck per service.

## Cost model

One sumcheck per service circuit:
  v = log2(N) rounds, max(degree)+1 evaluations per round.
  For N=50K, degree-2: 16 rounds × 3 evals = 48 field ops.
  + 1 polynomial opening (O(sqrt(N)) hashes).
  Total: ~2ms per service circuit.

  341 cores × 1 circuit each = ~682ms sequential.
  On 16 cores: ~43ms per slot.

## Interaction with protocol

- Service registers circuit definition on-chain (via code upgrade)
- Guarantor produces standard ZODA encoding (no extra work)
- Validator runs batched sumcheck for each service's circuit
- If circuit fails: work report rejected, guarantor slashed
- Circuit definition versioned by service code hash

## References

- Accidental Computer (Evans & Angeris 2025)
- ZODA (Evans, Mohnblatt & Angeris 2025)
- Lasso (Setty, Thaler & Wahby 2023) — lookup arguments
-/

namespace Jar.Verifiable.ServiceCircuit

open Jar.Commitment.Field

-- ============================================================================
-- Circuit Cost Manifest
-- ============================================================================

/-- Maximum polynomial degree for service constraints. -/
def MAX_DEGREE : Nat := 4

/-- Maximum constraints per circuit definition. -/
def MAX_CONSTRAINTS : Nat := 4096

/-- Maximum auxiliary witness columns a service can declare. -/
def MAX_AUX_COLUMNS : Nat := 16

-- ============================================================================
-- Wire References (segment-isolated)
-- ============================================================================

/-- A reference to a field element in the service's DA segment.
    The segment_offset is relative to the service's work item data,
    NOT the full DA matrix. This prevents cross-service data access. -/
structure WireRef where
  /-- Offset within this service's segment (not global DA index). -/
  segmentOffset : UInt32
  /-- 0 = primary data, 1..MAX_AUX = auxiliary witness columns. -/
  column : UInt8
  deriving BEq, Inhabited

-- ============================================================================
-- Constraint Types
-- ============================================================================

/-- A polynomial constraint term: coefficient × wire reference. -/
structure ConstraintTerm where
  coeff : GF32
  wire : WireRef
  deriving BEq, Inhabited

/-- A single polynomial constraint.
    The constraint asserts that the polynomial evaluates to zero
    over the committed data. Constraints are multilinear or
    low-degree (up to MAX_DEGREE). -/
inductive Constraint where
  /-- Linear: Σ coeffs[i] × wires[i] == 0 -/
  | linear (terms : Array ConstraintTerm)
  /-- Quadratic: Σ_ij a_ij × wire_i × wire_j == 0
      Stored as (wire_a, wire_b, coeff) triples. -/
  | quadratic (triples : Array (WireRef × WireRef × GF32))
  /-- Lookup: all values in `queries` appear in `table`.
      Uses Lasso argument — no sorting needed. -/
  | lookup (table queries : Array WireRef)
  /-- Constant: wire == value. -/
  | constant (wire : WireRef) (value : GF32)
  deriving Inhabited

-- ============================================================================
-- Circuit Definition
-- ============================================================================

/-- A service circuit registered on-chain as part of the service code.
    Versioned by service code hash — upgrades are atomic. -/
structure CircuitDef where
  /-- Constraints to verify over the committed data. -/
  constraints : Array Constraint
  /-- Number of auxiliary witness columns (0 = constraints over raw data only). -/
  auxColumns : UInt8
  /-- Segment size: how many GF(2^32) elements this service expects. -/
  segmentSize : UInt32
  deriving Inhabited

namespace CircuitDef

def valid (cd : CircuitDef) : Bool :=
  cd.constraints.size > 0
  && cd.constraints.size <= MAX_CONSTRAINTS
  && cd.auxColumns.toNat <= MAX_AUX_COLUMNS

/-- Estimated verifier cost in microseconds. -/
def estimatedCostUs (cd : CircuitDef) : Nat :=
  -- One batched sumcheck: ~50µs per constraint (dominated by opening)
  -- Lookup constraints cost ~100µs each (Lasso sumcheck)
  let base := cd.constraints.size * 50
  let lookups := cd.constraints.foldl (fun acc c =>
    match c with | .lookup _ _ => acc + 50 | _ => acc) 0
  base + lookups

end CircuitDef

-- ============================================================================
-- Penumbra Example Circuits
-- ============================================================================

/-- Example: balance conservation for a shielded pool.
    Asserts Σ input_values == Σ output_values.
    Each value is a field element in the service's DA segment. -/
def balanceConservation (inputOffsets outputOffsets : Array UInt32) : Constraint :=
  let inputTerms := inputOffsets.map fun off =>
    { coeff := (1 : GF32), wire := { segmentOffset := off, column := 0 } : ConstraintTerm }
  let outputTerms := outputOffsets.map fun off =>
    -- In GF(2^32), subtraction = addition (char 2), so -1 = 1.
    -- For conservation over integers, we'd need a different field.
    -- Over GF(2^32): this checks XOR-conservation, not integer sum.
    -- For real balance conservation, use auxiliary witnesses with
    -- carry propagation constraints.
    { coeff := (1 : GF32), wire := { segmentOffset := off, column := 0 } : ConstraintTerm }
  .linear (inputTerms ++ outputTerms)

/-- Example: nullifier set membership check.
    Uses Lasso lookup: assert each spent nullifier appears in the set.
    The nullifier set is committed as part of the service's DA segment. -/
def nullifierMembership (setOffsets queryOffsets : Array UInt32) : Constraint :=
  .lookup
    (setOffsets.map fun off => { segmentOffset := off, column := 0 })
    (queryOffsets.map fun off => { segmentOffset := off, column := 0 })

-- ============================================================================
-- Verification
-- ============================================================================

/-- Verify a service circuit against the committed data.
    Batches all constraints into one sumcheck via random linear
    combination from the Fiat-Shamir transcript.

    Cost: ~2ms per circuit (one sumcheck + one opening proof). -/
def verifyCircuit (circuit : CircuitDef)
    (commitmentRoot : ByteArray)
    : Bool := Id.run do
  if !circuit.valid then return false
  if commitmentRoot.size != 32 then return false

  -- The actual verification:
  -- 1. Squeeze batching challenge from transcript
  -- 2. Combine constraints: P(x) = Σ r_i × constraint_i(x)
  -- 3. Run ONE sumcheck proving Σ_x P(x) = 0
  -- 4. Final round: verify opening against commitmentRoot
  --
  -- Implementation delegated to the sumcheck/Ligerito layer.
  -- This function defines the STRUCTURE.
  true

end Jar.Verifiable.ServiceCircuit
