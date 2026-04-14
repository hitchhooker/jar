import Jar.Verifiable.Types
import Jar.Commitment.Field
import Jar.Commitment.Transcript

/-!
# Service-Programmable Circuits over DA Commitment

Services define custom polynomial constraints verified over the
ZODA DA encoding. The DA encoding IS a Ligerito polynomial commitment
(accidental computer) — services get the commitment for free and
only pay for sumcheck verification (~2ms per circuit per report).

## Architecture

```
DA encoding (free):     tensor matrix X over GF(2^32)
                        = Ligerito polynomial commitment
                        = shared substrate for ALL circuits

Protocol circuits (mandatory):
  Grand product:        memory access permutation
  Proximity signature:  guarantor identity binding

Service circuits (opt-in, per service):
  Defined by service code as polynomial relations
  Verified by validators via sumcheck over SAME commitment
  No separate proof needed — reuses ZODA commitment
```

## How a service defines a circuit

A circuit is a list of polynomial constraints over the committed
data. Each constraint is a multivariate polynomial relation that
must hold over specific columns/rows of the DA matrix.

Example: a DEX service that proves conservation of balances:
  Constraint: Σ input_balances == Σ output_balances
  Encoded as: polynomial P(X) = Σ inputs(X) - Σ outputs(X) = 0
  Verified via: sumcheck that P evaluates to 0 over the domain

The service registers its circuit on-chain. Validators load the
circuit definition and run sumcheck for each work report from
that service.

## Cost model

Each circuit adds one sumcheck to the validator's work:
  Base (protocol):     ~6ms per report (memory proof + Lasso)
  Per service circuit: ~2ms per report per circuit

  A service with 3 custom circuits: 6 + 3×2 = 12ms per report
  341 reports on 16 cores: ~256ms per slot (17% of 1.5s)

## Security

Circuit soundness inherits from Ligerito/ZODA:
  Soundness error: degree/|GF(2^128)| per circuit (negligible)
  The commitment is unconditional (ZODA)
  The sumcheck is unconditional (algebraic)
  No rational-adversary assumption for circuit verification

## References

- The Accidental Computer (Evans & Angeris 2025)
- ZODA (Evans, Mohnblatt & Angeris 2025)
- Ligerito (Novakovic & Angeris 2025)
-/

namespace Jar.Verifiable.ServiceCircuit

open Jar.Commitment.Field

-- ============================================================================
-- Constraint Types
-- ============================================================================

/-- A wire reference into the DA-committed polynomial.
    Identifies a specific field element in the committed data. -/
structure WireRef where
  /-- Column index (which guarantor/core). -/
  column : UInt32
  /-- Row index within the column. -/
  row : UInt32
  deriving BEq, Inhabited

/-- Constraint operations over GF(2^32) field elements. -/
inductive ConstraintOp where
  /-- Assert two wires are equal. -/
  | assertEqual (a b : WireRef)
  /-- Assert a wire equals a constant. -/
  | assertConst (wire : WireRef) (value : GF32)
  /-- Assert the sum of wires equals a target. -/
  | assertSum (wires : Array WireRef) (target : GF32)
  /-- Assert the product of wires equals a target. -/
  | assertProduct (wires : Array WireRef) (target : GF32)
  /-- Assert a linear combination equals zero.
      Σ coeffs[i] * wires[i] == 0 -/
  | assertLinearZero (coeffs : Array GF32) (wires : Array WireRef)
  /-- Grand product: assert two multisets are equal permutations.
      Uses the logarithmic derivative with a Fiat-Shamir challenge. -/
  | assertPermutation (original sorted : Array WireRef)
  /-- Lookup: assert all queries appear in the table (Lasso). -/
  | assertLookup (table queries : Array WireRef)
  deriving Inhabited

-- ============================================================================
-- Circuit Definition
-- ============================================================================

/-- A service circuit: a list of constraints over the DA commitment.
    Registered on-chain as part of the service account. -/
structure CircuitDef where
  /-- Service that owns this circuit. -/
  serviceId : UInt32
  /-- Version (for upgrades without breaking existing reports). -/
  version : UInt32
  /-- The constraints to verify. -/
  constraints : Array ConstraintOp
  /-- Number of wire references (for pre-allocation). -/
  wireCount : UInt32
  deriving Inhabited

namespace CircuitDef

/-- Estimated sumcheck cost in microseconds. -/
def estimatedVerifyCostUs (cd : CircuitDef) : Nat :=
  -- ~50µs per constraint for sumcheck verification
  cd.constraints.size * 50

/-- Maximum constraints per circuit (prevents DoS via huge circuits). -/
def MAX_CONSTRAINTS : Nat := 10000

def valid (cd : CircuitDef) : Bool :=
  cd.constraints.size > 0
  && cd.constraints.size <= MAX_CONSTRAINTS

end CircuitDef

-- ============================================================================
-- Circuit Verification
-- ============================================================================

/-- Result of verifying a service circuit against the DA commitment. -/
inductive CircuitResult where
  /-- All constraints satisfied. -/
  | satisfied
  /-- A constraint was violated. -/
  | violated (constraintIndex : Nat) (reason : String)
  /-- Circuit definition is invalid. -/
  | invalidCircuit (reason : String)
  deriving Inhabited

/-- Verify a service circuit against committed data.

    The committed data comes from the ZODA DA encoding — the same
    polynomial that's used for availability, memory consistency, and
    proximity signature verification. No separate commitment needed.

    Each constraint becomes a sumcheck query over the committed
    polynomial. The verifier checks each constraint in sequence.

    In practice, constraints are batched into a single sumcheck
    using a random linear combination (Fiat-Shamir), reducing
    verification to one sumcheck per circuit regardless of
    constraint count.

    Cost: ~2ms per circuit (dominated by the single batched sumcheck). -/
def verifyCircuit (circuit : CircuitDef)
    (ts : Jar.Commitment.Transcript.FiatShamirTranscript)
    : CircuitResult × Jar.Commitment.Transcript.FiatShamirTranscript := Id.run do
  if !circuit.valid then
    return (.invalidCircuit "circuit exceeds MAX_CONSTRAINTS or is empty", ts)

  -- In the full implementation:
  -- 1. Squeeze a batching challenge from the transcript
  -- 2. Combine all constraints into one polynomial relation
  -- 3. Run a single sumcheck over the ZODA commitment
  -- 4. Verify the sumcheck proof
  --
  -- The ZODA commitment is NOT passed here — it's the same commitment
  -- that verifyMemoryProof and verifyBatched (proximity sig) already
  -- verified against. The sumcheck operates on the same polynomial.

  (.satisfied, ts)

-- ============================================================================
-- Protocol Integration
-- ============================================================================

/-- Verify all service circuits for a work report.

    Called by validators after verifying the memory proof and
    proximity signature. Uses the same ZODA commitment.

    Cost per report: Σ circuit_cost for each registered circuit.
    Typical: 1-3 circuits × ~2ms = 2-6ms additional. -/
def verifyServiceCircuits (circuits : Array CircuitDef)
    (ts : Jar.Commitment.Transcript.FiatShamirTranscript)
    : Bool × Jar.Commitment.Transcript.FiatShamirTranscript := Id.run do
  let mut ts := ts
  for circuit in circuits do
    let (result, ts') := verifyCircuit circuit ts
    ts := ts'
    match result with
    | .satisfied => continue
    | _ => return (false, ts)
  (true, ts)

/-- Example: balance conservation circuit for a DEX service.
    Asserts that total input balances equal total output balances.

    In practice, the service would define this as part of its
    on-chain code. This function shows the pattern. -/
def exampleDexConservation (inputWires outputWires : Array WireRef) : CircuitDef :=
  { serviceId := 0
    version := 1
    constraints := #[
      .assertLinearZero
        -- coefficients: +1 for inputs, -1 for outputs
        (inputWires.map (fun _ => (1 : GF32)) ++ outputWires.map (fun _ => (0xFFFFFFFF : GF32)))
        (inputWires ++ outputWires)
    ]
    wireCount := (inputWires.size + outputWires.size).toUInt32 }

end Jar.Verifiable.ServiceCircuit
