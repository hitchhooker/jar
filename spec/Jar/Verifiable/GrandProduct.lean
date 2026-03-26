import Jar.Verifiable.Types
import Jar.Commitment.Field
import Jar.Commitment.Transcript

/-!
# Grand Product Permutation Argument

Proves that two memory access logs (original execution order and
sorted by address+seq) are permutations of each other.

Uses the **logarithmic derivative** approach (HyperPlonk/Lasso):
  Σ_i 1/(α - encode(original_i)) = Σ_i 1/(α - encode(sorted_i))

This is equivalent to the multiplicative grand product but composes
naturally with sumcheck (already used by Ligerito).

## Encoding

Each MemoryAccess has 6 GF(2^32) elements (via to_field_elements).
These are compressed into a single GF(2^128) element using a random
challenge β:
  encode(t_0, ..., t_5) = Σ_j embed(t_j) · β^j

β is squeezed from the Fiat-Shamir transcript AFTER committing to
the witness polynomial, ensuring the prover cannot choose β.

## Soundness

Over GF(2^128), the Schwartz-Zippel bound gives error probability
N/2^128 for N accesses — negligible for any practical N.

## seq constraint

The polynomial additionally constrains seq_i == i for each entry
in the original (execution-order) log. This prevents entry
duplication, which the permutation check alone cannot detect
(it proves multiset equality, not set equality).
-/

namespace Jar.Verifiable.GrandProduct

open Jar.Commitment.Field
open Jar.Commitment.Transcript

-- ============================================================================
-- Tuple compression: 6 × GF(2^32) → GF(2^128)
-- ============================================================================

/-- Compress a 6-element GF(2^32) tuple into GF(2^128) using challenge β.
    encode(t) = Σ_j embed(t_j) · β^j -/
def encodeTuple (beta : GF128) (elements : Array GF32) : GF128 := Id.run do
  let mut result : GF128 := GF128.zero
  let mut beta_power : GF128 := GF128.one
  for e in elements do
    result := GF128.add result (GF128.mul (embedGF32 e) beta_power)
    beta_power := GF128.mul beta_power beta
  result

-- ============================================================================
-- Logarithmic derivative permutation check
-- ============================================================================

/-- Compute the logarithmic derivative sum:
    Σ_i 1/(α - encode(tuple_i))
    Returns None if any denominator is zero (α collides with an encoding). -/
def logDerivativeSum (alpha beta : GF128) (tuples : Array (Array GF32))
    : Option GF128 := Id.run do
  let mut sum : GF128 := GF128.zero
  for t in tuples do
    let encoded := encodeTuple beta t
    let denom := GF128.add alpha encoded  -- α - encoded = α + encoded (char 2)
    if denom == GF128.zero then return none
    sum := GF128.add sum (GF128.inv denom)
  some sum

/-- Verify the permutation: original and sorted logs have equal
    logarithmic derivative sums. -/
def verifyPermutation (alpha beta : GF128)
    (original sorted : Array (Array GF32)) : Bool := Id.run do
  match logDerivativeSum alpha beta original, logDerivativeSum alpha beta sorted with
  | some s1, some s2 => s1 == s2
  | _, _ => false

-- ============================================================================
-- seq_i == i constraint
-- ============================================================================

/-- Verify that seq fields in the original log are consecutive: seq_i == i.
    This prevents entry duplication (grand product is multiset equality). -/
def verifySeqConstraint (original : Array (Array GF32)) : Bool := Id.run do
  for i in [:original.size] do
    let tuple := original[i]!
    -- seq is at position 3 in the 6-element tuple
    if tuple.size < 4 then return false
    if tuple[3]! != i.toUInt32 then return false
  true

-- ============================================================================
-- Full verification (called by the prover/verifier integration)
-- ============================================================================

/-- Squeeze the tuple compression challenge β from the transcript. -/
def squeezeBeta (ts : FiatShamirTranscript) : (GF128 × FiatShamirTranscript) :=
  challengeGF128 ts

/-- Squeeze the permutation challenge α from the transcript. -/
def squeezeAlpha (ts : FiatShamirTranscript) : (GF128 × FiatShamirTranscript) :=
  challengeGF128 ts

/-- Convert a MemoryAccess to its 6-element GF(2^32) tuple.
    Matches the Rust `to_field_elements()` encoding exactly. -/
def accessToTuple (a : MemoryAccess) : Array GF32 :=
  let value_lo : GF32 := (a.value &&& 0xFFFFFFFF).toUInt32
  let value_hi : GF32 := (a.value >>> 32).toUInt32
  let width_val : GF32 := match a.width with
    | .byte1 => 1 | .byte2 => 2 | .byte4 => 4 | .byte8 => 8
  let flags : GF32 := if a.isWrite then 1 else 0
  #[a.address, value_lo, value_hi, a.seq, width_val, flags]

/-- Full grand product verification for a memory access trace.
    1. Squeeze β (tuple compression challenge)
    2. Squeeze α (permutation challenge)
    3. Verify seq_i == i in original log
    4. Compute logarithmic derivative sums
    5. Check equality -/
def verifyGrandProduct (ts : FiatShamirTranscript)
    (originalAccesses sortedAccesses : Array MemoryAccess)
    : Bool × FiatShamirTranscript := Id.run do
  -- Squeeze challenges from transcript
  let (beta, ts) := squeezeBeta ts
  let (alpha, ts) := squeezeAlpha ts

  -- Convert to field element tuples
  let original := originalAccesses.map accessToTuple
  let sorted := sortedAccesses.map accessToTuple

  -- Check seq constraint on original log
  if !verifySeqConstraint original then
    return (false, ts)

  -- Check permutation via logarithmic derivative
  let ok := verifyPermutation alpha beta original sorted
  (ok, ts)

end Jar.Verifiable.GrandProduct
