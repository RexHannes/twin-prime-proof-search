import Mathlib
import RequestProject.IteratedCarrierPeel

/-!
# Peel Semantics Alignment: Raw vs Canonical

## Motivation

Session 13 defined `peelOnce` as a "raw" peel:
1. Find the minimal v_p layer among all weights.
2. Merge layer terms into a signed sum S.
3. Divide S by p^m to get the merged residual.
4. Keep non-layer terms **unchanged**.

The Kaggle canonical normalized peel does:
1. Find the minimal v_p layer.
2. Merge layer terms into signed sum S.
3. Divide **all** terms (layer merged AND non-layer) by p^m.
4. Then divide the entire equation by gcd of all resulting terms.
5. Canonicalize sign/order.

These produce different residual equations. The Kaggle CSV scans use the
canonical version, so empirical data (CC distributions, support thresholds)
must be interpreted under canonical semantics.

This file:
- Defines `peelOnceRaw` (= Session 13's `peelOnce`).
- Defines `peelOnceCanonical` (divide all by p^m, then by gcd).
- Proves the relationship: canonical = gcd-normalize ∘ raw-full-divide.
- Reworks the 32+3+1=27+9 example under both semantics.
- Records the support-6 two-step Kaggle diagnostic data.

## Key insight

For the raw peel to produce a valid equation, it must divide ALL terms by p^m
(since every term is divisible by p^m by definition of m being the minimum
v_p valuation). The Session 13 `peelOnce` only divides the merged layer term,
which is correct for a "merge-and-replace" view but does NOT match the Kaggle
semantics and fails to produce valid residuals on the second peel.

The canonical peel additionally divides by the gcd of all residual terms,
which ensures the equation is primitive (no common factor).
-/

open Finset BigOperators

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

/-! ## Section 1: peelOnceRaw — The Session 13 Definition (Renamed)

This is exactly the `peelOnce` from `IteratedCarrierPeel.lean`, renamed
for clarity. It merges the minimal v_p layer into one term divided by p^m,
and keeps non-layer terms unchanged.

NOTE: This definition has a semantic issue — the non-layer terms are all
divisible by p^m (since m is the minimum), but they are NOT divided by p^m.
This means the resulting equation is NOT the standard p-adic peel; it is
the original equation with the layer terms replaced by their merge.
-/

section RawPeel

/-- `peelOnceRaw` is the Session 13 `peelOnce`: merge the minimal v_p layer,
    divide the merge by p^m, leave non-layer terms unchanged. -/
def peelOnceRaw (s : PeelState) (pp : PeelPrime) : PeelState :=
  peelOnce s pp  -- exactly the existing definition

end RawPeel

/-! ## Section 2: Full-Divide Peel — Divide ALL terms by p^m

This is the mathematically correct p-adic peel: divide every term by p^m
(where m is the minimum v_p valuation), then merge the layer.

Equivalently: divide all weights by p^m, then the layer terms all have
v_p = 0 while non-layer terms have v_p > 0. The equation remains balanced
because both sides were divided by the same p^m.
-/

section FullDividePeel

/-- Divide a natural number by p^m, returning the quotient.
    Assumes p^m divides n. -/
def divPowNat (n p m : ℕ) : ℕ := n / (p ^ m)

/-- `peelOnceFullDiv` divides ALL terms by p^m (where m = min v_p), then
    merges the (now v_p = 0) layer into one signed term.

    Step-by-step:
    1. Compute m = min v_p over all weights.
    2. Divide ALL weights by p^m.
    3. The layer consists of divided weights with v_p = 0.
    4. Merge layer into signed sum.
    5. Non-layer terms are the divided weights with v_p > 0.
    6. The new equation has: non-layer divided terms + merged layer term. -/
def peelOnceFullDiv (s : PeelState) (pp : PeelPrime) : PeelState :=
  let p := pp.val
  let m := minVpList p s.weights
  let pm := p ^ m
  -- Divide all weights by p^m
  let dividedPairs := (s.weights.zip s.signs).map fun ⟨w, sgn⟩ => (w / pm, sgn)
  -- Partition divided pairs into layer (v_p of original = m, i.e. v_p of divided = 0) and non-layer
  let layer := dividedPairs.filter (fun ⟨w, _⟩ => vpVal p w = 0)
  let nonlayer := dividedPairs.filter (fun ⟨w, _⟩ => vpVal p w ≠ 0)
  -- Merge layer into signed sum
  let layerSum : ℤ := layer.foldl (fun acc ⟨w, sgn⟩ =>
    acc + if sgn then (w : ℤ) else -(w : ℤ)) 0
  let mergedAbs : ℕ := layerSum.natAbs
  let mergedSign : Bool := 0 ≤ layerSum
  -- Build new state
  let newWeights := nonlayer.map Prod.fst ++ [mergedAbs]
  let newSigns := nonlayer.map Prod.snd ++ [mergedSign]
  { label := s.label ++ " → fullDiv(" ++ pp.toString ++ ")"
    weights := newWeights
    signs := newSigns
    lengths_match := by simp [newWeights, newSigns, List.length_append, List.length_map]
    peelHistory := s.peelHistory ++ [pp]
    step := s.step + 1 }

end FullDividePeel

/-! ## Section 3: GCD Normalization -/

section GCDNorm

/-- The gcd of a list of natural numbers. -/
def listGcd : List ℕ → ℕ
  | []      => 0
  | [n]     => n
  | n :: ns => Nat.gcd n (listGcd ns)

/-- Divide all weights in a PeelState by their gcd, producing the canonical
    (primitive) form of the equation. -/
def gcdNormalize (s : PeelState) : PeelState :=
  let g := listGcd s.weights
  if g ≤ 1 then s
  else
    { label := s.label ++ " [gcd-norm]"
      weights := s.weights.map (· / g)
      signs := s.signs
      lengths_match := by simp [List.length_map, s.lengths_match]
      peelHistory := s.peelHistory
      step := s.step }

/-- `peelOnceCanonical` = full-divide peel followed by gcd normalization.
    This matches the Kaggle scan semantics:
    1. Divide all terms by p^m.
    2. Merge the v_p = 0 layer.
    3. Divide all resulting terms by their gcd.
    4. (Sign/order canonicalization is omitted as it doesn't affect CC.) -/
def peelOnceCanonical (s : PeelState) (pp : PeelPrime) : PeelState :=
  gcdNormalize (peelOnceFullDiv s pp)

end GCDNorm

/-! ## Section 4: Relationship Between Semantics

**Theorem (informal):**
`peelOnceCanonical s p = gcdNormalize (peelOnceFullDiv s p)`

This is true by definition. The deeper relationship is:

1. `peelOnceRaw` does NOT divide non-layer terms by p^m. This means the
   raw peel output has a "scale mismatch": layer-merged term is at scale 1,
   while non-layer terms are at scale p^m. The equation is still valid
   because the merge computes the correct signed sum. But the second peel
   on a raw-peeled state produces invalid results because the terms have
   incompatible scales.

2. `peelOnceFullDiv` divides all terms by p^m, so the equation is
   homogeneously rescaled. The second peel works correctly.

3. `peelOnceCanonical` additionally removes common factors, matching
   the Kaggle semantics exactly.

**For empirical comparison with Kaggle CSV data, always use `peelOnceCanonical`.**
-/

/-! ## Section 5: Worked Example — 32+3+1=27+9 Under Both Semantics -/

section WorkedExampleBoth

/-- The identity 32 + 3 + 1 = 27 + 9, equivalently 32 + 3 + 1 - 27 - 9 = 0. -/
def ex_32_3_1_27_9 : PeelState :=
  mkInitialState "32+3+1=27+9" [32, 3, 1] [27, 9]

theorem ex_initial_valid : ex_32_3_1_27_9.isValid := by native_decide
theorem ex_initial_support : ex_32_3_1_27_9.support = 5 := by native_decide
theorem ex_initial_cc : ex_32_3_1_27_9.carrierComplexity = 0 := by native_decide

/-! ### 5.1: Raw first v₃-peel

v₃ valuations: v₃(32)=0, v₃(3)=1, v₃(1)=0, v₃(27)=3, v₃(9)=2.
Min v₃ = 0, layer = {32(+), 1(+)}, sum = 33.
Non-layer = {3(+), 27(−), 9(−)} **unchanged**.
Merged = 33 / 3⁰ = 33.
Raw result: [3, 27, 9, 33] with signs [+, −, −, +].
Equation: 3 − 27 − 9 + 33 = 0. ✓ (valid)
CC = 1 (carrier: 33 = 3·11). -/

def ex_raw_v3 : PeelState := peelOnceRaw ex_32_3_1_27_9 .three

theorem ex_raw_v3_valid : ex_raw_v3.isValid := by native_decide
theorem ex_raw_v3_weights : ex_raw_v3.weights = [3, 27, 9, 33] := by native_decide
theorem ex_raw_v3_signs : ex_raw_v3.signs = [true, false, false, true] := by native_decide
theorem ex_raw_v3_cc : ex_raw_v3.carrierComplexity = 1 := by native_decide
theorem ex_raw_v3_carrier : ex_raw_v3.carrierWeights = [33] := by native_decide

/-! ### 5.2: Full-divide first v₃-peel

Same layer identification. But now ALL terms divided by 3⁰ = 1.
Result is identical to raw in this case (since m = 0, p^m = 1).
Full-div result: [3, 27, 9, 33] with signs [+, −, −, +].
-/

def ex_fulldiv_v3 : PeelState := peelOnceFullDiv ex_32_3_1_27_9 .three

theorem ex_fulldiv_v3_valid : ex_fulldiv_v3.isValid := by native_decide
theorem ex_fulldiv_v3_weights : ex_fulldiv_v3.weights = [3, 27, 9, 33] := by native_decide
theorem ex_fulldiv_v3_cc : ex_fulldiv_v3.carrierComplexity = 1 := by native_decide

/-! ### 5.3: Canonical first v₃-peel

Full-div gives [3, 27, 9, 33]. gcd(3,27,9,33) = 3.
Canonical: divide by 3 → [1, 9, 3, 11].
Equation: 1 − 9 − 3 + 11 = 0. ✓
CC = 1 (carrier: 11 ∉ ALLOWED). -/

def ex_canonical_v3 : PeelState := peelOnceCanonical ex_32_3_1_27_9 .three

theorem ex_canonical_v3_valid : ex_canonical_v3.isValid := by native_decide
theorem ex_canonical_v3_weights : ex_canonical_v3.weights = [1, 9, 3, 11] := by native_decide
theorem ex_canonical_v3_cc : ex_canonical_v3.carrierComplexity = 1 := by native_decide
theorem ex_canonical_v3_carrier : ex_canonical_v3.carrierWeights = [11] := by native_decide

/-! ### 5.4: Semantics mismatch explained

After the first v₃-peel:
- **Raw**:       [3, 27, 9, 33], carrier = [33]
- **Canonical**: [1, 9, 3, 11],  carrier = [11]

Session 13 summary said "first v₃-peel has carrier [33]" — this was the RAW peel.
The Kaggle scans use canonical, which gives carrier [11] directly.

This explains the reported mismatch: the Session 13 code used raw peel semantics,
while Kaggle used canonical. The carrier [33] was an artifact of not normalizing.
-/

/-! ### 5.5: Raw second v₃-peel (FAILS to produce valid equation)

Starting from raw result [3, 27, 9, 33]:
v₃: v₃(3)=1, v₃(27)=3, v₃(9)=2, v₃(33)=1.
Min v₃ = 1, layer = {3(+), 33(+)}, sum = 36.
Non-layer = {27(−), 9(−)} **unchanged**.
Merged = 36 / 3¹ = 12. Sign = +.
Raw result: [27, 9, 12] with signs [−, −, +].
Equation: −27 − 9 + 12 = −24 ≠ 0. ❌ INVALID.

The raw peel produces an invalid equation on the second step because
non-layer terms were not divided by p^m at the first step.
-/

def ex_raw_v3_v3 : PeelState := peelOnceRaw ex_raw_v3 .three

-- This demonstrates the invalidity of raw second peel:
theorem ex_raw_v3_v3_invalid : ¬ ex_raw_v3_v3.isValid := by native_decide

/-! ### 5.6: Full-divide second v₃-peel (from full-div first result)

Starting from full-div result [3, 27, 9, 33] (same as raw when m=0):
v₃: v₃(3)=1, v₃(27)=3, v₃(9)=2, v₃(33)=1.
Min v₃ = 1, layer = {3(+), 33(+)}.
Divide all by 3¹: [1, 9, 3, 11].
Layer (v₃ of original = 1, v₃ of divided = 0): {1(+), 11(+)}, sum = 12.
Non-layer (v₃ of divided > 0): {9(−), 3(−)}.
Merged = 12. Sign = +.
Full-div result: [9, 3, 12] with signs [−, −, +].
Equation: −9 − 3 + 12 = 0. ✓
CC = 0 (all ALLOWED-smooth). -/

def ex_fulldiv_v3_v3 : PeelState := peelOnceFullDiv ex_fulldiv_v3 .three

theorem ex_fulldiv_v3_v3_valid : ex_fulldiv_v3_v3.isValid := by native_decide
theorem ex_fulldiv_v3_v3_weights : ex_fulldiv_v3_v3.weights = [9, 3, 12] := by native_decide
theorem ex_fulldiv_v3_v3_cc : ex_fulldiv_v3_v3.carrierComplexity = 0 := by native_decide

/-! ### 5.7: Canonical second v₃-peel (from canonical first result)

Starting from canonical [1, 9, 3, 11]:
v₃: v₃(1)=0, v₃(9)=2, v₃(3)=1, v₃(11)=0.
Min v₃ = 0, layer = {1(+), 11(+)}.
Divide all by 3⁰ = 1 (no change).
Layer (v₃ = 0): {1(+), 11(+)}, sum = 12.
Non-layer: {9(−), 3(−)}.
Full-div result: [9, 3, 12] with signs [−, −, +].
gcd(9, 3, 12) = 3. Canonical: [3, 1, 4].
Equation: −3 − 1 + 4 = 0. ✓
CC = 0. -/

def ex_canonical_v3_v3 : PeelState := peelOnceCanonical ex_canonical_v3 .three

theorem ex_canonical_v3_v3_valid : ex_canonical_v3_v3.isValid := by native_decide
theorem ex_canonical_v3_v3_weights : ex_canonical_v3_v3.weights = [3, 1, 4] := by native_decide
theorem ex_canonical_v3_v3_cc : ex_canonical_v3_v3.carrierComplexity = 0 := by native_decide

/-! ### 5.8: Summary comparison table

| Step | Raw weights | Raw CC | Raw carrier | FullDiv weights | FullDiv CC | Canonical weights | Canonical CC | Canonical carrier |
|------|-------------|--------|-------------|-----------------|------------|-------------------|--------------|-------------------|
| 0    | [32,3,1,27,9] | 0 | — | [32,3,1,27,9] | 0 | [32,3,1,27,9] | 0 | — |
| v₃   | [3,27,9,33] | 1 | [33] | [3,27,9,33] | 1 | [1,9,3,11] | 1 | [11] |
| v₃v₃ | [27,9,12] ❌ | — | — | [9,3,12] | 0 | [3,1,4] | 0 | — |

Key observations:
1. Raw peel FAILS on second step (produces invalid equation).
2. Full-divide and canonical agree on validity and CC classification.
3. Canonical additionally normalizes by gcd, producing smaller numbers.
4. The Session 13 claim "carrier [33] after first v₃-peel" was raw semantics.
5. The Kaggle-matching result is "carrier [11] after first v₃-peel" (canonical).
-/

end WorkedExampleBoth

/-! ## Section 6: Iterated Canonical Peeling -/

section IteratedCanonical

/-- Apply a sequence of canonical peels. -/
def peelSequenceCanonical (s : PeelState) : List PeelPrime → PeelState
  | []      => s
  | p :: ps => peelSequenceCanonical (peelOnceCanonical s p) ps

/-- Apply a sequence of full-div peels (without gcd normalization). -/
def peelSequenceFullDiv (s : PeelState) : List PeelPrime → PeelState
  | []      => s
  | p :: ps => peelSequenceFullDiv (peelOnceFullDiv s p) ps

end IteratedCanonical

/-! ## Section 7: Support-6 Two-Step Kaggle Diagnostic Data

The following records the empirical results from the Kaggle support-6
two-step canonical peel diagnostic scan.

**Source**: Kaggle exact scan of all 35,994 primitive support-6 {2,3}-smooth cores.
**Peel sequences tested**: (2,2), (2,3), (3,2), (3,3).
**Total two-step states**: 35,994 × 4 = 143,976 (each core × each 2-step sequence).

Note: The user reports 143,688 two-step states, slightly less than 143,976,
likely due to some cores degenerating (reaching support ≤ 2 after the first peel,
making the second peel trivial or undefined).

**CC distribution after two canonical peels:**
- CC = 0: 93,471
- CC = 1: 48,318
- CC = 2: 1,899
- CC > 2: 0 observed

**Key finding**: CC = 2 DOES occur after two canonical peels, in about 1.32%
of states. This REFUTES the conjecture "CC ≤ 1 forever."

The corrected empirical statement is:
- One-step canonical peeling: CC ≤ 1 always (likely near-tautological).
- Two-step canonical peeling: CC ≤ 2 always observed; CC = 2 is rare (~1.3%).
- No CC > 2 observed in the support-6 two-step scan.
-/

section Support6TwoStepData

/-- Record of the support-6 two-step canonical peel diagnostic. -/
structure TwoStepPeelDiagnostic where
  /-- Number of primitive cores scanned -/
  coresLoaded : ℕ
  /-- Peel sequences tested (encoded as pairs of PeelPrime) -/
  peelSequencesTested : List (PeelPrime × PeelPrime)
  /-- Total two-step states examined -/
  totalTwoStepStates : ℕ
  /-- Count of states with CC = 0 after two peels -/
  cc0Count : ℕ
  /-- Count of states with CC = 1 after two peels -/
  cc1Count : ℕ
  /-- Count of states with CC = 2 after two peels -/
  cc2Count : ℕ
  /-- Count of states with CC > 2 after two peels -/
  ccGt2Count : ℕ
  /-- Consistency: counts sum to total -/
  counts_sum : cc0Count + cc1Count + cc2Count + ccGt2Count = totalTwoStepStates

/-- The actual support-6 two-step diagnostic data from the Kaggle scan. -/
def support6TwoStepDiagnostic : TwoStepPeelDiagnostic :=
  { coresLoaded := 35994
    peelSequencesTested :=
      [ (.two, .two), (.two, .three), (.three, .two), (.three, .three) ]
    totalTwoStepStates := 143688
    cc0Count := 93471
    cc1Count := 48318
    cc2Count := 1899
    ccGt2Count := 0
    counts_sum := by native_decide }

/-- CC > 2 was never observed. -/
theorem support6_twoStep_no_cc_gt2 : support6TwoStepDiagnostic.ccGt2Count = 0 := rfl

/-- CC = 2 occurs in about 1.32% of two-step states. -/
theorem support6_twoStep_cc2_count : support6TwoStepDiagnostic.cc2Count = 1899 := rfl

/-- Total cores scanned. -/
theorem support6_twoStep_cores : support6TwoStepDiagnostic.coresLoaded = 35994 := rfl

/-- The CC ≤ 1 conjecture is FALSE for two-step canonical peeling. -/
theorem support6_twoStep_cc_leq1_false :
    support6TwoStepDiagnostic.cc2Count > 0 := by native_decide

/-- But CC ≤ 2 holds for all observed two-step states. -/
theorem support6_twoStep_cc_leq2 :
    support6TwoStepDiagnostic.ccGt2Count = 0 := rfl

/-!
### Interpretation

1. **"CC ≤ 1 forever" is REFUTED** by the two-step data: 1,899 states
   reach CC = 2 after two canonical peels.

2. The corrected empirical phenomenon is **sparse/structured CC growth**:
   - CC grows slowly (at most +1 per peel step, empirically).
   - CC = 2 is rare (~1.3% of two-step states).
   - No CC > 2 is observed.

3. The next conjecture should be **"subcritical carrier genealogy"**:
   carrier complexity grows sublinearly (logarithmically?) in the number
   of peel steps, not "single-carrier forever."

4. The real open question is whether CC remains bounded by some function
   of the number of peel steps (or even bounded absolutely) for primitive
   {2,3}-smooth identities under canonical peeling.
-/

end Support6TwoStepData

/-! ## Section 8: Which Semantics Matches Kaggle

**Statement**: The Kaggle CSV scans use **canonical normalized peel** semantics:

1. Find the minimal v_p layer.
2. Merge all terms in that layer into one signed term.
3. Divide **all** residual terms (not just the merged one) by p^m.
4. Divide the entire resulting equation by the gcd of all residual terms.
5. Canonicalize sign/order (positive terms first, sorted descending).

**Evidence**:
- The worked example 32+3+1=27+9 produces carrier [11] (not [33]) after
  the first v₃-peel in Kaggle, matching `peelOnceCanonical` output.
- The two-step data was generated using this canonical semantics.

**Consequence**:
- All CC distribution data in this project should be interpreted under
  canonical peel semantics.
- The `peelOnce` definition in `IteratedCarrierPeel.lean` (Session 13)
  corresponds to `peelOnceRaw`, which does NOT match Kaggle.
- For correct iterated peeling, use `peelOnceCanonical` or
  `peelOnceFullDiv` from this file.
-/

/-! ## Section 9: Properties of peelOnceCanonical -/

section CanonicalProperties

/-- Canonical peel preserves step increment. -/
theorem peelOnceCanonical_step (s : PeelState) (p : PeelPrime) :
    (peelOnceCanonical s p).step = s.step + 1 := by
  simp [peelOnceCanonical, gcdNormalize, peelOnceFullDiv]
  split <;> simp_all

/-- Canonical peel appends one prime to history. -/
theorem peelOnceCanonical_history (s : PeelState) (p : PeelPrime) :
    (peelOnceCanonical s p).peelHistory = s.peelHistory ++ [p] := by
  simp [peelOnceCanonical, gcdNormalize, peelOnceFullDiv]
  split <;> simp_all

/-- Full-div peel preserves step increment. -/
theorem peelOnceFullDiv_step (s : PeelState) (p : PeelPrime) :
    (peelOnceFullDiv s p).step = s.step + 1 := by
  simp [peelOnceFullDiv]

/-- Full-div peel appends one prime to history. -/
theorem peelOnceFullDiv_history (s : PeelState) (p : PeelPrime) :
    (peelOnceFullDiv s p).peelHistory = s.peelHistory ++ [p] := by
  simp [peelOnceFullDiv]

end CanonicalProperties
