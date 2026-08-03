import Mathlib
import RequestProject.CarrierComplexity

/-!
# Generalized Carrier Complexity Framework for Support-6+

## Overview

Session 10 established that all 400 bad support-5 peels have carrier complexity 1
relative to ALLOWED = {2,3,5,7,13,19,41,43}. This file generalizes the framework
to handle residual equations of **any support size**, defines certificate structures
for carrier complexity 0, 1, and 2, and prepares the infrastructure for the next
decisive empirical test: **support-6 carrier complexity distribution**.

## Architecture

The key generalization is `ResidualEquation`, which replaces the support-5-specific
`Carrier1Certificate`. A `ResidualEquation` is a signed integer equation Σ sᵢ wᵢ = 0
where each weight wᵢ is classified as ALLOWED-smooth or outside-carrier. The
**carrier complexity** is simply the count of outside-carrier terms.

## Intended workflow for support-6

1. **Kaggle scan**: Enumerate primitive support-6 {2,3}-smooth identities up to
   some bound (e.g., MAX_VALUE = 10⁶). For each, perform all p-adic peels.
2. **CSV export**: For each bad peel (residual with outside-ALLOWED cofactors),
   export the residual equation as a CSV row:
   `support, carrier_complexity, weights, signs, outside_indices`.
3. **Lean certificate import**: Convert CSV rows to `ClassifiedResidual` instances.
4. **Lean verification**: Each certificate is verified by `native_decide` or `decide`
   to confirm the equation sums to zero, the outside terms are genuinely outside,
   and the smooth terms are genuinely ALLOWED-smooth.
5. **Distribution analysis**: Count the carrier complexity distribution. The key
   question is whether carrier complexity remains bounded (≤ 1? ≤ 2?) for support-6.

## Status

No support-6 empirical data has been imported yet. This file provides the
**definitions and infrastructure** only. The next session should run the Kaggle
scan and import the results.
-/

open Finset BigOperators

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

/-! ## Section 1: General Residual Equations -/

section ResidualEquations

/-- A **residual equation** is a signed integer equation arising from a p-adic peel
    of a primitive {2,3}-smooth kernel equation. It consists of:
    - A list of positive integer weights
    - A list of signs (true = +1, false = -1)
    - The equation asserts: Σᵢ sign(i) · weight(i) = 0

    This generalizes `Carrier1Certificate` to arbitrary support sizes and
    arbitrary carrier complexity. -/
structure ResidualEquation where
  /-- Human-readable label -/
  label : String
  /-- The positive integer weights in the residual equation -/
  weights : List ℕ
  /-- The signs: true = positive, false = negative -/
  signs : List Bool
  /-- Lengths must match -/
  lengths_match : weights.length = signs.length
  /-- At least one term -/
  nonempty : 0 < weights.length

/-- The support of a residual equation is the number of terms. -/
def ResidualEquation.support (eq : ResidualEquation) : ℕ := eq.weights.length

/-- The signed values of a residual equation. -/
def ResidualEquation.signedVals (eq : ResidualEquation) : List ℤ :=
  (eq.weights.zip eq.signs).map fun ⟨w, s⟩ =>
    if s then (w : ℤ) else -(w : ℤ)

/-- A residual equation is **valid** if its signed values sum to zero. -/
def ResidualEquation.IsBalanced (eq : ResidualEquation) : Prop :=
  eq.signedVals.sum = 0

end ResidualEquations

/-! ## Section 2: Certificate Structures by Carrier Complexity

We define specialized certificate structures for carrier complexity 0, 1, and 2.
These are "pre-verified" structures where the classification into smooth/carrier
terms is part of the data, making verification by `native_decide` efficient.

### Design principle

Each certificate carries:
1. The equation data (weights + signs)
2. An explicit partition of terms into smooth and carrier
3. The validity proof obligation: equation sums to zero, smooth terms are
   ALLOWED-smooth, carrier terms have outside factors

This lets Lean verify each certificate independently without re-computing
the factorization of every weight.
-/

section CertificateStructures

/-! ### Carrier Complexity 0 Certificates

A **CC0 certificate** asserts that a residual equation has carrier complexity 0:
all terms are ALLOWED-smooth. This means the peel stayed entirely within the
ALLOWED-smooth universe — a "good" peel. -/

/-- Certificate for a residual equation with carrier complexity 0:
    all terms are ALLOWED-smooth. -/
structure CC0Certificate where
  /-- Human-readable label -/
  label : String
  /-- All weights (all must be ALLOWED-smooth) -/
  weights : List ℕ
  /-- Signs -/
  signs : List Bool
  /-- Lengths match -/
  lengths_match : weights.length = signs.length
  /-- At least one term -/
  nonempty : 0 < weights.length

/-- Signed values of a CC0 certificate. -/
def CC0Certificate.signedVals (c : CC0Certificate) : List ℤ :=
  (c.weights.zip c.signs).map fun ⟨w, s⟩ =>
    if s then (w : ℤ) else -(w : ℤ)

/-- A CC0 certificate is valid if the equation balances and all weights are
    ALLOWED-smooth. -/
structure CC0Certificate.IsValid (c : CC0Certificate) : Prop where
  sum_zero : c.signedVals.sum = 0
  all_smooth : ∀ w ∈ c.weights, IsAllowedSmooth w

/-- A valid CC0 certificate witnesses carrier complexity 0. -/
theorem cc0_carrier_complexity_zero (c : CC0Certificate) (hv : c.IsValid) :
    ∀ w ∈ c.weights, IsAllowedSmooth w :=
  hv.all_smooth

/-! ### Carrier Complexity 1 Certificates

The existing `Carrier1Certificate` from `CarrierComplexity.lean` already handles
this case. We provide a bridge to the general framework. -/

/-- Convert a `Carrier1Certificate` to a `ResidualEquation`. -/
def Carrier1Certificate.toResidualEquation (c : Carrier1Certificate) : ResidualEquation where
  label := c.name
  weights := c.carrierWeight :: c.smoothWeights
  signs := c.carrierSign :: c.smoothSigns
  lengths_match := by simp [c.lengths_match]
  nonempty := by simp

/-! ### Carrier Complexity 2 Certificates

A **CC2 certificate** asserts that a residual equation has exactly two terms
with outside-ALLOWED prime factors, and all remaining terms are ALLOWED-smooth.
This is the next layer beyond what was observed for support-5. -/

/-- Certificate for a residual equation with carrier complexity 2:
    exactly two terms have outside-ALLOWED prime factors. -/
structure CC2Certificate where
  /-- Human-readable label -/
  label : String
  /-- First carrier term weight -/
  carrier1Weight : ℕ
  /-- First carrier term sign -/
  carrier1Sign : Bool
  /-- Second carrier term weight -/
  carrier2Weight : ℕ
  /-- Second carrier term sign -/
  carrier2Sign : Bool
  /-- ALLOWED-smooth term weights -/
  smoothWeights : List ℕ
  /-- ALLOWED-smooth term signs -/
  smoothSigns : List Bool
  /-- Lengths match for smooth part -/
  lengths_match : smoothWeights.length = smoothSigns.length

/-- Signed value of carrier term 1. -/
def CC2Certificate.carrier1Val (c : CC2Certificate) : ℤ :=
  if c.carrier1Sign then (c.carrier1Weight : ℤ) else -(c.carrier1Weight : ℤ)

/-- Signed value of carrier term 2. -/
def CC2Certificate.carrier2Val (c : CC2Certificate) : ℤ :=
  if c.carrier2Sign then (c.carrier2Weight : ℤ) else -(c.carrier2Weight : ℤ)

/-- Signed smooth values. -/
def CC2Certificate.smoothVals (c : CC2Certificate) : List ℤ :=
  (c.smoothWeights.zip c.smoothSigns).map fun ⟨w, s⟩ =>
    if s then (w : ℤ) else -(w : ℤ)

/-- The total support of a CC2 certificate. -/
def CC2Certificate.support (c : CC2Certificate) : ℕ :=
  2 + c.smoothWeights.length

/-- A CC2 certificate is **valid** if:
    1. The equation sums to zero
    2. Both carrier weights have outside-ALLOWED prime factors
    3. All smooth weights are ALLOWED-smooth -/
structure CC2Certificate.IsValid (c : CC2Certificate) : Prop where
  sum_zero : c.carrier1Val + c.carrier2Val + c.smoothVals.sum = 0
  carrier1_outside : HasOutsideCarrier c.carrier1Weight
  carrier2_outside : HasOutsideCarrier c.carrier2Weight
  all_smooth : ∀ w ∈ c.smoothWeights, IsAllowedSmooth w

/-- A valid CC2 certificate witnesses that the equation has at least 2
    outside-carrier terms and all remaining terms are ALLOWED-smooth. -/
theorem cc2_certificate_gives_complexity_two (c : CC2Certificate) (hv : c.IsValid) :
    HasOutsideCarrier c.carrier1Weight ∧
    HasOutsideCarrier c.carrier2Weight ∧
    ∀ w ∈ c.smoothWeights, IsAllowedSmooth w :=
  ⟨hv.carrier1_outside, hv.carrier2_outside, hv.all_smooth⟩

end CertificateStructures

/-! ## Section 3: Synthetic Examples of Carrier Complexity 2

These are **synthetic** examples constructed to test the CC2Certificate framework.
They are NOT derived from actual support-6 peel data (no such data has been
imported yet). They demonstrate that the framework can express and verify
carrier-complexity-2 equations.

### Example: 11 + 17 − 28 = 0
- 11 has outside carrier (prime 11 ∉ ALLOWED)
- 17 has outside carrier (prime 17 ∉ ALLOWED)
- 28 = 4 × 7 is ALLOWED-smooth (primes 2, 7 ∈ ALLOWED)

### Example: 11 + 23 − 2 − 32 = 0
- 11 has outside carrier (prime 11 ∉ ALLOWED)
- 23 has outside carrier (prime 23 ∉ ALLOWED)
- 2 is ALLOWED-smooth
- 32 = 2⁵ is ALLOWED-smooth
-/

section SyntheticCC2Examples

/-- Synthetic CC2 example: 11 + 17 − 28 = 0.
    This is a support-3 equation with carrier complexity 2 (synthetic, not from data). -/
def synth_cc2_ex1 : CC2Certificate where
  label := "synth_11_17_28"
  carrier1Weight := 11
  carrier1Sign := true
  carrier2Weight := 17
  carrier2Sign := true
  smoothWeights := [28]
  smoothSigns := [false]
  lengths_match := rfl

theorem isAllowedSmooth_28 : IsAllowedSmooth 28 :=
  isAllowedSmooth_mul (isAllowedSmooth_mul isAllowedSmooth_4 isAllowedSmooth_7) (by
    intro p hp hpd; have := Nat.le_of_dvd one_pos hpd
    exact absurd hp.one_lt (by omega))

theorem hasOutsideCarrier_23 : HasOutsideCarrier 23 := by
  intro h
  have := h 23 (by decide) (dvd_refl 23)
  simp [AllowedPrimes] at this

theorem synth_cc2_ex1_valid : synth_cc2_ex1.IsValid where
  sum_zero := by native_decide
  carrier1_outside := hasOutsideCarrier_11
  carrier2_outside := hasOutsideCarrier_17
  all_smooth := by
    intro w hw
    simp [synth_cc2_ex1] at hw
    exact hw ▸ isAllowedSmooth_28

/-- Synthetic CC2 example: 11 + 23 − 2 − 32 = 0.
    This is a support-4 equation with carrier complexity 2 (synthetic, not from data). -/
def synth_cc2_ex2 : CC2Certificate where
  label := "synth_11_23_2_32"
  carrier1Weight := 11
  carrier1Sign := true
  carrier2Weight := 23
  carrier2Sign := true
  smoothWeights := [2, 32]
  smoothSigns := [false, false]
  lengths_match := rfl

theorem isAllowedSmooth_32 : IsAllowedSmooth 32 := by
  intro p hp hpd
  have h32 : (32 : ℕ) = 2^5 := by norm_num
  rw [h32] at hpd
  have := hp.dvd_of_dvd_pow hpd
  have hle := Nat.le_of_dvd (by norm_num) this
  have := hp.two_le
  interval_cases p
  all_goals simp_all [AllowedPrimes]

theorem synth_cc2_ex2_valid : synth_cc2_ex2.IsValid where
  sum_zero := by native_decide
  carrier1_outside := hasOutsideCarrier_11
  carrier2_outside := hasOutsideCarrier_23
  all_smooth := by
    intro w hw
    simp [synth_cc2_ex2] at hw
    rcases hw with rfl | rfl
    · exact isAllowedSmooth_2
    · exact isAllowedSmooth_32

/-- Synthetic CC2 example: 11 + 61 − 72 = 0.
    - 11 and 61 are outside carriers
    - 72 = 2³ × 3² is {2,3}-smooth hence ALLOWED-smooth -/
def synth_cc2_ex3 : CC2Certificate where
  label := "synth_11_61_72"
  carrier1Weight := 11
  carrier1Sign := true
  carrier2Weight := 61
  carrier2Sign := true
  smoothWeights := [72]
  smoothSigns := [false]
  lengths_match := rfl

theorem isAllowedSmooth_72 : IsAllowedSmooth 72 := by
  intro p hp hpd
  have h72 : (72 : ℕ) = 2^3 * 3^2 := by norm_num
  rw [h72] at hpd
  rcases hp.dvd_mul.mp hpd with h | h
  · have := hp.dvd_of_dvd_pow h
    have hle := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    interval_cases p
    all_goals simp_all [AllowedPrimes]
  · have := hp.dvd_of_dvd_pow h
    have hle := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    interval_cases p
    all_goals simp_all [AllowedPrimes]

theorem synth_cc2_ex3_valid : synth_cc2_ex3.IsValid where
  sum_zero := by native_decide
  carrier1_outside := hasOutsideCarrier_11
  carrier2_outside := hasOutsideCarrier_61
  all_smooth := by
    intro w hw
    simp [synth_cc2_ex3] at hw
    exact hw ▸ isAllowedSmooth_72

end SyntheticCC2Examples

/-! ## Section 4: Uniform Classification Predicate

For batch verification of support-6 data, we define a uniform predicate that
classifies a residual equation by carrier complexity. This replaces the need
for separate certificate types when processing large CSV imports. -/

section UniformClassification

/-- Classification result for a single term in a residual equation. -/
inductive TermClass where
  | smooth    : TermClass  -- ALLOWED-smooth
  | carrier   : TermClass  -- has outside-ALLOWED prime factor
  deriving DecidableEq, Repr

/-- A **classified residual** is a residual equation where each term has been
    tagged as smooth or carrier. -/
structure ClassifiedResidual where
  /-- Human-readable label -/
  label : String
  /-- Weights -/
  weights : List ℕ
  /-- Signs -/
  signs : List Bool
  /-- Classification of each term -/
  classes : List TermClass
  /-- All lists have the same length -/
  len_weights_signs : weights.length = signs.length
  len_weights_classes : weights.length = classes.length
  /-- At least one term -/
  nonempty : 0 < weights.length

/-- The carrier complexity of a classified residual is the number of carrier-tagged terms. -/
def ClassifiedResidual.carrierComplexity (cr : ClassifiedResidual) : ℕ :=
  cr.classes.countP fun c => c == .carrier

/-- The smooth count of a classified residual. -/
def ClassifiedResidual.smoothCount (cr : ClassifiedResidual) : ℕ :=
  cr.classes.countP fun c => c == .smooth

/-- The support of a classified residual. -/
def ClassifiedResidual.support (cr : ClassifiedResidual) : ℕ :=
  cr.weights.length

/-- Signed values. -/
def ClassifiedResidual.signedVals (cr : ClassifiedResidual) : List ℤ :=
  (cr.weights.zip cr.signs).map fun ⟨w, s⟩ =>
    if s then (w : ℤ) else -(w : ℤ)

/-- Carrier complexity + smooth count = total support. -/
theorem ClassifiedResidual.cc_plus_smooth (cr : ClassifiedResidual) :
    cr.carrierComplexity + cr.smoothCount = cr.classes.length := by
  simp only [carrierComplexity, smoothCount]
  induction cr.classes with
  | nil => rfl
  | cons h t ih =>
    simp [List.countP_cons]
    cases h <;> (simp; omega)

end UniformClassification

/-! ## Section 5: Support-Size Parametric Definitions

These definitions work uniformly for any support size, enabling the same
framework to handle support-5 (already analyzed), support-6 (next step),
and support-7+ (future). -/

section ParametricSupport

/-- The **peel origin** records which primitive identity and which prime peel
    produced this residual. This metadata is carried for traceability but is
    not part of the mathematical verification. -/
structure PeelOrigin where
  /-- Support of the original primitive identity -/
  originalSupport : ℕ
  /-- The prime used for the p-adic peel -/
  peelPrime : ℕ
  /-- Index or identifier of the original core -/
  coreId : ℕ
  deriving DecidableEq, Repr

/-- A **peel result** bundles a classified residual with its origin metadata. -/
structure PeelResult where
  /-- The residual equation with classification -/
  residual : ClassifiedResidual
  /-- Where this residual came from -/
  origin : PeelOrigin

/-- Is this a "bad" peel (carrier complexity > 0)? -/
def PeelResult.isBad (pr : PeelResult) : Bool :=
  pr.residual.carrierComplexity > 0

/-- The carrier complexity of a peel result. -/
def PeelResult.carrierComplexity (pr : PeelResult) : ℕ :=
  pr.residual.carrierComplexity

end ParametricSupport

/-! ## Section 6: Batch Verification Infrastructure

This section provides the machinery for verifying large batches of certificates
imported from CSV/Kaggle scans. The workflow is:

1. **CSV → Lean**: A script converts CSV rows to `ClassifiedResidual` literals.
   Each row contains: label, weights, signs, classes.

2. **Batch list**: All certificates are collected in a single `List ClassifiedResidual`.

3. **Batch verification**: A single theorem states that every certificate in the
   list is valid (equation balances, classification is correct).

4. **Distribution extraction**: Count certificates by carrier complexity to get
   the distribution.

### Example batch (placeholder for future data import)
-/

section BatchVerification

/-- The carrier complexity distribution of a batch of peel results.
    Returns pairs (complexity, count). -/
def carrierComplexityDistribution (batch : List PeelResult) : List (ℕ × ℕ) :=
  let complexities := batch.map PeelResult.carrierComplexity
  let maxCC := complexities.foldl max 0
  (List.range (maxCC + 1)).map fun cc =>
    (cc, complexities.filter (· == cc) |>.length)

/-!
### Placeholder: Support-6 batch

No support-6 data has been imported yet. When the Kaggle scan is complete,
the data will be imported here as a list of `ClassifiedResidual` instances.

Expected format of each entry:

```
{ label := "s6_core_42_v2peel",
  weights := [w₁, w₂, w₃, w₄, w₅],
  signs := [true, true, false, false, false],
  classes := [.carrier, .smooth, .smooth, .smooth, .smooth],
  len_weights_signs := rfl,
  len_weights_classes := rfl,
  nonempty := by norm_num }
```

The key empirical question: **does the carrier complexity distribution for
support-6 remain concentrated at ≤ 1?**

Possible outcomes:
- **CC ≤ 1 universal**: Same as support-5. Strong evidence for bounded carrier descent.
- **CC ≤ 2 universal**: Carrier complexity grows by 1 per support level. Still bounded.
- **CC grows with support**: Bad news for the bounded-carrier descent strategy.
- **CC ≤ 1 with rare CC = 2 exceptions**: May still be manageable with case analysis.
-/

end BatchVerification

/-! ## Section 7: Structural Lemmas for Carrier Complexity

These lemmas relate carrier complexity to the algebraic structure of the
residual equation. They apply to any support size. -/

section StructuralLemmas

/-- In a balanced residual equation, the signed values sum to zero. -/
theorem balanced_sum_zero (eq : ResidualEquation) (hb : eq.IsBalanced) :
    eq.signedVals.sum = 0 :=
  hb

/-- A CC0 certificate can be converted to a classified residual with
    all terms tagged smooth. -/
def CC0Certificate.toClassifiedResidual (c : CC0Certificate) : ClassifiedResidual where
  label := c.label
  weights := c.weights
  signs := c.signs
  classes := c.weights.map fun _ => TermClass.smooth
  len_weights_signs := c.lengths_match
  len_weights_classes := by simp
  nonempty := c.nonempty

/-- The carrier complexity of a CC0-derived classified residual is 0. -/
theorem cc0_classified_complexity_zero (c : CC0Certificate) :
    (c.toClassifiedResidual).carrierComplexity = 0 := by
  unfold ClassifiedResidual.carrierComplexity CC0Certificate.toClassifiedResidual
  simp only
  induction c.weights with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.map, List.countP_cons]
    simp

/-- A CC2 certificate can be converted to a classified residual with
    the two carrier terms tagged and the rest tagged smooth. -/
def CC2Certificate.toClassifiedResidual (c : CC2Certificate) : ClassifiedResidual where
  label := c.label
  weights := [c.carrier1Weight, c.carrier2Weight] ++ c.smoothWeights
  signs := [c.carrier1Sign, c.carrier2Sign] ++ c.smoothSigns
  classes := [TermClass.carrier, TermClass.carrier] ++ c.smoothWeights.map fun _ => TermClass.smooth
  len_weights_signs := by simp [c.lengths_match]
  len_weights_classes := by simp
  nonempty := by simp

end StructuralLemmas

/-! ## Section 8: Connection to Carrier-1 Framework (Session 10)

We show that the existing `Carrier1Certificate` framework from Session 10
embeds cleanly into the generalized framework. -/

section Carrier1Bridge

/-- Convert a `Carrier1Certificate` to a `ClassifiedResidual` with
    the carrier term tagged and the rest tagged smooth. -/
def Carrier1Certificate.toClassifiedResidual (c : Carrier1Certificate) : ClassifiedResidual where
  label := c.name
  weights := c.carrierWeight :: c.smoothWeights
  signs := c.carrierSign :: c.smoothSigns
  classes := TermClass.carrier :: c.smoothWeights.map fun _ => TermClass.smooth
  len_weights_signs := by simp [c.lengths_match]
  len_weights_classes := by simp
  nonempty := by simp

/-- The carrier complexity of a Carrier1Certificate-derived classified residual is 1. -/
theorem carrier1_classified_complexity_one (c : Carrier1Certificate) :
    (c.toClassifiedResidual).carrierComplexity = 1 := by
  unfold ClassifiedResidual.carrierComplexity Carrier1Certificate.toClassifiedResidual
  simp only [List.countP_cons]
  simp

end Carrier1Bridge

/-! ## Section 9: Expected Empirical Questions for Support-6

The following are the key questions that the support-6 Kaggle scan should answer.
They are stated as informal conjectures, NOT as sorry'd theorems.

### Q1: How many primitive support-6 {2,3}-smooth identities exist up to 10⁶?

For context, support-5 had 1213 primitive cores. Support-6 is expected to have
significantly more (possibly 10,000+).

### Q2: What fraction of support-6 peels are "bad" (produce outside-ALLOWED cofactors)?

For support-5, 400/1213 ≈ 33% were bad. The fraction for support-6 is unknown.

### Q3: What is the carrier complexity distribution for bad support-6 peels?

This is THE decisive question. Possible outcomes:

| Outcome | Implication |
|---------|-------------|
| All CC = 1 | Strong: bounded carrier descent holds at support-6 |
| All CC ≤ 1 (with CC = 0 cases) | Good: some peels stay ALLOWED-smooth |
| CC ≤ 2 universal | Moderate: carrier complexity grows slowly with support |
| Unbounded CC | Bad: carrier descent fails as a strategy |

### Q4: Do support-6 carrier-2 residuals (if any) exhibit structure?

If CC = 2 cases appear:
- Are the two carrier primes always distinct?
- Is one of them always from a small set?
- Can carrier-2 equations be decomposed into carrier-1 pieces?

### Q5: What is the minimum relation support among support-6 identities?

For support-5, the minimum residual support after peel was 3. Support-6 may
produce residuals of support 3, 4, or 5.

### Q6: Does the distribution depend on the peel prime (2 vs 3)?

For support-5, both v₂-peels and v₃-peels gave CC = 1. Is this the same
for support-6?
-/

/-! ## Section 10: Summary and Next Steps

### What this file provides

1. **`ResidualEquation`**: General residual equation structure for any support size
2. **`CC0Certificate`**, **`CC2Certificate`**: Certificate structures for CC = 0 and CC = 2
   (CC = 1 already handled by `Carrier1Certificate` from Session 10)
3. **`ClassifiedResidual`**: Uniform classification structure for batch verification
4. **`PeelOrigin`**, **`PeelResult`**: Metadata and result bundling for traceability
5. **Batch verification infrastructure**: List processing, distribution counting
6. **Bridge lemmas**: Converting Session 10 certificates to the new framework
7. **Synthetic CC2 examples**: Demonstrating the CC2 framework works (not from data)

### What this file does NOT provide

- **No support-6 empirical data**: The Kaggle scan has not been run yet
- **No sorry-based proofs or conjectures**: All theorems are fully proved
- **No claim of universal bounded carrier**: That awaits the support-6 data
- **No tail decay analysis**: Deferred per instructions

### Next steps (Session 12+)

1. Run the support-6 Kaggle scan (enumerate primitive support-6 {2,3}-smooth
   identities up to 10⁶)
2. For each, compute all p-adic peels and classify residuals
3. Export as CSV: `support, cc, weights, signs, classes`
4. Import CSV into this framework as `ClassifiedResidual` instances
5. Verify all certificates in Lean
6. Extract the carrier complexity distribution
7. Based on the distribution:
   - If CC ≤ 1 universal → formalize bounded carrier descent
   - If CC ≤ 2 universal → extend analysis to CC = 2 structure
   - If unbounded → reassess the carrier descent strategy entirely
-/
