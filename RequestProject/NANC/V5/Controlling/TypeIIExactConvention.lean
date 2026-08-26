/-
NANC V5 CONTROLLING LAYER — THE EXACT TYPE-II INTERVAL CONVENTION.

The source's Type-II hypothesis is stated on the interval

    (X/2)^θ  <  m  ≤  X^(θ+ν),

with the **lower endpoint at `(X/2)^θ`**, not at `X^θ`.  This file records that
convention exactly (real exponentiation, no asymptotic notation), defines the
Type-II predicate over the resulting range — retaining the literal universal
quantifier over arbitrary divisor-bounded `ξ, κ` from the V4 predicate — and
proves that replacing the lower endpoint by `X^θ` changes the range.

UNINHABITED: `FMTypeIIExactAtScale`.

PERMANENT FIREWALL:
    sourceSpecificTypeII  ≠  FMTypeIIExactAtScale
without a full reassembly certificate.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.FordMaynardMetadata

namespace NANC.V5.Controlling

open scoped BigOperators
open NANC.V4

/-- The exact lower endpoint `(X/2)^θ` of the Type-II range. -/
noncomputable def typeIILowerEndpoint (X : ℕ) (theta : ℚ) : ℝ :=
  ((X : ℝ) / 2) ^ (theta : ℝ)

/-- The naive (incorrect) lower endpoint `X^θ`, recorded only to be kept apart. -/
noncomputable def typeIINaiveLowerEndpoint (X : ℕ) (theta : ℚ) : ℝ :=
  (X : ℝ) ^ (theta : ℝ)

/-- The upper endpoint `X^(θ+ν)` of the Type-II range. -/
noncomputable def typeIIUpperEndpoint (X : ℕ) (theta nu : ℚ) : ℝ :=
  (X : ℝ) ^ ((theta + nu : ℚ) : ℝ)

/-- Membership in the exact Type-II range: `(X/2)^θ < m ≤ X^(θ+ν)`. -/
def InTypeIIRangeExact (X : ℕ) (theta nu : ℚ) (m : ℕ) : Prop :=
  typeIILowerEndpoint X theta < (m : ℝ) ∧ (m : ℝ) ≤ typeIIUpperEndpoint X theta nu

/-- Membership in the naive range `X^θ < m ≤ X^(θ+ν)`. -/
def InTypeIIRangeNaive (X : ℕ) (theta nu : ℚ) (m : ℕ) : Prop :=
  typeIINaiveLowerEndpoint X theta < (m : ℝ) ∧ (m : ℝ) ≤ typeIIUpperEndpoint X theta nu

open Classical in
/-- The exact Type-II range, cut out of a supplied finite family of candidates. -/
noncomputable def exactTypeIIRange (X : ℕ) (theta nu : ℚ) (candidates : Finset ℕ) : Finset ℕ :=
  candidates.filter (fun m => InTypeIIRangeExact X theta nu m)

open Classical in
/-- The naive Type-II range, cut out of the same candidates. -/
noncomputable def naiveTypeIIRange (X : ℕ) (theta nu : ℚ) (candidates : Finset ℕ) : Finset ℕ :=
  candidates.filter (fun m => InTypeIIRangeNaive X theta nu m)

theorem mem_exactTypeIIRange {X : ℕ} {theta nu : ℚ} {candidates : Finset ℕ} {m : ℕ} :
    m ∈ exactTypeIIRange X theta nu candidates ↔
      m ∈ candidates ∧ InTypeIIRangeExact X theta nu m := by
  classical
  simp [exactTypeIIRange]

theorem mem_naiveTypeIIRange {X : ℕ} {theta nu : ℚ} {candidates : Finset ℕ} {m : ℕ} :
    m ∈ naiveTypeIIRange X theta nu candidates ↔
      m ∈ candidates ∧ InTypeIIRangeNaive X theta nu m := by
  classical
  simp [naiveTypeIIRange]

/-- **Firewall (finite witness).**  The two conventions are not interchangeable:
for `X = 4`, `θ = 1`, `ν = 0` the multiplier `m = 3` lies in the exact range
`(X/2)^θ < m ≤ X^(θ+ν)` but not in the naive range `X^θ < m ≤ X^(θ+ν)`. -/
theorem exact_range_ne_naive_range :
    ∃ (X : ℕ) (theta nu : ℚ) (candidates : Finset ℕ),
      exactTypeIIRange X theta nu candidates ≠ naiveTypeIIRange X theta nu candidates := by
  classical
  refine ⟨4, 1, 0, {3}, ?_⟩
  intro hEq
  have h3 : (3 : ℕ) ∈ exactTypeIIRange 4 1 0 {3} := by
    rw [mem_exactTypeIIRange]
    refine ⟨by simp, ?_, ?_⟩
    · simp only [typeIILowerEndpoint, Rat.cast_one, Real.rpow_one]
      norm_num
    · simp only [typeIIUpperEndpoint]
      norm_num
  rw [hEq, mem_naiveTypeIIRange] at h3
  obtain ⟨-, hlow, -⟩ := h3
  simp only [typeIINaiveLowerEndpoint, Rat.cast_one, Real.rpow_one] at hlow
  norm_num at hlow

/-- **The exact Ford–Maynard Type-II hypothesis at scale (UNINHABITED).**

The V4 Type-II predicate — in which the universal quantifier over arbitrary
divisor-bounded complex `ξ, κ` appears literally — taken over the range cut out
by the *exact* endpoint convention `(X/2)^θ < m ≤ X^(θ+ν)`. -/
noncomputable def FMTypeIIExactAtScale (X : ℕ) (theta nu : ℚ) (candidates nRange : Finset ℕ)
    (dwM dwN : ℕ → ℝ) (w : ℕ → ℂ) (target : ℝ) : Prop :=
  FMTypeIIAtScale X (exactTypeIIRange X theta nu candidates) nRange dwM dwN w target

/-- The universal quantifier is retained: the exact hypothesis specializes to any
divisor-bounded pair of source coefficients. -/
theorem FMTypeIIExact_imp_sourceSpecific {X : ℕ} {theta nu : ℚ} {candidates nRange : Finset ℕ}
    {dwM dwN : ℕ → ℝ} {w : ℕ → ℂ} {target : ℝ} {xi0 kappa0 : ℕ → ℂ}
    (h : FMTypeIIExactAtScale X theta nu candidates nRange dwM dwN w target)
    (hxi : DivisorBoundedCoeff (exactTypeIIRange X theta nu candidates) dwM xi0)
    (hkappa : DivisorBoundedCoeff nRange dwN kappa0) :
    SourceSpecificTypeII X (exactTypeIIRange X theta nu candidates) nRange w xi0 kappa0 target :=
  h xi0 kappa0 hxi hkappa

/-- **Firewall (finite counterexample).**  The converse fails: a source-specific
bilinear bound on the exact range does *not* give the exact Type-II hypothesis.
Witness: `X = 4`, `θ = 1`, `ν = 0`, candidates `{3}`, inner range `{1}`, `w ≡ 1`,
divisor weights `≡ 1`, target `0`, source coefficients `ξ₀ = κ₀ = 0`. -/
theorem sourceSpecific_not_FMTypeIIExact :
    ∃ (X : ℕ) (theta nu : ℚ) (candidates nRange : Finset ℕ) (dwM dwN : ℕ → ℝ) (w : ℕ → ℂ)
      (xi0 kappa0 : ℕ → ℂ) (target : ℝ),
      DivisorBoundedCoeff (exactTypeIIRange X theta nu candidates) dwM xi0 ∧
      DivisorBoundedCoeff nRange dwN kappa0 ∧
      SourceSpecificTypeII X (exactTypeIIRange X theta nu candidates) nRange w xi0 kappa0
        target ∧
      ¬ FMTypeIIExactAtScale X theta nu candidates nRange dwM dwN w target := by
  classical
  have hrange : exactTypeIIRange 4 1 0 {3} = {3} := by
    have h3 : InTypeIIRangeExact 4 1 0 3 := by
      refine ⟨?_, ?_⟩
      · simp only [typeIILowerEndpoint, Rat.cast_one, Real.rpow_one]
        norm_num
      · simp only [typeIIUpperEndpoint]
        norm_num
    ext m
    rw [mem_exactTypeIIRange]
    constructor
    · rintro ⟨hm, -⟩; exact hm
    · intro hm
      have : m = 3 := Finset.mem_singleton.mp hm
      subst this
      exact ⟨hm, h3⟩
  refine ⟨4, 1, 0, {3}, {1}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0, 0,
    ?_, ?_, ?_, ?_⟩
  · intro m _; norm_num
  · intro m _; norm_num
  · simp [SourceSpecificTypeII, typeIISum]
  · intro h
    have h1 := h (fun _ => 1) (fun _ => 1) (fun m _ => by norm_num) (fun m _ => by norm_num)
    rw [hrange] at h1
    simp [typeIISum, dyadicSupport] at h1

/-- Status entry for the exact Type-II convention. -/
def typeIIConventionEntry : ControlEntry where
  name := "Ford–Maynard Type-II interval convention (X/2)^θ < m ≤ X^(θ+ν)"
  status := ControlStatus.leanProved
  notes := "The endpoint convention is recorded exactly; the predicate itself is uninhabited."

/-- Status entry for the exact Type-II hypothesis itself: uninhabited. -/
def typeIIExactEntry : ControlEntry where
  name := "FMTypeIIExactAtScale"
  status := ControlStatus.uninhabitedInterface
  notes := "Arbitrary divisor-bounded ξ, κ are quantified literally; no inhabitant is produced."

theorem typeIIExactEntry_not_leanEvidence :
    ControlEntry.IsLeanEvidence typeIIExactEntry = false := rfl

end NANC.V5.Controlling
