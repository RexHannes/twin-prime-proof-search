import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 26: the `k = 1` four-prime grouping no-go

**PURE RATIONAL NO-GO.**  Pascadi's Proposition 6.3 is an *external analytic
theorem* and is **not** formalized here, nor is anything asserted about its
truth.  What is banked is only this: the exponent dictionary we attempted, for
the four-prime block of the `k = 1` split, is rationally infeasible.

The four-prime block consists of four equal prime-box exponents `1/4` relative
to its own total length.  A three-slot grouping therefore has exponent multiset
`{1/2, 1/4, 1/4}`, i.e. one of the three groupings

  A: `M = 1/2`, `N = L = 1/4`;
  B: `N = 1/2`, `M = L = 1/4`;
  C: `L = 1/2`, `M = N = 1/4`.

The attempted range dictionary is the conjunction

  `M ≤ Rmod`,  `Rmod ≤ N + L − ε`,  `N + L ≤ 2/3 − ε`,  `L ≤ M − ε`,

and each grouping violates at least one conjunct for every `ε > 0`.

**CRITICAL.**  This theorem is only about the exponent dictionary attempted
here.  It does not assert that Pascadi's proposition is false, and it does not
assert that every possible adaptation of its proof is impossible.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace PascadiGrouping

/-- The exponent skeleton of the attempted Proposition-6.3 dictionary. -/
def Prop63RangeSkeleton (M N L Rmod eps : ℚ) : Prop :=
  M ≤ Rmod ∧ Rmod ≤ N + L - eps ∧ N + L ≤ 2 / 3 - eps ∧ L ≤ M - eps

/-! ## 1. Grouping A: `M = 1/2`, `N = L = 1/4` -/

/-- **Grouping A is killed by the range pair** `M ≤ Rmod ≤ N + L − ε`: since
`N + L = 1/2 = M`, it demands `1/2 ≤ Rmod ≤ 1/2 − ε`, impossible for `ε > 0`. -/
theorem groupingA_fails {eps : ℚ} (heps : 0 < eps) :
    ¬ ∃ Rmod : ℚ, Prop63RangeSkeleton (1 / 2) (1 / 4) (1 / 4) Rmod eps := by
  rintro ⟨Rmod, h1, h2, -, -⟩
  have : (1 / 4 : ℚ) + 1 / 4 - eps < 1 / 2 := by linarith
  linarith

/-- The exact arithmetic fact behind Grouping A: the two slots sum to the first
one. -/
theorem groupingA_sum : (1 / 4 : ℚ) + 1 / 4 = 1 / 2 := by norm_num

/-! ## 2. Grouping B: `N = 1/2`, `M = L = 1/4` -/

/-- **Grouping B is killed by** `N + L ≤ 2/3 − ε`: here `N + L = 3/4 > 2/3`. -/
theorem groupingB_fails {eps : ℚ} (heps : 0 < eps) :
    ¬ ∃ Rmod : ℚ, Prop63RangeSkeleton (1 / 4) (1 / 2) (1 / 4) Rmod eps := by
  rintro ⟨Rmod, -, -, h3, -⟩
  have : (1 / 2 : ℚ) + 1 / 4 = 3 / 4 := by norm_num
  rw [this] at h3
  linarith

/-- The margin by which Grouping B fails. -/
theorem groupingB_margin : (3 / 4 : ℚ) - 2 / 3 = 1 / 12 := by norm_num

theorem groupingB_margin_pos : (0 : ℚ) < 3 / 4 - 2 / 3 := by norm_num

/-! ## 3. Grouping C: `L = 1/2`, `M = N = 1/4` -/

/-- **Grouping C is killed by** `L ≤ M − ε`: already `L = 1/2 > 1/4 = M`. -/
theorem groupingC_fails {eps : ℚ} (heps : 0 < eps) :
    ¬ ∃ Rmod : ℚ, Prop63RangeSkeleton (1 / 4) (1 / 4) (1 / 2) Rmod eps := by
  rintro ⟨Rmod, -, -, -, h4⟩
  linarith

/-- The exact arithmetic fact behind Grouping C. -/
theorem groupingC_gap : (1 / 4 : ℚ) < 1 / 2 := by norm_num

/-! ## 4. The packaged no-go -/

/-- **`PASCADI_K1_PROP63_GROUPING_NO_GO`.**  For every `ε > 0`, none of the three
three-slot groupings of the `k = 1` four-prime block satisfies the attempted
Proposition-6.3 exponent skeleton.

**CRITICAL.**  This is a statement about the exponent dictionary attempted in
this project only.  Pascadi's analytic proposition itself is external, is not
formalized here, and is not contradicted by this theorem; nor does this theorem
exclude a proof-level adaptation using a different dictionary. -/
theorem no_four_prime_grouping_satisfies_prop63_exponent_skeleton
    {eps : ℚ} (heps : 0 < eps) :
    (¬ ∃ Rmod : ℚ, Prop63RangeSkeleton (1 / 2) (1 / 4) (1 / 4) Rmod eps) ∧
    (¬ ∃ Rmod : ℚ, Prop63RangeSkeleton (1 / 4) (1 / 2) (1 / 4) Rmod eps) ∧
    (¬ ∃ Rmod : ℚ, Prop63RangeSkeleton (1 / 4) (1 / 4) (1 / 2) Rmod eps) :=
  ⟨groupingA_fails heps, groupingB_fails heps, groupingC_fails heps⟩

/-! ## 5. Guard -/

/-- **Guard.**  The skeleton is not vacuous: for other exponent data it *is*
satisfiable, so the no-go above is a genuine constraint on the `{1/2, 1/4, 1/4}`
multiset and not a defect of the formalisation. -/
theorem prop63_skeleton_satisfiable :
    Prop63RangeSkeleton (1 / 4) (1 / 4) (1 / 8) (1 / 4) (1 / 100) := by
  refine ⟨le_rfl, by norm_num, by norm_num, by norm_num⟩

end PascadiGrouping
end Gate1BDet2
end TwinPrimeProject
