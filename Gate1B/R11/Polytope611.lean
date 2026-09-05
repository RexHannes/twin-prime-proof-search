/-
# Gate1B / R11 : full-polytope rational geometry and the uniform `6/11` cutoff

Pure ordered-field geometry.  Nothing analytic is claimed or used here: every statement
below is a linear consequence of

* positivity of the smallest coordinate,
* the monotone ordering `x₀ ≤ x₁ ≤ ⋯ ≤ x₁₀`,
* the normalisation `∑ xᵢ = 1`,

together with — where explicitly assumed — the two CARD5 chamber inequalities

* `x₆+x₇+x₈+x₉+x₁₀ ≤ γ`,
* `x₀+x₇+x₈+x₉+x₁₀ ≤ γ`.

The three block coordinates are `M = x₀+⋯+x₄`, `N = x₅+⋯+x₈`, `L = x₉+x₁₀`.

**Firewall.**  The stronger rational bounds `2/5 + (6/5)ε ≤ M` and `1/3 + (2/3)ε ≤ N`
are *not* consequences of the ordering and the normalisation alone: they need the chamber
parameter to be pinned at `γ ≤ 1/2 − ε`.  That extra source hypothesis is carried
explicitly in the statements, and §5 exhibits kernel-checked counterexamples showing that
without it the two bounds are false.  Nothing is invented.
-/
import Mathlib

namespace Gate1B.R11

open Finset

/-! ## 1. The exponent vector -/

/-- An abstract ordered exponent vector: eleven coordinates, positive, non-decreasing,
summing to `1`. -/
structure ExponentVector where
  /-- The eleven exponents. -/
  x : Fin 11 → ℝ
  /-- The smallest coordinate is positive. -/
  x_pos : 0 < x 0
  /-- The coordinates are non-decreasing. -/
  x_mono : Monotone x
  /-- The coordinates sum to `1`. -/
  x_sum : ∑ i, x i = 1

namespace ExponentVector

variable (v : ExponentVector)

/-- The `M`-block `x₀+x₁+x₂+x₃+x₄`. -/
def Mblock : ℝ := v.x 0 + v.x 1 + v.x 2 + v.x 3 + v.x 4

/-- The `N`-block `x₅+x₆+x₇+x₈`. -/
def Nblock : ℝ := v.x 5 + v.x 6 + v.x 7 + v.x 8

/-- The `L`-block `x₉+x₁₀`. -/
def Lblock : ℝ := v.x 9 + v.x 10

/-- The normalisation, written out coordinatewise. -/
theorem sum_expanded :
    v.x 0 + v.x 1 + v.x 2 + v.x 3 + v.x 4 + v.x 5 + v.x 6 + v.x 7 + v.x 8 + v.x 9 + v.x 10 = 1 := by
  have e : ∑ i, v.x i
      = v.x 0 + v.x 1 + v.x 2 + v.x 3 + v.x 4 + v.x 5 + v.x 6 + v.x 7 + v.x 8 + v.x 9 + v.x 10 := by
    simp [Fin.sum_univ_succ]
    ring
  linarith [e, v.x_sum]

/-- The full monotone chain, as ten separate inequalities (convenient for `linarith`). -/
theorem chain :
    v.x 0 ≤ v.x 1 ∧ v.x 1 ≤ v.x 2 ∧ v.x 2 ≤ v.x 3 ∧ v.x 3 ≤ v.x 4 ∧ v.x 4 ≤ v.x 5 ∧
      v.x 5 ≤ v.x 6 ∧ v.x 6 ≤ v.x 7 ∧ v.x 7 ≤ v.x 8 ∧ v.x 8 ≤ v.x 9 ∧ v.x 9 ≤ v.x 10 :=
  ⟨v.x_mono (by decide), v.x_mono (by decide), v.x_mono (by decide), v.x_mono (by decide),
   v.x_mono (by decide), v.x_mono (by decide), v.x_mono (by decide), v.x_mono (by decide),
   v.x_mono (by decide), v.x_mono (by decide)⟩

/-! ## 2. Unconditional block geometry -/

/-- **Block conservation.**  `M + N + L = 1`. -/
theorem block_sum : v.Mblock + v.Nblock + v.Lblock = 1 := by
  have h := v.sum_expanded
  simp only [Mblock, Nblock, Lblock]
  linarith

/-- **`M ≤ 5/11`.**  The five smallest of eleven ordered coordinates carry at most `5/11`
of the total mass. -/
theorem Mblock_le : v.Mblock ≤ 5 / 11 := by
  obtain ⟨h01, h12, h23, h34, h45, h56, h67, h78, h89, h910⟩ := v.chain
  have h := v.sum_expanded
  simp only [Mblock]
  linarith

/-- **Uniform `6/11` geometry.**  The complementary mass is at least `6/11`. -/
theorem one_sub_Mblock_ge : 6 / 11 ≤ 1 - v.Mblock := by
  have := v.Mblock_le
  linarith

/-- **`L ≥ 2/11`.**  The two largest of eleven ordered coordinates carry at least `2/11`
of the total mass. -/
theorem Lblock_ge : 2 / 11 ≤ v.Lblock := by
  obtain ⟨h01, h12, h23, h34, h45, h56, h67, h78, h89, h910⟩ := v.chain
  have h := v.sum_expanded
  simp only [Lblock]
  linarith

/-- Every block is positive. -/
theorem blocks_pos : 0 < v.Mblock ∧ 0 < v.Nblock ∧ 0 < v.Lblock := by
  obtain ⟨h01, h12, h23, h34, h45, h56, h67, h78, h89, h910⟩ := v.chain
  have hp := v.x_pos
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mblock, Nblock, Lblock] <;> linarith

/-! ## 3. The CARD5 chamber -/

/-- The CARD5 chamber conditions at parameter `γ`. -/
structure Card5Chamber (γ : ℝ) : Prop where
  /-- `x₆+x₇+x₈+x₉+x₁₀ ≤ γ`. -/
  top_five : v.x 6 + v.x 7 + v.x 8 + v.x 9 + v.x 10 ≤ γ
  /-- `x₀+x₇+x₈+x₉+x₁₀ ≤ γ`. -/
  mixed_five : v.x 0 + v.x 7 + v.x 8 + v.x 9 + v.x 10 ≤ γ

/-- In the chamber, `L ≤ γ`. -/
theorem Lblock_le_of_chamber {γ : ℝ} (h : v.Card5Chamber γ) : v.Lblock ≤ γ := by
  obtain ⟨h01, h12, h23, h34, h45, h56, h67, h78, h89, h910⟩ := v.chain
  have hp := v.x_pos
  have := h.top_five
  simp only [Lblock]
  linarith

/-- **Chamber lower bound for `M`.**  `M ≥ 1 − (6/5)γ`, from `x₅ ≤ γ/5`. -/
theorem Mblock_ge_of_chamber {γ : ℝ} (h : v.Card5Chamber γ) : 1 - (6 / 5) * γ ≤ v.Mblock := by
  obtain ⟨h01, h12, h23, h34, h45, h56, h67, h78, h89, h910⟩ := v.chain
  have hs := v.sum_expanded
  have ht := h.top_five
  simp only [Mblock]
  linarith

/-- **Chamber lower bound for `N`.**  `N ≥ (2/3)(1 − γ)`, from `1 − γ ≤ x₀+⋯+x₅ ≤ 6x₅`. -/
theorem Nblock_ge_of_chamber {γ : ℝ} (h : v.Card5Chamber γ) : (2 / 3) * (1 - γ) ≤ v.Nblock := by
  obtain ⟨h01, h12, h23, h34, h45, h56, h67, h78, h89, h910⟩ := v.chain
  have hs := v.sum_expanded
  have ht := h.top_five
  simp only [Nblock]
  linarith

/-! ## 4. The pinned chamber `γ ≤ 1/2 − ε`

These are exactly the rational bounds quoted by the research compiler.  They are stated
*conditionally* on the pin `γ ≤ 1/2 − ε`, which is the extra source hypothesis they need;
§5 shows they fail without it. -/

/-- **`2/5 + (6/5)ε ≤ M`** in a chamber pinned at `γ ≤ 1/2 − ε`. -/
theorem Mblock_ge_pinned {γ ε : ℝ} (h : v.Card5Chamber γ) (hpin : γ ≤ 1 / 2 - ε) :
    2 / 5 + (6 / 5) * ε ≤ v.Mblock := by
  have h1 := v.Mblock_ge_of_chamber h
  linarith

/-- **`1/3 + (2/3)ε ≤ N`** in a chamber pinned at `γ ≤ 1/2 − ε`. -/
theorem Nblock_ge_pinned {γ ε : ℝ} (h : v.Card5Chamber γ) (hpin : γ ≤ 1 / 2 - ε) :
    1 / 3 + (2 / 3) * ε ≤ v.Nblock := by
  have h1 := v.Nblock_ge_of_chamber h
  linarith

/-- **The pinned CARD5 ledger.**  All four rational bounds together. -/
theorem pinned_ledger {γ ε : ℝ} (h : v.Card5Chamber γ) (hpin : γ ≤ 1 / 2 - ε) :
    2 / 5 + (6 / 5) * ε ≤ v.Mblock ∧ 1 / 3 + (2 / 3) * ε ≤ v.Nblock ∧ 2 / 11 ≤ v.Lblock ∧
      v.Mblock ≤ 5 / 11 ∧ 6 / 11 ≤ 1 - v.Mblock :=
  ⟨v.Mblock_ge_pinned h hpin, v.Nblock_ge_pinned h hpin, v.Lblock_ge, v.Mblock_le,
    v.one_sub_Mblock_ge⟩

end ExponentVector

/-! ## 5. Counterexamples: the pin is load-bearing -/

/-- An exponent vector with a very small `M`-block: five coordinates `1/100`, six
coordinates `95/600`. -/
noncomputable def smallMVector : ExponentVector where
  x := fun i => if (i : ℕ) ≤ 4 then 1 / 100 else 95 / 600
  x_pos := by norm_num
  x_mono := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i <;> norm_num
  x_sum := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num

/-- An exponent vector with a very small `N`-block: nine coordinates `1/100`, two
coordinates `91/200`. -/
noncomputable def smallNVector : ExponentVector where
  x := fun i => if (i : ℕ) ≤ 8 then 1 / 100 else 91 / 200
  x_pos := by norm_num
  x_mono := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i <;> norm_num
  x_sum := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num

/-- **The `M ≥ 2/5` bound is not chamber-free.**  `smallMVector` satisfies the CARD5
chamber conditions at `γ = 1` and has `M = 1/20 < 2/5`. -/
theorem smallMVector_counterexample :
    smallMVector.Card5Chamber 1 ∧ smallMVector.Mblock < 2 / 5 := by
  refine ⟨⟨by norm_num [smallMVector], by norm_num [smallMVector]⟩, ?_⟩
  simp only [ExponentVector.Mblock]
  norm_num [smallMVector]

/-- **The `N ≥ 1/3` bound is not chamber-free.**  `smallNVector` satisfies the CARD5
chamber conditions at `γ = 1` and has `N = 1/25 < 1/3`. -/
theorem smallNVector_counterexample :
    smallNVector.Card5Chamber 1 ∧ smallNVector.Nblock < 1 / 3 := by
  refine ⟨⟨by norm_num [smallNVector], by norm_num [smallNVector]⟩, ?_⟩
  simp only [ExponentVector.Nblock]
  norm_num [smallNVector]

/-! ## 6. The Pascadi-margin dictionary

We do **not** formalize Pascadi's analytic theorem, and we do not postulate it.  What we
record is a `Prop` bundling exactly the finite rational inequalities that the research
compiler consumes, and a kernel proof that the polytope geometry supplies them.  No
analytic discrepancy estimate is stated, implied, or used. -/

/-- The finite rational dictionary consumed by the exponent compiler: block conservation,
the uniform `6/11` complementary mass, the `5/11` cap, and the margin `2θ < 1 − M` at the
recorded value of `θ`. -/
structure PascadiExponentConditions (M N L R θ : ℝ) : Prop where
  /-- Block conservation `M + N + L = 1`. -/
  conservation : M + N + L = 1
  /-- `R` is the complementary block mass. -/
  complement : R = 1 - M
  /-- The `M`-cap. -/
  cap : M ≤ 5 / 11
  /-- The uniform `6/11` cutoff. -/
  uniform : 6 / 11 ≤ R
  /-- The two largest coordinates carry at least `2/11`. -/
  tail : 2 / 11 ≤ L
  /-- The recorded exponent margin: twice the sieve exponent stays below the complementary
  mass. -/
  margin : 2 * θ < R

/-- **The polytope supplies the dictionary at `θ = 7/32`.**  Purely rational; nothing
analytic is asserted. -/
theorem pascadi_conditions_of_polytope (v : ExponentVector) :
    PascadiExponentConditions v.Mblock v.Nblock v.Lblock (1 - v.Mblock) (7 / 32) where
  conservation := v.block_sum
  complement := rfl
  cap := v.Mblock_le
  uniform := v.one_sub_Mblock_ge
  tail := v.Lblock_ge
  margin := by have := v.Mblock_le; linarith

/-- The recorded margin inequality in isolated rational form: `2·(7/32) = 7/16 < 6/11`. -/
theorem theta_margin_rational : 2 * (7 / 32 : ℝ) < 6 / 11 := by norm_num

end Gate1B.R11
