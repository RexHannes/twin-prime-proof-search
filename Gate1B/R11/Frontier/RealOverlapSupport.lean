/-
# Gate1B / R11 / Frontier : real-overlap support

The deterministic support implication used by the current source, formalised exactly and with no
asymptotic notation.

* `logOverlap` is the **logarithmic support condition** of the source,
  `|log (A·B_{j,v} / (B·B_{i,u}))| ≤ h_i + h_j`;
* `ratio_bounds_of_log_le` converts `|log (x/y)| ≤ δ` into the two multiplicative bounds
  `x ≤ y e^δ`, `y ≤ x e^δ`;
* `abs_sub_le_of_log_le` converts these into the additive bound `|x − y| ≤ (max x y)(e^δ − 1)`;
* `exp_sub_one_le_two_mul` gives the explicit linearisation `e^δ − 1 ≤ 2δ` on `0 ≤ δ ≤ 1`,
  whence `|x − y| ≤ 2 δ max x y`;
* `overlap_abs_sub_le` is the source-shaped corollary: under an explicit upper bound `Cp` for both
  products, the logarithmic support condition yields
  `|A·B_{j,v} − B·B_{i,u}| ≤ 2 Cp (h_i + h_j)`.

Nothing here is asymptotic: every constant is explicit and kernel-checked.  In particular the
`O(·)` form of the source inequality is *not* postulated.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Gate1B.R11.Frontier

open Real

/-! ## 1. From a logarithmic bound to multiplicative bounds -/

/-- `|log (x/y)| ≤ δ` gives the two-sided multiplicative control `x ≤ y e^δ`, `y ≤ x e^δ`. -/
theorem ratio_bounds_of_log_le {x y delta : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : |Real.log (x / y)| ≤ delta) : x ≤ y * Real.exp delta ∧ y ≤ x * Real.exp delta := by
  rw [Real.log_div hx.ne' hy.ne', abs_le] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · have : Real.log x ≤ Real.log y + delta := by linarith
    have hexp := Real.exp_le_exp.2 this
    rwa [Real.exp_log hx, Real.exp_add, Real.exp_log hy] at hexp
  · have : Real.log y ≤ Real.log x + delta := by linarith
    have hexp := Real.exp_le_exp.2 this
    rwa [Real.exp_log hy, Real.exp_add, Real.exp_log hx] at hexp

/-- The additive form: `|x − y| ≤ (max x y)(e^δ − 1)`. -/
theorem abs_sub_le_of_log_le {x y delta : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : |Real.log (x / y)| ≤ delta) : |x - y| ≤ max x y * (Real.exp delta - 1) := by
  obtain ⟨h1, h2⟩ := ratio_bounds_of_log_le hx hy h
  have hmx : x ≤ max x y := le_max_left _ _
  have hmy : y ≤ max x y := le_max_right _ _
  have hd : 0 ≤ Real.exp delta - 1 := by
    have : (1 : ℝ) ≤ Real.exp delta := by
      refine Real.one_le_exp ?_
      have habs : (0 : ℝ) ≤ |Real.log (x / y)| := abs_nonneg _
      linarith
    linarith
  rcases abs_cases (x - y) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]
    have : x - y ≤ y * (Real.exp delta - 1) := by nlinarith
    nlinarith
  · rw [heq]
    have : y - x ≤ x * (Real.exp delta - 1) := by nlinarith
    nlinarith

/-! ## 2. Explicit linearisation of `e^δ − 1` -/

/-- On `0 ≤ t ≤ 1` one has `e^t ≤ 1 + 2t`; hence `e^t − 1 ≤ 2t`.  (Proved from convexity of `exp`
and `e < 3`, with no asymptotics.) -/
theorem exp_sub_one_le_two_mul {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.exp t - 1 ≤ 2 * t := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by linarith : (0:ℝ) ≤ 1 - t) h0 (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, Real.exp_zero, zero_add] at hconv
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  nlinarith [Real.exp_pos t]

/-- The explicit control used downstream: `|x − y| ≤ 2 δ max x y` for `0 ≤ δ ≤ 1`. -/
theorem abs_sub_le_two_mul_of_log_le {x y delta : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (h : |Real.log (x / y)| ≤ delta) :
    |x - y| ≤ 2 * delta * max x y := by
  have hmax : 0 < max x y := lt_of_lt_of_le hx (le_max_left _ _)
  refine le_trans (abs_sub_le_of_log_le hx hy h) ?_
  have := exp_sub_one_le_two_mul hd0 hd1
  nlinarith

/-! ## 3. The source-shaped statement -/

/-- **The logarithmic support condition of the source**, stated exactly. -/
def logOverlap (A B Biu Bjv hi hj : ℝ) : Prop :=
  |Real.log ((A * Bjv) / (B * Biu))| ≤ hi + hj

/-- **REAL-OVERLAP SUPPORT.**  Under positivity, an explicit common upper bound `Cp` for both
products, and `h_i + h_j ≤ 1`, the logarithmic support condition gives the explicit additive
bound `|A B_{j,v} − B B_{i,u}| ≤ 2 Cp (h_i + h_j)`. -/
theorem overlap_abs_sub_le {A B Biu Bjv hi hj Cp : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hiu : 0 < Biu) (hjv : 0 < Bjv) (hhi : 0 ≤ hi) (hhj : 0 ≤ hj) (hsum : hi + hj ≤ 1)
    (hCp1 : A * Bjv ≤ Cp) (hCp2 : B * Biu ≤ Cp) (h : logOverlap A B Biu Bjv hi hj) :
    |A * Bjv - B * Biu| ≤ 2 * Cp * (hi + hj) := by
  have hx : 0 < A * Bjv := mul_pos hA hjv
  have hy : 0 < B * Biu := mul_pos hB hiu
  have hmax : max (A * Bjv) (B * Biu) ≤ Cp := max_le hCp1 hCp2
  have hbase := abs_sub_le_two_mul_of_log_le hx hy (by linarith) hsum h
  have hnn : 0 ≤ 2 * (hi + hj) := by linarith
  nlinarith [le_max_left (A * Bjv) (B * Biu), le_max_right (A * Bjv) (B * Biu)]

/-- **FIREWALL.**  The support condition alone gives no *sharper* bound than the linear one: for
`x = e^δ`, `y = 1` the difference is exactly `e^δ − 1`, which is `≥ δ`.  Hence no `o(δ)` gain may
be extracted from the overlap condition. -/
theorem overlap_bound_is_not_o_delta {delta : ℝ} (h0 : 0 ≤ delta) :
    |Real.exp delta - 1| ≥ delta := by
  have h1 : delta + 1 ≤ Real.exp delta := by
    have := Real.add_one_le_exp delta
    linarith
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp delta - 1)]
  linarith

end Gate1B.R11.Frontier
