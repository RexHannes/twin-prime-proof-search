/-
# Gate-1A Δv4 §24 — root depth: exactly one square root over `r`

The Δv4 reassembly uses **one** Cauchy–Schwarz over the moving prime `r`,
and no second root.  The pieces:

* the four-cycle bound `‖A_r‖_op² ≤ ∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²` is already
  banked in `Gate1A/FourCycle.lean` (`outer_four_cycle_operator`) — it is
  reused, not reproved;
* `single_cauchy_over_r` — the single root:
  `∑_r x_r ≤ √(#r) · √(∑_r x_r²)` for nonnegative `x`;
* `root_depth_assembly` — the combination
  `∑_r ‖A_r‖_op ≤ √R · √(∑_r T4_r)` from `‖A_r‖_op² ≤ T4_r`;
* the exponent side `M R^{-1/2} ≤ H` with its vertex margins is in
  `Gate1A/Delta4/Scale.lean` (`root_depth_capacity`, `root_depth_margin_V*`).
-/
import Mathlib
import Gate1A.FourCycle
import Gate1A.Delta4.Scale

namespace Gate1A

namespace Delta4

open Finset Matrix

/-- **The single root.**  Cauchy–Schwarz over `r`, used exactly once. -/
theorem single_cauchy_over_r {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∑ i ∈ s, x i ≤ Real.sqrt (s.card) * Real.sqrt (∑ i ∈ s, (x i) ^ 2) := by
  have h1 : (∑ i ∈ s, x i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (x i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx
  calc ∑ i ∈ s, x i = Real.sqrt ((∑ i ∈ s, x i) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, (x i) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (s.card) * Real.sqrt (∑ i ∈ s, (x i) ^ 2) :=
        Real.sqrt_mul (Nat.cast_nonneg _) _

/-- **§24 (`root_depth_assembly`).**  One Cauchy over `r`, no second root:
from the per-`r` four-cycle bound `‖A_r‖_op² ≤ T4_r` one gets
`∑_r ‖A_r‖_op ≤ √R · √(∑_r T4_r)`, where `R = #{r}`. -/
theorem root_depth_assembly {ι : Type*} (s : Finset ι) (nrm T4 : ι → ℝ)
    (hnrm : ∀ i ∈ s, 0 ≤ nrm i) (hT4 : ∀ i ∈ s, (nrm i) ^ 2 ≤ T4 i) :
    ∑ i ∈ s, nrm i ≤ Real.sqrt (s.card) * Real.sqrt (∑ i ∈ s, T4 i) := by
  refine (single_cauchy_over_r s nrm hnrm).trans ?_
  have hsum : ∑ i ∈ s, (nrm i) ^ 2 ≤ ∑ i ∈ s, T4 i := Finset.sum_le_sum hT4
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _)

/-- The banked four-cycle input, restated in the Δv4 vocabulary:
`‖∑_m T_mᴴ T_m‖_HS² = ∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²` (an exact identity;
`hsNormSq` is the *squared* Hilbert–Schmidt norm).  Reused verbatim from the
banked four-cycle module, not reproved. -/
theorem four_cycle_input {iota K I : Type*} [Fintype iota] [Fintype K] [Fintype I]
    (T : iota → Matrix K I ℂ) :
    FourCycle.hsNormSq (FourCycle.gram T)
      = ∑ m : iota, ∑ m' : iota, FourCycle.hsNormSq (T m * (T m')ᴴ) :=
  FourCycle.outer_four_cycle_matrix T

end Delta4

end Gate1A
