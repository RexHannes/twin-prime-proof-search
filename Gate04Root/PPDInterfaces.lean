/-
# Gate04Root.PPDInterfaces

The PPD bank.

`PPD B T` is the *hypothesis* that the off-diagonal column Gram mass is at most
`T`.  Combined with a repeated-`p` (diagonal) bound it yields, by the exact dual
split of `Gate04Root.MatrixDuality`, the R4C fourth-moment bound.

Nothing here proves PPD, nor any analytic bound on `T`: the analytic estimate is
an explicit hypothesis everywhere.
-/
import Gate04Root.R4CInterfaces

open Finset

namespace Gate04Root

variable {E P : Type*} [Fintype E] [Fintype P]

/-- **PPD hypothesis**: `∑_{p₁ ≠ p₂} |G(p₁,p₂)|² ≤ T`. -/
def PPD (B : E → P → ℂ) [DecidableEq P] (T : ℝ) : Prop := offDiagColSum B ≤ T

/-- **PPD + repeated-`p` ⇒ R4C fourth moment bound** (an exact finite identity
plus two hypotheses). -/
theorem ppd_and_repeatedP_imply_r4c [DecidableEq P] {B : E → P → ℂ} {T U : ℝ}
    (hppd : PPD B T) (hdiag : diagColSum B ≤ U) : fourthMoment B ≤ T + U := by
  rw [fourthMoment_split]
  have : diagColSum B + offDiagColSum B ≤ U + T := add_le_add hdiag hppd
  linarith

/-- Normalised corollary: if the two pieces fit under `S²`, the R4C bound holds
at scale `S`. -/
theorem ppd_and_repeatedP_imply_R4CBound [DecidableEq P] {B : E → P → ℂ}
    {T U S : ℝ} (hppd : PPD B T) (hdiag : diagColSum B ≤ U) (hfit : T + U ≤ S ^ 2) :
    R4CBound B S :=
  le_trans (ppd_and_repeatedP_imply_r4c hppd hdiag) hfit

/-- **Repeated-`p` bound from a pointwise bound.**  If `|B e p| ≤ C` and the
cardinalities are bounded by `E₀`, `P₀`, then `∑_p |G(p,p)|² ≤ P₀ E₀² C⁴`. -/
theorem repeatedP_bound_of_pointwise {B : E → P → ℂ} {C E₀ P₀ : ℝ}
    (hB : ∀ e p, ‖B e p‖ ≤ C)
    (hE : (Fintype.card E : ℝ) ≤ E₀) (hP : (Fintype.card P : ℝ) ≤ P₀) :
    diagColSum B ≤ P₀ * E₀ ^ 2 * C ^ 4 := by
  have hterm : ∀ p : P, ‖colGram B p p‖ ^ 2 ≤ (E₀ * C ^ 2) ^ 2 := by
    intro p
    have h1 : ‖colGram B p p‖ ≤ E₀ * C ^ 2 := by
      calc ‖colGram B p p‖ ≤ ∑ e, ‖B e p * (starRingEnd ℂ) (B e p)‖ :=
            norm_sum_le _ _
        _ = ∑ e, ‖B e p‖ ^ 2 := by
            refine Finset.sum_congr rfl fun e _ => ?_
            simp [sq]
        _ ≤ ∑ _e : E, C ^ 2 := by
            refine Finset.sum_le_sum fun e _ => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hB e p) 2
        _ = (Fintype.card E : ℝ) * C ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ E₀ * C ^ 2 := by
            exact mul_le_mul_of_nonneg_right hE (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc diagColSum B = ∑ p, ‖colGram B p p‖ ^ 2 := rfl
    _ ≤ ∑ _p : P, (E₀ * C ^ 2) ^ 2 := Finset.sum_le_sum fun p _ => hterm p
    _ = (Fintype.card P : ℝ) * (E₀ * C ^ 2) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ P₀ * (E₀ * C ^ 2) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hP (by positivity)
    _ = P₀ * E₀ ^ 2 * C ^ 4 := by ring

/-- Symbolic instantiation `E₀ = M²`, `P₀ = L`, `C = L/H`:  the repeated-`p`
budget is `M⁴ L⁵ / H⁴`. -/
theorem repeatedP_symbolic_bound {M L H : ℝ} (hH : H ≠ 0) :
    L * (M ^ 2) ^ 2 * (L / H) ^ 4 = M ^ 4 * L ^ 5 / H ^ 4 := by
  field_simp

end Gate04Root
