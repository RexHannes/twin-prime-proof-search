/-
# Gate04Root.R4CInterfaces

The **conditional** R4C implications.

`R4CBound B T` is the finite hypothesis `fourthMoment B ≤ T^2`, i.e. the
Hilbert–Schmidt bound `tr((B Bᴴ)²) ≤ T²`.  We prove, by three applications of the
finite Cauchy–Schwarz inequality, that it implies the squared-operator-norm
bound

  `∑_e |∑_p B e p x p|² ≤ T ∑_p |x p|²`   for all `x`,

and the derived scale statements.  Nothing here proves R4C itself: `R4CBound` is
always a hypothesis.
-/
import Gate04Root.MatrixDuality

open Finset

namespace Gate04Root

/-- The squared `ℓ²` norm of a finite complex vector. -/
noncomputable def nsq {ι : Type*} [Fintype ι] (f : ι → ℂ) : ℝ := ∑ i, ‖f i‖ ^ 2

theorem nsq_nonneg {ι : Type*} [Fintype ι] (f : ι → ℂ) : 0 ≤ nsq f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nsq_conj {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    nsq (fun i => (starRingEnd ℂ) (f i)) = nsq f := by
  simp [nsq]

/-- Finite Cauchy–Schwarz in squared form. -/
theorem cs_sq {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * (starRingEnd ℂ) (b i)‖ ^ 2 ≤ nsq a * nsq b := by
  have h1 : ‖∑ i, a i * (starRingEnd ℂ) (b i)‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by simp)
  have h2 : (∑ i, ‖a i‖ * ‖b i‖) ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖∑ i, a i * (starRingEnd ℂ) (b i)‖ ^ 2
      ≤ (∑ i, ‖a i‖ * ‖b i‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ nsq a * nsq b := h2

variable {E P : Type*} [Fintype E] [Fintype P]

/-- The image vector `B x`. -/
noncomputable def applyB (B : E → P → ℂ) (x : P → ℂ) : E → ℂ := fun e => ∑ p, B e p * x p

/-- The adjoint image `Bᴴ v`. -/
noncomputable def applyBstar (B : E → P → ℂ) (v : E → ℂ) : P → ℂ :=
  fun p => ∑ e, (starRingEnd ℂ) (B e p) * v e

/-- The row-Gram image `H v`. -/
noncomputable def applyH (B : E → P → ℂ) (v : E → ℂ) : E → ℂ :=
  fun f => ∑ e, rowGram B f e * v e

private def swap3 : P × E × E ≃ E × E × P where
  toFun z := (z.2.2, z.2.1, z.1)
  invFun y := (y.2.2, y.2.1, y.1)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum3_comm (T : P → E → E → ℂ) :
    ∑ p, ∑ e, ∑ f, T p e f = ∑ f, ∑ e, ∑ p, T p e f := by
  have h1 : ∑ p, ∑ e, ∑ f, T p e f = ∑ z : P × E × E, T z.1 z.2.1 z.2.2 := by
    simp [Fintype.sum_prod_type]
  have h2 : ∑ f, ∑ e, ∑ p, T p e f = ∑ y : E × E × P, T y.2.2 y.2.1 y.1 := by
    simp [Fintype.sum_prod_type]
  rw [h1, h2]
  exact Fintype.sum_equiv swap3 _ _ (fun _ => rfl)

/-- `⟨Bx, Bx⟩ = ⟨x, Bᴴ B x⟩`. -/
theorem inner_shift (B : E → P → ℂ) (x : P → ℂ) :
    ∑ e, applyB B x e * (starRingEnd ℂ) (applyB B x e)
      = ∑ p, x p * (starRingEnd ℂ) (applyBstar B (applyB B x) p) := by
  have hL : ∑ e, applyB B x e * (starRingEnd ℂ) (applyB B x e)
      = ∑ e, ∑ p₁, ∑ p₂,
          (B e p₁ * x p₁) * ((starRingEnd ℂ) (B e p₂) * (starRingEnd ℂ) (x p₂)) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [applyB, map_sum, map_mul]
    rw [Finset.sum_mul_sum]
  have hR : ∑ p, x p * (starRingEnd ℂ) (applyBstar B (applyB B x) p)
      = ∑ p₁, ∑ e, ∑ p₂,
          (B e p₁ * x p₁) * ((starRingEnd ℂ) (B e p₂) * (starRingEnd ℂ) (x p₂)) := by
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    simp only [applyBstar, applyB, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun p₂ _ => by ring
  rw [hL, hR, Finset.sum_comm]

/-- `⟨Bᴴv, Bᴴv⟩ = ⟨H v, v⟩`. -/
theorem inner_star (B : E → P → ℂ) (v : E → ℂ) :
    ∑ p, applyBstar B v p * (starRingEnd ℂ) (applyBstar B v p)
      = ∑ f, applyH B v f * (starRingEnd ℂ) (v f) := by
  have hL : ∑ p, applyBstar B v p * (starRingEnd ℂ) (applyBstar B v p)
      = ∑ p, ∑ e, ∑ f,
          ((starRingEnd ℂ) (B e p) * v e) * (B f p * (starRingEnd ℂ) (v f)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [applyBstar, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_mul_sum]
  have hR : ∑ f, applyH B v f * (starRingEnd ℂ) (v f)
      = ∑ f, ∑ e, ∑ p,
          ((starRingEnd ℂ) (B e p) * v e) * (B f p * (starRingEnd ℂ) (v f)) := by
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [applyH, rowGram, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun p _ => by ring
  rw [hL, hR]
  exact sum3_comm _

private theorem nsq_eq_norm_inner {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ((nsq f : ℝ) : ℂ) = ∑ i, f i * (starRingEnd ℂ) (f i) := by
  simp only [nsq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj]
  norm_cast
  exact (Complex.normSq_eq_norm_sq _).symm

/-- Step 1: `‖Bx‖⁴ ≤ ‖x‖² ‖Bᴴ B x‖²`. -/
theorem step_one (B : E → P → ℂ) (x : P → ℂ) :
    (nsq (applyB B x)) ^ 2 ≤ nsq x * nsq (applyBstar B (applyB B x)) := by
  have h : ((nsq (applyB B x) : ℝ) : ℂ)
      = ∑ p, x p * (starRingEnd ℂ) (applyBstar B (applyB B x) p) := by
    rw [nsq_eq_norm_inner]; exact inner_shift B x
  have h2 : nsq (applyB B x)
      = ‖∑ p, x p * (starRingEnd ℂ) (applyBstar B (applyB B x) p)‖ := by
    rw [← h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nsq_nonneg _)]
  rw [h2]
  exact cs_sq _ _

/-- Step 2: `‖Bᴴ v‖⁴ ≤ ‖H v‖² ‖v‖²`. -/
theorem step_two (B : E → P → ℂ) (v : E → ℂ) :
    (nsq (applyBstar B v)) ^ 2 ≤ nsq (applyH B v) * nsq v := by
  have h : ((nsq (applyBstar B v) : ℝ) : ℂ)
      = ∑ f, applyH B v f * (starRingEnd ℂ) (v f) := by
    rw [nsq_eq_norm_inner]; exact inner_star B v
  have h2 : nsq (applyBstar B v) = ‖∑ f, applyH B v f * (starRingEnd ℂ) (v f)‖ := by
    rw [← h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nsq_nonneg _)]
  rw [h2]
  exact cs_sq _ _

/-- Step 3: `‖H v‖² ≤ tr(H²) ‖v‖²`. -/
theorem step_three (B : E → P → ℂ) (v : E → ℂ) :
    nsq (applyH B v) ≤ fourthMoment B * nsq v := by
  have hterm : ∀ f : E, ‖applyH B v f‖ ^ 2 ≤ (∑ e, ‖rowGram B f e‖ ^ 2) * nsq v := by
    intro f
    have : applyH B v f
        = ∑ e, rowGram B f e * (starRingEnd ℂ) ((starRingEnd ℂ) (v e)) := by
      simp [applyH]
    rw [this]
    calc ‖∑ e, rowGram B f e * (starRingEnd ℂ) ((starRingEnd ℂ) (v e))‖ ^ 2
        ≤ nsq (fun e => rowGram B f e) * nsq (fun e => (starRingEnd ℂ) (v e)) :=
          cs_sq _ _
      _ = (∑ e, ‖rowGram B f e‖ ^ 2) * nsq v := by rw [nsq_conj]; rfl
  calc nsq (applyH B v) = ∑ f, ‖applyH B v f‖ ^ 2 := rfl
    _ ≤ ∑ f, (∑ e, ‖rowGram B f e‖ ^ 2) * nsq v :=
        Finset.sum_le_sum fun f _ => hterm f
    _ = (∑ f, ∑ e, ‖rowGram B f e‖ ^ 2) * nsq v := by rw [Finset.sum_mul]
    _ = fourthMoment B * nsq v := by
        rw [fourthMoment, Finset.sum_comm]

/-- The finite R4C hypothesis: `tr((B Bᴴ)²) ≤ T²`. -/
def R4CBound (B : E → P → ℂ) (T : ℝ) : Prop := fourthMoment B ≤ T ^ 2

/-- The squared-operator-norm bound in explicit finite form. -/
def OpNormSqBound (B : E → P → ℂ) (c : ℝ) : Prop :=
  ∀ x : P → ℂ, nsq (applyB B x) ≤ c * nsq x

/-- **R4C ⇒ test-vector bound.**  If `tr((B Bᴴ)²) ≤ T²` with `T ≥ 0` then
`∑_e |∑_p B e p x p|² ≤ T ∑_p |x p|²` for every `x`. -/
theorem r4c_implies_testVector_bound {B : E → P → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hR : R4CBound B T) (x : P → ℂ) : nsq (applyB B x) ≤ T * nsq x := by
  set V := nsq (applyB B x) with hV
  set W := nsq (applyBstar B (applyB B x)) with hW
  set Xn := nsq x with hXn
  have hV0 : 0 ≤ V := nsq_nonneg _
  have hW0 : 0 ≤ W := nsq_nonneg _
  have hX0 : 0 ≤ Xn := nsq_nonneg _
  have h1 : V ^ 2 ≤ Xn * W := step_one B x
  have h2 : W ^ 2 ≤ nsq (applyH B (applyB B x)) * V := step_two B (applyB B x)
  have h3 : nsq (applyH B (applyB B x)) ≤ fourthMoment B * V := step_three B (applyB B x)
  have hF0 : 0 ≤ fourthMoment B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 : W ^ 2 ≤ fourthMoment B * V ^ 2 := by
    calc W ^ 2 ≤ nsq (applyH B (applyB B x)) * V := h2
      _ ≤ (fourthMoment B * V) * V := by
          exact mul_le_mul_of_nonneg_right h3 hV0
      _ = fourthMoment B * V ^ 2 := by ring
  -- combine: V⁴ ≤ Xn² W² ≤ Xn² T² V²
  have h5 : V ^ 4 ≤ Xn ^ 2 * (fourthMoment B * V ^ 2) := by
    have hsq : (V ^ 2) ^ 2 ≤ (Xn * W) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) h1 2
    calc V ^ 4 = (V ^ 2) ^ 2 := by ring
      _ ≤ (Xn * W) ^ 2 := hsq
      _ = Xn ^ 2 * W ^ 2 := by ring
      _ ≤ Xn ^ 2 * (fourthMoment B * V ^ 2) := by
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : V ^ 4 ≤ (T * Xn) ^ 2 * V ^ 2 := by
    calc V ^ 4 ≤ Xn ^ 2 * (fourthMoment B * V ^ 2) := h5
      _ ≤ Xn ^ 2 * (T ^ 2 * V ^ 2) := by
          have : fourthMoment B * V ^ 2 ≤ T ^ 2 * V ^ 2 :=
            mul_le_mul_of_nonneg_right hR (by positivity)
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = (T * Xn) ^ 2 * V ^ 2 := by ring
  rcases eq_or_lt_of_le hV0 with hV0' | hVpos
  · rw [← hV0']
    positivity
  · have hpos : (0 : ℝ) < V ^ 2 := by positivity
    have h7 : V ^ 2 ≤ (T * Xn) ^ 2 :=
      le_of_mul_le_mul_right (by
        calc V ^ 2 * V ^ 2 = V ^ 4 := by ring
          _ ≤ (T * Xn) ^ 2 * V ^ 2 := h6) hpos
    have h8 : V ≤ T * Xn := (sq_le_sq₀ hV0 (by positivity)).mp h7
    linarith [h8]

/-- **R4C ⇒ operator bound.**  `T` dominates the squared operator norm of `B`. -/
theorem r4c_implies_operator_bound {B : E → P → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hR : R4CBound B T) : OpNormSqBound B T :=
  fun x => r4c_implies_testVector_bound hT hR x

/-- **R4C at scale `T = M D L` applied to a test vector of mass `L`.** -/
theorem r4c_implies_MDL2_bound {B : E → P → ℂ} {M D L : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hR : R4CBound B (M * D * L)) {b : P → ℂ} (hb : nsq b ≤ L) :
    nsq (applyB B b) ≤ M * D * L ^ 2 := by
  have hT : 0 ≤ M * D * L := by positivity
  have h := r4c_implies_testVector_bound hT hR b
  calc nsq (applyB B b) ≤ (M * D * L) * nsq b := h
    _ ≤ (M * D * L) * L := by exact mul_le_mul_of_nonneg_left hb hT
    _ = M * D * L ^ 2 := by ring

/-- With `D H = L²` and `H ≠ 0`, the scale `M D L²` equals `M L⁴ / H`. -/
theorem MDL2_eq_ML4_div_H {M D L H : ℝ} (hH : H ≠ 0) (hDH : D * H = L ^ 2) :
    M * D * L ^ 2 = M * L ^ 4 / H := by
  field_simp
  linear_combination (M * L ^ 2) * hDH

/-- **Average covariance scale.**  Combination of the previous two statements. -/
theorem r4c_implies_avgCov_scale {B : E → P → ℂ} {M D L H : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hL : 0 ≤ L) (hH : H ≠ 0) (hDH : D * H = L ^ 2)
    (hR : R4CBound B (M * D * L)) {b : P → ℂ} (hb : nsq b ≤ L) :
    nsq (applyB B b) ≤ M * L ^ 4 / H := by
  rw [← MDL2_eq_ML4_div_H (M := M) hH hDH]
  exact r4c_implies_MDL2_bound hM hD hL hR hb

/-- `(M D L)² = M² L⁶ / H²` under `D H = L²`. -/
theorem MDL_sq_eq {M D L H : ℝ} (hH : H ≠ 0) (hDH : D * H = L ^ 2) :
    (M * D * L) ^ 2 = M ^ 2 * L ^ 6 / H ^ 2 := by
  field_simp
  linear_combination (M ^ 2 * L ^ 2 * (D * H + L ^ 2)) * hDH

end Gate04Root
