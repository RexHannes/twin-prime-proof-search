import Mathlib

/-!
# Route-A fibre frame: the finite Gram / fourth-moment inequality

Let `J`, `T` be finite index types and `x y : J → T → ℂ`.  Put

`G j j' = ∑ t, x j t * conj (y j' t)`,  `Q x = ∑ j j', |∑ t, x j t * conj (x j' t)|²`.

We prove the finite Cauchy–Schwarz inequality (Gram4)

`∑ j j', |G j j'|² ≤ (Q x)^(1/2) * (Q y)^(1/2)`,

together with its square-root-free form

`(∑ j j', |G j j'|²)² ≤ Q x * Q y`.

Everything is a finite algebraic identity plus one application of the discrete
Cauchy–Schwarz inequality; nothing analytic is used.
-/

namespace RouteAFibreFrame

open Finset Complex

variable {J T : Type*} [Fintype J] [Fintype T]

/-- The cross Gram matrix `G j j' = ∑ t, x j t * conj (y j' t)`. -/
noncomputable def gram (x y : J → T → ℂ) (j j' : J) : ℂ :=
  ∑ t : T, x j t * (starRingEnd ℂ) (y j' t)

/-- The `T × T` correlation matrix `P x t t' = ∑ j, x j t * conj (x j t')`. -/
noncomputable def corr (x : J → T → ℂ) (t t' : T) : ℂ :=
  ∑ j : J, x j t * (starRingEnd ℂ) (x j t')

/-- The fourth-moment functional `Q x = ∑ j j', |∑ t, x j t * conj (x j' t)|²`. -/
noncomputable def gramFourth (x : J → T → ℂ) : ℝ :=
  ∑ j : J, ∑ j' : J, ‖gram x x j j'‖ ^ 2

/-- The cross fourth moment `∑ j j', |G j j'|²`. -/
noncomputable def crossFourth (x y : J → T → ℂ) : ℝ :=
  ∑ j : J, ∑ j' : J, ‖gram x y j j'‖ ^ 2

private theorem norm_sq_cast (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.sq_norm, Complex.mul_conj]

theorem crossFourth_nonneg (x y : J → T → ℂ) : 0 ≤ crossFourth x y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem gramFourth_nonneg (x : J → T → ℂ) : 0 ≤ gramFourth x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- Reordering of a fourfold finite sum. -/
theorem sum_swap_four (f : J → J → T → T → ℂ) :
    ∑ j : J, ∑ j' : J, ∑ t : T, ∑ t' : T, f j j' t t'
      = ∑ t : T, ∑ t' : T, ∑ j : J, ∑ j' : J, f j j' t t' := by
  have h1 : (∑ j : J, ∑ j' : J, ∑ t : T, ∑ t' : T, f j j' t t')
      = ∑ p : J × J, ∑ q : T × T, f p.1 p.2 q.1 q.2 := by
    simp [Fintype.sum_prod_type]
  have h2 : (∑ t : T, ∑ t' : T, ∑ j : J, ∑ j' : J, f j j' t t')
      = ∑ q : T × T, ∑ p : J × J, f p.1 p.2 q.1 q.2 := by
    simp [Fintype.sum_prod_type]
  rw [h1, h2, Finset.sum_comm]

/-- Key expansion: the `J`-side cross fourth moment equals the `T`-side pairing
of the two correlation matrices. -/
theorem crossFourth_eq_corr_pairing (x y : J → T → ℂ) :
    (crossFourth x y : ℂ) =
      ∑ t : T, ∑ t' : T, corr x t t' * (starRingEnd ℂ) (corr y t t') := by
  have hL : ((crossFourth x y : ℝ) : ℂ)
      = ∑ j : J, ∑ j' : J, ∑ t : T, ∑ t' : T,
          (x j t * (starRingEnd ℂ) (y j' t)) * ((starRingEnd ℂ) (x j t') * y j' t') := by
    rw [crossFourth]
    push_cast
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [show ((‖gram x y j j'‖ : ℝ) : ℂ) ^ 2 = ((‖gram x y j j'‖ ^ 2 : ℝ) : ℂ) by
        push_cast; ring, norm_sq_cast]
    simp only [gram, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hR : (∑ t : T, ∑ t' : T, corr x t t' * (starRingEnd ℂ) (corr y t t'))
      = ∑ t : T, ∑ t' : T, ∑ j : J, ∑ j' : J,
          (x j t * (starRingEnd ℂ) (y j' t)) * ((starRingEnd ℂ) (x j t') * y j' t') := by
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    simp only [corr, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [hL, hR, sum_swap_four]

/-- Specialisation to `y = x`: the fourth-moment functional is the squared
Frobenius norm of the correlation matrix. -/
theorem gramFourth_eq_corr_sq (x : J → T → ℂ) :
    gramFourth x = ∑ t : T, ∑ t' : T, ‖corr x t t'‖ ^ 2 := by
  have h := crossFourth_eq_corr_pairing x x
  have hcast : ((gramFourth x : ℝ) : ℂ) =
      ((∑ t : T, ∑ t' : T, ‖corr x t t'‖ ^ 2 : ℝ) : ℂ) := by
    rw [show (gramFourth x : ℝ) = crossFourth x x from rfl, h]
    push_cast
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    rw [show ((‖corr x t t'‖ : ℝ) : ℂ) ^ 2 = ((‖corr x t t'‖ ^ 2 : ℝ) : ℂ) by
        push_cast; ring, norm_sq_cast]
  exact_mod_cast hcast

/-- The cross fourth moment is bounded by the pointwise `T × T` pairing of the
correlation matrices. -/
theorem crossFourth_le_pairing (x y : J → T → ℂ) :
    crossFourth x y ≤ ∑ t : T, ∑ t' : T, ‖corr x t t'‖ * ‖corr y t t'‖ := by
  have h := crossFourth_eq_corr_pairing x y
  have h1 : crossFourth x y = ‖((crossFourth x y : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (crossFourth_nonneg x y)]
  rw [h1, h]
  calc ‖∑ t : T, ∑ t' : T, corr x t t' * (starRingEnd ℂ) (corr y t t')‖
      ≤ ∑ t : T, ‖∑ t' : T, corr x t t' * (starRingEnd ℂ) (corr y t t')‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t : T, ∑ t' : T, ‖corr x t t' * (starRingEnd ℂ) (corr y t t')‖ :=
        Finset.sum_le_sum fun t _ => norm_sum_le _ _
    _ = ∑ t : T, ∑ t' : T, ‖corr x t t'‖ * ‖corr y t t'‖ := by
        simp

/-- **(Gram4), squared form.**  `(∑ j j', |G j j'|²)² ≤ Q x * Q y`. -/
theorem finite_gram_fourth_moment_sq (x y : J → T → ℂ) :
    (crossFourth x y) ^ 2 ≤ gramFourth x * gramFourth y := by
  have hCS :
      (∑ t : T, ∑ t' : T, ‖corr x t t'‖ * ‖corr y t t'‖) ^ 2 ≤
        (∑ t : T, ∑ t' : T, ‖corr x t t'‖ ^ 2) *
          (∑ t : T, ∑ t' : T, ‖corr y t t'‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      ((Finset.univ : Finset T) ×ˢ (Finset.univ : Finset T))
      (fun p : T × T => ‖corr x p.1 p.2‖) (fun p : T × T => ‖corr y p.1 p.2‖)
    rw [Finset.sum_product, Finset.sum_product, Finset.sum_product] at h
    exact h
  calc (crossFourth x y) ^ 2
      ≤ (∑ t : T, ∑ t' : T, ‖corr x t t'‖ * ‖corr y t t'‖) ^ 2 :=
        pow_le_pow_left₀ (crossFourth_nonneg x y) (crossFourth_le_pairing x y) 2
    _ ≤ (∑ t : T, ∑ t' : T, ‖corr x t t'‖ ^ 2) *
          (∑ t : T, ∑ t' : T, ‖corr y t t'‖ ^ 2) := hCS
    _ = gramFourth x * gramFourth y := by
        rw [gramFourth_eq_corr_sq, gramFourth_eq_corr_sq]

/-- **(Gram4).**  `∑ j j', |G j j'|² ≤ (Q x)^(1/2) (Q y)^(1/2)`. -/
theorem finite_gram_fourth_moment_cauchy (x y : J → T → ℂ) :
    crossFourth x y ≤ Real.sqrt (gramFourth x) * Real.sqrt (gramFourth y) := by
  have hsq := finite_gram_fourth_moment_sq x y
  have h : crossFourth x y ≤ Real.sqrt (gramFourth x * gramFourth y) := by
    rw [show crossFourth x y = Real.sqrt ((crossFourth x y) ^ 2) by
      rw [Real.sqrt_sq (crossFourth_nonneg x y)]]
    exact Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_mul (gramFourth_nonneg x)] at h

end RouteAFibreFrame
