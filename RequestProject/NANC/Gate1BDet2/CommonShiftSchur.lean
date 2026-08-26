import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 23: the abstract bipartite Schur bound

A completely general finite lemma, with no arithmetic content: a bounded weight
supported on a finite bipartite edge set `E ⊆ A × B` whose left degrees are at
most `Dₐ` and whose right degrees are at most `D_b` gives

  `|∑_{(a,b) ∈ E} w(a,b) xₐ y_b|² ≤ Dₐ D_b (∑ₐ |xₐ|²)(∑_b |y_b|²)`.

The squared form is the primary statement (it is the cheaper one to state and
use); the square-root form is derived from it.

This is the coefficient-blind estimate whose exponent bookkeeping is banked in
`SplitSchurExponentLedger`.  It is *not* an arithmetic input: the degree bounds
must be supplied from outside (in the intended application, by the common-shift
rigidity of `CommonShiftRigidity`).
-/

namespace TwinPrimeProject
namespace Gate1BDet2

open Finset

variable {A B : Type*}

/-! ## 1. Degree-weighted rearrangement -/

/-- Summing a function of the left endpoint over the edge set weights each
vertex by its degree. -/
theorem sum_edge_left_eq_degree_weighted [DecidableEq A] (E : Finset (A × B)) (sA : Finset A)
    (hEA : ∀ p ∈ E, p.1 ∈ sA) (F : A → ℝ) :
    ∑ p ∈ E, F p.1 = ∑ a ∈ sA, ((E.filter (fun p => p.1 = a)).card : ℝ) * F a := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : A × B => p.1) (t := sA) hEA
    (f := fun p : A × B => F p.1)]
  refine Finset.sum_congr rfl ?_
  intro a _
  have : ∀ p ∈ E.filter (fun p : A × B => p.1 = a), F p.1 = F a := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

/-- Summing a function of the right endpoint over the edge set weights each
vertex by its degree. -/
theorem sum_edge_right_eq_degree_weighted [DecidableEq B] (E : Finset (A × B)) (sB : Finset B)
    (hEB : ∀ p ∈ E, p.2 ∈ sB) (G : B → ℝ) :
    ∑ p ∈ E, G p.2 = ∑ b ∈ sB, ((E.filter (fun p => p.2 = b)).card : ℝ) * G b := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : A × B => p.2) (t := sB) hEB
    (f := fun p : A × B => G p.2)]
  refine Finset.sum_congr rfl ?_
  intro b _
  have : ∀ p ∈ E.filter (fun p : A × B => p.2 = b), G p.2 = G b := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

/-- Left-degree bound in `ℓ²` form. -/
theorem sum_edge_left_sq_le [DecidableEq A] (E : Finset (A × B)) (sA : Finset A) (DA : ℕ)
    (hEA : ∀ p ∈ E, p.1 ∈ sA)
    (hdegA : ∀ a, (E.filter (fun p => p.1 = a)).card ≤ DA) (x : A → ℂ) :
    ∑ p ∈ E, ‖x p.1‖ ^ 2 ≤ (DA : ℝ) * ∑ a ∈ sA, ‖x a‖ ^ 2 := by
  classical
  rw [sum_edge_left_eq_degree_weighted E sA hEA (fun a => ‖x a‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro a _
  have h1 : ((E.filter (fun p : A × B => p.1 = a)).card : ℝ) ≤ (DA : ℝ) := by
    exact_mod_cast hdegA a
  have h2 : (0 : ℝ) ≤ ‖x a‖ ^ 2 := sq_nonneg _
  exact mul_le_mul_of_nonneg_right h1 h2

/-- Right-degree bound in `ℓ²` form. -/
theorem sum_edge_right_sq_le [DecidableEq B] (E : Finset (A × B)) (sB : Finset B) (DB : ℕ)
    (hEB : ∀ p ∈ E, p.2 ∈ sB)
    (hdegB : ∀ b, (E.filter (fun p => p.2 = b)).card ≤ DB) (y : B → ℂ) :
    ∑ p ∈ E, ‖y p.2‖ ^ 2 ≤ (DB : ℝ) * ∑ b ∈ sB, ‖y b‖ ^ 2 := by
  classical
  rw [sum_edge_right_eq_degree_weighted E sB hEB (fun b => ‖y b‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro b _
  have h1 : ((E.filter (fun p : A × B => p.2 = b)).card : ℝ) ≤ (DB : ℝ) := by
    exact_mod_cast hdegB b
  have h2 : (0 : ℝ) ≤ ‖y b‖ ^ 2 := sq_nonneg _
  exact mul_le_mul_of_nonneg_right h1 h2

/-! ## 2. The bipartite Schur bound -/

/-- **`bipartite_schur_bound` (squared form).**  For a bounded weight on a finite
bipartite edge set with left degrees `≤ Dₐ` and right degrees `≤ D_b`,

  `|∑_{(a,b) ∈ E} w(a,b) xₐ y_b|² ≤ Dₐ D_b (∑ₐ|xₐ|²)(∑_b|y_b|²)`.

Two Cauchy–Schwarz-type steps: the triangle inequality followed by the discrete
Cauchy–Schwarz inequality on the edge set, then the degree rearrangement. -/
theorem bipartite_schur_bound_sq [DecidableEq A] [DecidableEq B] (E : Finset (A × B)) (sA : Finset A) (sB : Finset B)
    (w : A → B → ℂ) (x : A → ℂ) (y : B → ℂ) (DA DB : ℕ)
    (hw : ∀ p ∈ E, ‖w p.1 p.2‖ ≤ 1)
    (hEA : ∀ p ∈ E, p.1 ∈ sA) (hEB : ∀ p ∈ E, p.2 ∈ sB)
    (hdegA : ∀ a, (E.filter (fun p => p.1 = a)).card ≤ DA)
    (hdegB : ∀ b, (E.filter (fun p => p.2 = b)).card ≤ DB) :
    ‖∑ p ∈ E, w p.1 p.2 * x p.1 * y p.2‖ ^ 2
      ≤ (DA : ℝ) * (DB : ℝ) * (∑ a ∈ sA, ‖x a‖ ^ 2) * (∑ b ∈ sB, ‖y b‖ ^ 2) := by
  classical
  -- Step 1: triangle inequality and `‖w‖ ≤ 1`
  have step1 : ‖∑ p ∈ E, w p.1 p.2 * x p.1 * y p.2‖ ≤ ∑ p ∈ E, ‖x p.1‖ * ‖y p.2‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro p hp
    have : ‖w p.1 p.2 * x p.1 * y p.2‖ = ‖w p.1 p.2‖ * ‖x p.1‖ * ‖y p.2‖ := by
      rw [norm_mul, norm_mul]
    rw [this]
    have h1 : ‖w p.1 p.2‖ * ‖x p.1‖ ≤ 1 * ‖x p.1‖ :=
      mul_le_mul_of_nonneg_right (hw p hp) (norm_nonneg _)
    have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (y p.2))
    simpa using this
  -- Step 2: Cauchy–Schwarz on the edge set
  have step2 : (∑ p ∈ E, ‖x p.1‖ * ‖y p.2‖) ^ 2
      ≤ (∑ p ∈ E, ‖x p.1‖ ^ 2) * (∑ p ∈ E, ‖y p.2‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq E (fun p => ‖x p.1‖) (fun p => ‖y p.2‖)
  -- Step 3: degree rearrangement
  have step3 : (∑ p ∈ E, ‖x p.1‖ ^ 2) * (∑ p ∈ E, ‖y p.2‖ ^ 2)
      ≤ ((DA : ℝ) * ∑ a ∈ sA, ‖x a‖ ^ 2) * ((DB : ℝ) * ∑ b ∈ sB, ‖y b‖ ^ 2) := by
    have hA := sum_edge_left_sq_le E sA DA hEA hdegA x
    have hB := sum_edge_right_sq_le E sB DB hEB hdegB y
    have hA0 : (0 : ℝ) ≤ ∑ p ∈ E, ‖x p.1‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hB0 : (0 : ℝ) ≤ ∑ p ∈ E, ‖y p.2‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hBpos : (0 : ℝ) ≤ (DB : ℝ) * ∑ b ∈ sB, ‖y b‖ ^ 2 := le_trans hB0 hB
    calc (∑ p ∈ E, ‖x p.1‖ ^ 2) * (∑ p ∈ E, ‖y p.2‖ ^ 2)
        ≤ ((DA : ℝ) * ∑ a ∈ sA, ‖x a‖ ^ 2) * (∑ p ∈ E, ‖y p.2‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hA hB0
      _ ≤ ((DA : ℝ) * ∑ a ∈ sA, ‖x a‖ ^ 2) * ((DB : ℝ) * ∑ b ∈ sB, ‖y b‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left hB ?_
          exact le_trans hA0 hA
  have hsum0 : (0 : ℝ) ≤ ∑ p ∈ E, ‖x p.1‖ * ‖y p.2‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖∑ p ∈ E, w p.1 p.2 * x p.1 * y p.2‖ ^ 2
      ≤ (∑ p ∈ E, ‖x p.1‖ * ‖y p.2‖) ^ 2 := by
        gcongr
    _ ≤ (∑ p ∈ E, ‖x p.1‖ ^ 2) * (∑ p ∈ E, ‖y p.2‖ ^ 2) := step2
    _ ≤ ((DA : ℝ) * ∑ a ∈ sA, ‖x a‖ ^ 2) * ((DB : ℝ) * ∑ b ∈ sB, ‖y b‖ ^ 2) := step3
    _ = (DA : ℝ) * (DB : ℝ) * (∑ a ∈ sA, ‖x a‖ ^ 2) * (∑ b ∈ sB, ‖y b‖ ^ 2) := by ring

/-- **`bipartite_schur_bound` (square-root form).**  The same estimate written
with `Real.sqrt`. -/
theorem bipartite_schur_bound [DecidableEq A] [DecidableEq B] (E : Finset (A × B)) (sA : Finset A) (sB : Finset B)
    (w : A → B → ℂ) (x : A → ℂ) (y : B → ℂ) (DA DB : ℕ)
    (hw : ∀ p ∈ E, ‖w p.1 p.2‖ ≤ 1)
    (hEA : ∀ p ∈ E, p.1 ∈ sA) (hEB : ∀ p ∈ E, p.2 ∈ sB)
    (hdegA : ∀ a, (E.filter (fun p => p.1 = a)).card ≤ DA)
    (hdegB : ∀ b, (E.filter (fun p => p.2 = b)).card ≤ DB) :
    ‖∑ p ∈ E, w p.1 p.2 * x p.1 * y p.2‖
      ≤ Real.sqrt ((DA : ℝ) * (DB : ℝ)) *
          Real.sqrt (∑ a ∈ sA, ‖x a‖ ^ 2) * Real.sqrt (∑ b ∈ sB, ‖y b‖ ^ 2) := by
  have hsq := bipartite_schur_bound_sq E sA sB w x y DA DB hw hEA hEB hdegA hdegB
  have hA0 : (0 : ℝ) ≤ ∑ a ∈ sA, ‖x a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : (0 : ℝ) ≤ ∑ b ∈ sB, ‖y b‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD0 : (0 : ℝ) ≤ (DA : ℝ) * (DB : ℝ) := by positivity
  set SA : ℝ := ∑ a ∈ sA, ‖x a‖ ^ 2 with hSA
  set SB : ℝ := ∑ b ∈ sB, ‖y b‖ ^ 2 with hSB
  have hrhs : Real.sqrt (((DA : ℝ) * (DB : ℝ)) * SA * SB)
      = Real.sqrt ((DA : ℝ) * (DB : ℝ)) * Real.sqrt SA * Real.sqrt SB := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((DA : ℝ) * (DB : ℝ)) * SA),
      Real.sqrt_mul hD0]
  rw [← hrhs]
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

end Gate1BDet2
end TwinPrimeProject
