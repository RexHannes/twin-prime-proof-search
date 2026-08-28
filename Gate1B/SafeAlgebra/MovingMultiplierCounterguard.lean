/-
# Gate 1B v12 — family-lift counterguard: exact ℓ² duality on a finite index set

**Status: PROVED_ALGEBRAIC (finite Hilbert-space algebra only).**

Let `Theta` be a finite index type and `B : Theta → ℂ` an arbitrary vector.
We prove the exact duality

    sup { ‖∑_Θ A Θ * B Θ‖ : ∑_Θ ‖A Θ‖² ≤ 1 }  =  ‖B‖₂,

as an `IsGreatest` statement: the supremum is *attained*, by the explicit
saturating vector `conj B / ‖B‖₂` (and by `0` when `B = 0`).

The counterguard consequence recorded here is:

    a fixed pointwise multiplier bound together with ℓ²-multiplier data
    does **not**, by finite Hilbert-space algebra alone, produce any
    moving-family norm smaller than `‖B‖₂`.

The hypothetical saving factor is carried only as an abstract scalar
parameter `c`; no numerical saving is asserted anywhere.

Contents:

* `l2Norm` — the ℓ² norm of a finite vector;
* `pairing_norm_le` — the Cauchy–Schwarz upper bound;
* `exists_saturating_multiplier` — the explicit saturating vector;
* `movingFamily_l2_duality` — `IsGreatest` form;
* `fixedMultiplierSaving_not_familyLift_by_l2_alone` — the counterguard.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

variable {Theta : Type*} [Fintype Theta]

/-- The ℓ² norm of a finite complex vector. -/
noncomputable def l2Norm (B : Theta → ℂ) : ℝ := Real.sqrt (∑ t : Theta, ‖B t‖ ^ 2)

theorem l2Norm_nonneg (B : Theta → ℂ) : 0 ≤ l2Norm B := Real.sqrt_nonneg _

theorem l2Norm_sq (B : Theta → ℂ) : l2Norm B ^ 2 = ∑ t : Theta, ‖B t‖ ^ 2 := by
  unfold l2Norm
  exact Real.sq_sqrt (Finset.sum_nonneg fun t _ => sq_nonneg _)

/-- **Cauchy–Schwarz upper bound** for the ℓ²-constrained pairing. -/
theorem pairing_norm_le (A B : Theta → ℂ) (hA : ∑ t : Theta, ‖A t‖ ^ 2 ≤ 1) :
    ‖∑ t : Theta, A t * B t‖ ≤ l2Norm B := by
  have h1 : ‖∑ t : Theta, A t * B t‖ ≤ ∑ t : Theta, ‖A t‖ * ‖B t‖ := by
    refine (norm_sum_le _ _).trans_eq ?_
    exact Finset.sum_congr rfl fun t _ => norm_mul _ _
  have h2 : ∑ t : Theta, ‖A t‖ * ‖B t‖
      ≤ Real.sqrt (∑ t : Theta, ‖A t‖ ^ 2) * Real.sqrt (∑ t : Theta, ‖B t‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h3 : Real.sqrt (∑ t : Theta, ‖A t‖ ^ 2) ≤ 1 := by
    have := Real.sqrt_le_sqrt hA
    simpa using this
  refine h1.trans (h2.trans ?_)
  have hnn : (0 : ℝ) ≤ Real.sqrt (∑ t : Theta, ‖B t‖ ^ 2) := Real.sqrt_nonneg _
  calc Real.sqrt (∑ t : Theta, ‖A t‖ ^ 2) * Real.sqrt (∑ t : Theta, ‖B t‖ ^ 2)
      ≤ 1 * Real.sqrt (∑ t : Theta, ‖B t‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_right h3 hnn
    _ = l2Norm B := by rw [one_mul]; rfl

/-- **The bound is attained**: an explicit ℓ²-normalised multiplier saturates the
pairing.  For `B ≠ 0` it is `conj B / ‖B‖₂`. -/
theorem exists_saturating_multiplier (B : Theta → ℂ) :
    ∃ A : Theta → ℂ, (∑ t : Theta, ‖A t‖ ^ 2) ≤ 1 ∧ ‖∑ t : Theta, A t * B t‖ = l2Norm B := by
  classical
  by_cases hB : l2Norm B = 0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · simp
    · simp [hB]
  · have hpos : 0 < l2Norm B := lt_of_le_of_ne (l2Norm_nonneg B) (Ne.symm hB)
    refine ⟨fun t => (starRingEnd ℂ) (B t) / (l2Norm B : ℂ), ?_, ?_⟩
    · have hcast : ((l2Norm B : ℂ)) ≠ 0 := by
        exact_mod_cast (by exact_mod_cast hB : (l2Norm B : ℝ) ≠ 0)
      have hnorm : ∀ t : Theta, ‖(starRingEnd ℂ) (B t) / (l2Norm B : ℂ)‖ ^ 2
          = ‖B t‖ ^ 2 / l2Norm B ^ 2 := by
        intro t
        rw [norm_div, RCLike.norm_conj]
        rw [div_pow]
        congr 1
        simp [abs_of_nonneg (l2Norm_nonneg B)]
      rw [Finset.sum_congr rfl fun t _ => hnorm t, ← Finset.sum_div, ← l2Norm_sq B]
      exact le_of_eq (div_self (by positivity))
    · have hcast : ((l2Norm B : ℂ)) ≠ 0 := by
        simpa using (by exact_mod_cast hB : (l2Norm B : ℝ) ≠ 0)
      have hterm : ∀ t : Theta, (starRingEnd ℂ) (B t) / (l2Norm B : ℂ) * B t
          = ((‖B t‖ ^ 2 : ℝ) : ℂ) / (l2Norm B : ℂ) := by
        intro t
        rw [div_mul_eq_mul_div]
        congr 1
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div]
      have : (∑ t : Theta, ((‖B t‖ ^ 2 : ℝ) : ℂ)) = ((l2Norm B ^ 2 : ℝ) : ℂ) := by
        rw [l2Norm_sq B]; push_cast; ring
      rw [this]
      rw [show ((l2Norm B ^ 2 : ℝ) : ℂ) = (l2Norm B : ℂ) * (l2Norm B : ℂ) by push_cast; ring]
      rw [mul_div_assoc, div_self hcast, mul_one]
      simp [abs_of_nonneg (l2Norm_nonneg B)]

/-- **Exact ℓ² duality for a moving multiplier family**: the constrained pairing
supremum equals `‖B‖₂` and is attained. -/
theorem movingFamily_l2_duality (B : Theta → ℂ) :
    IsGreatest {r : ℝ | ∃ A : Theta → ℂ,
      (∑ t : Theta, ‖A t‖ ^ 2) ≤ 1 ∧ r = ‖∑ t : Theta, A t * B t‖} (l2Norm B) := by
  obtain ⟨A, hA, hAeq⟩ := exists_saturating_multiplier B
  constructor
  · exact ⟨A, hA, hAeq.symm⟩
  · rintro r ⟨A', hA', rfl⟩
    exact pairing_norm_le A' B hA'

/-- **Counterguard B (family lift).**  No factor strictly smaller than `1` can be
inserted in front of `‖B‖₂` on the strength of ℓ² multiplier data alone: the
duality bound is attained.  The hypothetical saving is carried purely as the
abstract scalar `c`; no concrete saving exponent occurs in the statement. -/
theorem fixedMultiplierSaving_not_familyLift_by_l2_alone
    (B : Theta → ℂ) (hB : 0 < l2Norm B) (c : ℝ) (hc : c < 1) :
    ∃ A : Theta → ℂ, (∑ t : Theta, ‖A t‖ ^ 2) ≤ 1 ∧
      c * l2Norm B < ‖∑ t : Theta, A t * B t‖ := by
  obtain ⟨A, hA, hAeq⟩ := exists_saturating_multiplier B
  refine ⟨A, hA, ?_⟩
  rw [hAeq]
  calc c * l2Norm B < 1 * l2Norm B := by
        exact (mul_lt_mul_of_pos_right hc hB)
    _ = l2Norm B := one_mul _

end Gate1B.SafeAlgebra
