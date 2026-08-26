/-
# Gate 1B safe extension — the physical outer Cauchy step

Exact finite algebra only.

* `physicalOuterCauchy` — for finite complex families,
  `‖∑ u, a u * S u‖ ^ 2 ≤ (∑ u, ‖a u‖ ^ 2) * (∑ u, ‖S u‖ ^ 2)`.
* `gate1B_A2` — the Gate-labelled source mass `A₂ = ∑ u ‖a u‖ ^ 2`.
* `physicalSecondMoment_imp_amplitude` — a purely ordered-field implication:
  `|P|² ≤ A₂ · E` together with `A₂ · E ≤ X₂ · δ` gives `|P|² ≤ X₂ · δ`.
* `gate1B_physicalSecondMomentBudget` — the two steps chained, with the
  second-moment bound `E` supplied as a hypothesis.

There is **no** asymptotic content here, and in particular nothing in this file
proves any bound on the actual Gate-1B second moment `∑_u |S_u|²`; that quantity
enters only as a hypothesis.  The retracted route through a lower floor
`C₂ ≫ Q log^{-O(1)}` is *not* used: the comparison is made directly against the
supplied physical target.
-/
import Mathlib

namespace Gate1B.SafeExtensions

open Finset

/-- **Physical outer Cauchy–Schwarz.**  Exact finite inequality. -/
theorem physicalOuterCauchy {ι : Type*} (s : Finset ι) (a S : ι → ℂ) :
    ‖∑ u ∈ s, a u * S u‖ ^ 2 ≤ (∑ u ∈ s, ‖a u‖ ^ 2) * (∑ u ∈ s, ‖S u‖ ^ 2) := by
  have hA : (0:ℝ) ≤ ∑ u ∈ s, ‖a u‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : (0:ℝ) ≤ ∑ u ∈ s, ‖S u‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ‖∑ u ∈ s, a u * S u‖ ≤ ∑ u ∈ s, ‖a u‖ * ‖S u‖ :=
    (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _)
  have h2 : ∑ u ∈ s, ‖a u‖ * ‖S u‖
      ≤ Real.sqrt (∑ u ∈ s, ‖a u‖ ^ 2) * Real.sqrt (∑ u ∈ s, ‖S u‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt s _ _
  have h3 := mul_self_le_mul_self (norm_nonneg _) (h1.trans h2)
  calc ‖∑ u ∈ s, a u * S u‖ ^ 2 = ‖∑ u ∈ s, a u * S u‖ * ‖∑ u ∈ s, a u * S u‖ := sq _
    _ ≤ (Real.sqrt (∑ u ∈ s, ‖a u‖ ^ 2) * Real.sqrt (∑ u ∈ s, ‖S u‖ ^ 2)) *
        (Real.sqrt (∑ u ∈ s, ‖a u‖ ^ 2) * Real.sqrt (∑ u ∈ s, ‖S u‖ ^ 2)) := h3
    _ = (∑ u ∈ s, ‖a u‖ ^ 2) * (∑ u ∈ s, ‖S u‖ ^ 2) := by
        rw [show ∀ x y : ℝ, x * y * (x * y) = (x * x) * (y * y) from fun x y => by ring,
          Real.mul_self_sqrt hA, Real.mul_self_sqrt hB]

/-- The Gate-labelled source mass `A₂ = ∑_u |a_u|²`. -/
noncomputable def gate1B_A2 {ι : Type*} (s : Finset ι) (a : ι → ℂ) : ℝ := ∑ u ∈ s, ‖a u‖ ^ 2

theorem gate1B_A2_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℂ) : 0 ≤ gate1B_A2 s a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The outer Cauchy step in Gate-1B notation: `|P|² ≤ A₂ · E` with
`E = ∑_u |S_u|²`. -/
theorem gate1B_outerCauchy {ι : Type*} (s : Finset ι) (a S : ι → ℂ) :
    ‖∑ u ∈ s, a u * S u‖ ^ 2 ≤ gate1B_A2 s a * ∑ u ∈ s, ‖S u‖ ^ 2 :=
  physicalOuterCauchy s a S

/-- **Ordered-field implication.**  If the amplitude square is controlled by
`A₂ · E`, and the physical second-moment budget `A₂ · E ≤ X₂ · δ` holds, then the
amplitude square meets the physical target.  No asymptotics, no lower bound on
any energy is used. -/
theorem physicalSecondMoment_imp_amplitude (P2 A2 E X2 delta : ℝ)
    (hP : P2 ≤ A2 * E) (hbudget : A2 * E ≤ X2 * delta) : P2 ≤ X2 * delta :=
  hP.trans hbudget

/-- **Gate 1B physical second-moment budget.**  The two safe steps chained: the
exact Cauchy inequality, plus a *supplied* second-moment bound
`∑_u |S_u|² ≤ E`, plus the budget inequality `A₂ · E ≤ X₂ · δ`. -/
theorem gate1B_physicalSecondMomentBudget {ι : Type*} (s : Finset ι) (a S : ι → ℂ)
    (E X2 delta : ℝ)
    (hE : ∑ u ∈ s, ‖S u‖ ^ 2 ≤ E)
    (hbudget : gate1B_A2 s a * E ≤ X2 * delta) :
    ‖∑ u ∈ s, a u * S u‖ ^ 2 ≤ X2 * delta := by
  refine physicalSecondMoment_imp_amplitude _ (gate1B_A2 s a) E X2 delta ?_ hbudget
  refine (gate1B_outerCauchy s a S).trans ?_
  exact mul_le_mul_of_nonneg_left hE (gate1B_A2_nonneg s a)

end Gate1B.SafeExtensions
