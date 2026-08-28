/-
# Gate 1B v8.5 — source-scalar firewall (`delta_i` normalisation)

**Status: SOURCE_INTERFACE (no scalar is defined) + PROVED_FINITE (logical guard).**

The exact prime / log-prime normalisation of the scalars `delta_i` is
*source-sensitive*.  The literal source normalisation is not available in this
repository, so no value is defined here — guessing one would silently change the
meaning of every downstream packet.

What *is* proved is the logical guard: agreement of the untwisted (PNT-level)
aggregate does **not** determine the individual scalars.  A two-sequence finite
counterexample is given.
-/
import Mathlib

namespace Gate1B.SafeExtensions

open Finset

/-- The untwisted aggregate of a finite scalar family (the only quantity that a
PNT-level statement sees). -/
noncomputable def untwistedAggregate {n : ℕ} (d : Fin n → ℝ) : ℝ := ∑ i : Fin n, d i

/-- **Scalar pin firewall.**  Two different scalar families can have the same
untwisted aggregate: PNT-level agreement does not pin `delta_i`. -/
theorem untwisted_does_not_determine_scalars :
    ∃ d₁ d₂ : Fin 2 → ℝ, untwistedAggregate d₁ = untwistedAggregate d₂ ∧ d₁ ≠ d₂ := by
  refine ⟨fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 0 else 1, ?_, ?_⟩
  · simp [untwistedAggregate, Fin.sum_univ_two]
  · intro h
    have := congrFun h 0
    simp at this

/-- The same failure persists after any *twist* that is constant on the family:
constant twists factor out of the aggregate, so they add no information. -/
theorem constant_twist_adds_nothing {n : ℕ} (c : ℝ) (d₁ d₂ : Fin n → ℝ)
    (h : untwistedAggregate d₁ = untwistedAggregate d₂) :
    ∑ i : Fin n, c * d₁ i = ∑ i : Fin n, c * d₂ i := by
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact congrArg (fun t => c * t) h

/-- Only a *non-constant* twist can separate the two families — which is exactly
the source-specific information that is missing.  Here is such a twist, showing
the obstruction is not vacuous. -/
theorem separating_twist_exists :
    ∃ (t : Fin 2 → ℝ) (d₁ d₂ : Fin 2 → ℝ),
      untwistedAggregate d₁ = untwistedAggregate d₂ ∧
        ∑ i : Fin 2, t i * d₁ i ≠ ∑ i : Fin 2, t i * d₂ i := by
  refine ⟨fun i => if i = 0 then 1 else 0,
    fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 0 else 1, ?_, ?_⟩
  · simp [untwistedAggregate, Fin.sum_univ_two]
  · simp [Fin.sum_univ_two]

end Gate1B.SafeExtensions
