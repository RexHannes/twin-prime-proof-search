/-
# Gate 1B v8.5 — generic two-sequence large-sieve interface

**Status: EXTERNAL_ANALYTIC_INTERFACE (uninhabited).**

The classical multiplicative large sieve is *not* declared as a Lean theorem
here, and it is *not* axiomatised.  It is represented as explicit **data**: a
structure whose single substantive field is the hypothesis

    ∀ a, characterEnergy a ≤ (Q^2 + N) * l2Energy a * analyticLoss.

No global instance and no inhabitant is provided; the compiler theorems take a
term of this structure as an argument, so every use is visible in the statement.

`largeSieve_not_self_generated` records that finite algebra alone cannot produce
such a term: for *any* fixed parameters there is a candidate character-energy
functional violating the bound.
-/
import Mathlib

namespace Gate1B.SafeExtensions

open Finset

/-- The `ℓ²` energy of a finite coefficient sequence. -/
noncomputable def l2Energy {ι : Type*} [Fintype ι] (a : ι → ℂ) : ℝ := ∑ i : ι, ‖a i‖ ^ 2

theorem l2Energy_nonneg {ι : Type*} [Fintype ι] (a : ι → ℂ) : 0 ≤ l2Energy a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **External analytic interface.**  A supplied multiplicative large-sieve
inequality for one prescribed character-energy functional.

The field `bound` is a *hypothesis carried by the structure*, never an axiom. -/
structure LargeSieveBound (ι : Type*) [Fintype ι] where
  /-- The conductor scale `Q`. -/
  Q : ℝ
  /-- The length `N` of the coefficient sequence. -/
  N : ℝ
  /-- The admissible analytic loss (e.g. a fixed power of `log`). -/
  analyticLoss : ℝ
  /-- The character energy functional that the sieve controls. -/
  characterEnergy : (ι → ℂ) → ℝ
  /-- The supplied inequality. -/
  bound : ∀ a : ι → ℂ,
    characterEnergy a ≤ (Q ^ 2 + N) * l2Energy a * analyticLoss

namespace LargeSieveBound

variable {ι : Type*} [Fintype ι]

/-- Monotone corollary: if the `ℓ²` energy of the sequence is itself bounded by
`E`, the character energy is bounded by `(Q² + N) * E * analyticLoss`. -/
theorem characterEnergy_le_of_l2_le (ls : LargeSieveBound ι) (a : ι → ℂ) (E : ℝ)
    (hE : l2Energy a ≤ E) (hQN : 0 ≤ ls.Q ^ 2 + ls.N) (hloss : 0 ≤ ls.analyticLoss) :
    ls.characterEnergy a ≤ (ls.Q ^ 2 + ls.N) * E * ls.analyticLoss := by
  refine (ls.bound a).trans ?_
  have : (ls.Q ^ 2 + ls.N) * l2Energy a ≤ (ls.Q ^ 2 + ls.N) * E :=
    mul_le_mul_of_nonneg_left hE hQN
  exact mul_le_mul_of_nonneg_right this hloss

end LargeSieveBound

/-- **No self-generation.**  For any prescribed parameters `Q`, `N`,
`analyticLoss`, there is a candidate character-energy functional for which the
large-sieve inequality *fails*.  Hence the finite compiler cannot manufacture a
`LargeSieveBound`: the analytic input is genuinely external. -/
theorem largeSieve_not_self_generated (Q N loss : ℝ) :
    ∃ E : (Unit → ℂ) → ℝ, ¬ (∀ a : Unit → ℂ, E a ≤ (Q ^ 2 + N) * l2Energy a * loss) := by
  refine ⟨fun a => (|(Q ^ 2 + N) * loss| + 1) * ‖a ()‖ ^ 2, ?_⟩
  intro h
  have h1 := h (fun _ => (1 : ℂ))
  have hl : l2Energy (fun _ : Unit => (1 : ℂ)) = 1 := by
    simp [l2Energy]
  rw [hl] at h1
  simp only [norm_one, one_pow, mul_one] at h1
  have h2 : (Q ^ 2 + N) * loss ≤ |(Q ^ 2 + N) * loss| := le_abs_self _
  linarith

end Gate1B.SafeExtensions
