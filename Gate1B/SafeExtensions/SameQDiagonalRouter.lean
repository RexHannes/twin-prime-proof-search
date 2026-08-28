/-
# Gate 1B v13 — same-`q` diagonal router (UNINHABITED residue-energy input)

**Status: interface UNINHABITED; the implication is PROVED.**

The `χ₁ = χ₂` part of the same-`q` character Gram is

    S_diag = (1/|Ch|²) · K(1) · ∑_χ |c(χ)|².

The bound it needs is therefore exactly a *residue-energy* bound on the
coefficient sequence together with a bound on the principal kernel value.  We
searched the repository for an existing JQ7 object with literally the same
source sequence and the same target; none matches (the banked
`productResidueEnergy_le_fibre_mul` is a no-wrap integer-fibre statement about a
different sequence).  The real input is therefore left **UNINHABITED**.

Contents:

* `SameQDiagonalResidueEnergyInput` — UNINHABITED interface;
* `sameQGramDiag_bound_of_input` — the deterministic implication;
* `sameQDiagonalResidueEnergyInput_not_vacuous` — non-vacuity guard.
-/
import Mathlib
import Gate1B.SafeAlgebra.SameQCharacterGramDiagonalization

namespace Gate1B.SafeExtensions

open Finset Gate1B.SafeAlgebra

variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] [CommGroup Ch]

/-- **UNINHABITED INTERFACE.**  The residue-energy bound needed for the
`χ₁ = χ₂` part of the same-`q` Gram. -/
structure SameQDiagonalResidueEnergyInput (c : Ch → ℂ) (E : ℝ) : Prop where
  /-- EXTERNAL ANALYTIC INPUT — never supplied here. -/
  energy_le : ∑ x : Ch, ‖c x‖ ^ 2 ≤ E

omit [DecidableEq Ch] in
/-- **Deterministic implication**: the residue-energy input plus a bound on the
principal kernel value bounds the same-`q` diagonal. -/
theorem sameQGramDiag_bound_of_input (c : Ch → ℂ) (K : Ch → ℂ) (E B : ℝ)
    (hB : ‖K 1‖ ≤ B) (hB0 : 0 ≤ B) (hin : SameQDiagonalResidueEnergyInput c E) :
    ‖sameQGramDiag c K‖ ≤ (1 / (Fintype.card Ch : ℝ) ^ 2) * (B * E) := by
  classical
  rw [sameQGramDiag_eq c K, norm_mul, norm_mul]
  have hcard : ‖(1 / (Fintype.card Ch : ℂ) ^ 2)‖ = 1 / (Fintype.card Ch : ℝ) ^ 2 := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
  rw [hcard]
  have hsum : ‖∑ x : Ch, ((‖c x‖ ^ 2 : ℝ) : ℂ)‖ = ∑ x : Ch, ‖c x‖ ^ 2 := by
    have hcast : (∑ x : Ch, ((‖c x‖ ^ 2 : ℝ) : ℂ)) = ((∑ x : Ch, ‖c x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun x _ => by positivity
  rw [hsum]
  have hE0 : 0 ≤ ∑ x : Ch, ‖c x‖ ^ 2 := Finset.sum_nonneg fun x _ => by positivity
  have hstep : ‖K 1‖ * ∑ x : Ch, ‖c x‖ ^ 2 ≤ B * E := by
    calc ‖K 1‖ * ∑ x : Ch, ‖c x‖ ^ 2 ≤ B * ∑ x : Ch, ‖c x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hB hE0
      _ ≤ B * E := mul_le_mul_of_nonneg_left hin.energy_le hB0
  have hpos : (0 : ℝ) ≤ 1 / (Fintype.card Ch : ℝ) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hstep hpos

omit [DecidableEq Ch] [CommGroup Ch] in
/-- **Non-vacuity guard.**  A negative energy target is impossible. -/
theorem sameQDiagonalResidueEnergyInput_not_vacuous (c : Ch → ℂ) :
    ¬ SameQDiagonalResidueEnergyInput c (-1) := by
  intro h
  have h0 : (0 : ℝ) ≤ ∑ x : Ch, ‖c x‖ ^ 2 := Finset.sum_nonneg fun x _ => by positivity
  have := h.energy_le
  linarith

end Gate1B.SafeExtensions
