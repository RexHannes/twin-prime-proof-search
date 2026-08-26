/-
# Gate 1B v8.2 — mandatory countermodels

Five explicit finite countermodels showing that the safe bank cannot be
strengthened in the obvious tempting ways.

* `A` — sign erasure destroys cancellation;
* `B` — the nonzero part does not determine the family (`E` is underdetermined);
* `C` — the maximal fibre value does not determine the ℓ² energy;
* `D` — the coprime CRT statement is vacuous when a quotient modulus is `1`;
* `E` — the zero-mode compiler is false without the hypothesis `E = MT`.
-/
import Mathlib
import Gate1B.SafeAlgebra.GlobalZeroMode

namespace Gate1B.SafeAlgebra

open Finset

/-- **Countermodel A — sign erasure.**  A signed family can sum to zero while
its absolute-value sum is maximal: taking absolute values destroys the
cancellation. -/
theorem countermodel_A_signErasure :
    ∃ f : Fin 2 → ℂ, (∑ i, f i) = 0 ∧ (∑ i, ‖f i‖) = 2 := by
  refine ⟨![1, -1], ?_, ?_⟩ <;> norm_num [Fin.sum_univ_two]

/-- **Countermodel B — the nonzero part does not determine the family.**  Two
different families can have the same nonzero part (they differ by their zero
mode). -/
theorem countermodel_B_nonzeroPart_not_determining :
    ∃ E₁ E₂ : Fin 2 → ℂ, nonzeroPart E₁ = nonzeroPart E₂ ∧ E₁ ≠ E₂ := by
  refine ⟨![1, -1], ![2, 0], ?_, ?_⟩
  · have h := nonzeroPart_independent_expectedTerm (ι := Fin 2) ![2, 0] 1
    have hfun : (fun i => (![2, 0] : Fin 2 → ℂ) i - 1) = ![1, -1] := by
      funext i
      fin_cases i <;> norm_num
    rw [hfun] at h
    exact h
  · intro h
    have := congrFun h 0
    norm_num at this

/-- **Countermodel C — the maximal fibre does not determine the energy.**  Two
families with the same maximal absolute value can have different ℓ² energies. -/
theorem countermodel_C_maxFibre_not_energy :
    ∃ f g : Fin 2 → ℂ,
      (‖f 0‖ = 1 ∧ ‖f 1‖ ≤ 1 ∧ ‖g 0‖ = 1 ∧ ‖g 1‖ ≤ 1) ∧
        (∑ i, ‖f i‖ ^ 2) ≠ ∑ i, ‖g i‖ ^ 2 := by
  refine ⟨![1, 1], ![1, 0], ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  simp [Fin.sum_univ_two]

/-- **Countermodel D — a quotient modulus `1` makes the CRT statement vacuous.**
Every statement about residues modulo `1` holds trivially, so no information is
carried by that factor. -/
theorem countermodel_D_trivialModulus_vacuous :
    ∀ x y : ZMod 1, x = y := by
  intro x y
  exact Subsingleton.elim x y

/-- **Countermodel E — the zero-mode compiler needs its hypothesis.**  Without
`E = MT` the centred residue can have a nonvanishing zero mode. -/
theorem countermodel_E_compiler_needs_E_eq_MT :
    ∃ E MT : Fin 2 → ℂ, zeroMode (fun i => E i - MT i) ≠ 0 := by
  refine ⟨![1, 1], ![0, 0], ?_⟩
  simp [zeroMode, Fin.sum_univ_two]

end Gate1B.SafeAlgebra
