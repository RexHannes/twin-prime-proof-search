/-
# Gate 1B v8.3 — the same-`q` Gram is **not** a function of residue energy

**Status: COUNTERMODEL (PROVED_FINITE).**

Residue energy is `Eres(R) = ∑_u |R(u)|²`, and by `character_parseval` this is
exactly `|G|⁻¹ ∑_χ |R̂(χ)|²`: residue energy sees only the *total* Fourier mass.

The same-`q` Gram of §16 is, by `sameQ_gram_eq_gramForm`, a weighted Hermitian
form in `R̂`.  A weighted Hermitian form is **not** determined by the total
Fourier mass: two hat-vectors supported on two different nontrivial character
modes with equal total mass produce different Gram output.

Consequence (firewall): no estimate may replace the same-`q` Gram by residue
energy unless an additional complete orthogonality hypothesis on the dual
`t`-family is supplied, which would force the weight matrix to be a multiple of
the identity.
-/
import Mathlib
import Gate1B.SafeAlgebra.SameQCharacterGram

namespace Gate1B.SafeAlgebra

open Finset

/-- A weighted Hermitian Gram form in the Fourier coefficients. -/
noncomputable def gramForm {ι : Type*} [Fintype ι] (w : ι → ι → ℂ) (Rh : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι, w i j * (Rh i * (starRingEnd ℂ) (Rh j))

/-- Total Fourier mass. -/
noncomputable def fourierEnergy {ι : Type*} [Fintype ι] (Rh : ι → ℂ) : ℝ :=
  ∑ i : ι, ‖Rh i‖ ^ 2

section Link

variable {q : ℕ} [NeZero q] {Ch : Type*} [Fintype Ch] [DecidableEq Ch]

/-- The same-`q` Gram weight matrix, with the source coefficients stripped out. -/
noncomputable def sameQWeightMatrix (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (b : (ZMod q)ˣ) (T : Finset (ZMod q)ˣ) (c d : Ch) : ℂ :=
  (tauCoeff C S c ^ 2 * (starRingEnd ℂ) (tauCoeff C S d ^ 2)) *
    (S.chi c b * (starRingEnd ℂ) (S.chi d b)) * dualCorrelation S T c d

/-- **The same-`q` Gram is a weighted Hermitian form in `R̂`.** -/
theorem sameQ_gram_eq_gramForm (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (R : (ZMod q)ˣ → ℂ) (b : (ZMod q)ˣ)
    (T : Finset (ZMod q)ˣ) :
    ∑ t ∈ T, sameQF C R b t * (starRingEnd ℂ) (sameQF C R b t)
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) ^ 2 *
          gramForm (sameQWeightMatrix C S b T) (S.hat R) := by
  rw [sameQ_gram_expand C S R b T]
  congr 1
  unfold gramForm sameQWeightMatrix sameQGramWeight
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Link

/-- The two-mode weight matrix: unit weight on the first mode, weight `2` on the
second. -/
noncomputable def twoModeWeight : Fin 2 → Fin 2 → ℂ :=
  fun i j => if i = j then (if i = 0 then 1 else 2) else 0

/-- **Countermodel.**  Two hat-vectors with equal total Fourier mass and
different Gram output. -/
theorem sameQ_not_function_of_residueEnergy :
    ∃ (w : Fin 2 → Fin 2 → ℂ) (R1 R2 : Fin 2 → ℂ),
      fourierEnergy R1 = fourierEnergy R2 ∧ gramForm w R1 ≠ gramForm w R2 := by
  refine ⟨twoModeWeight, ![1, 0], ![0, 1], ?_, ?_⟩
  · simp [fourierEnergy, Fin.sum_univ_two]
  · simp [gramForm, twoModeWeight, Fin.sum_univ_two]

/-- **Firewall form.**  No function of the total Fourier mass can compute the
weighted Gram. -/
theorem sameQ_ne_residueEnergy_counterexample :
    ∃ w : Fin 2 → Fin 2 → ℂ,
      ¬ ∃ Phi : ℝ → ℂ, ∀ Rh : Fin 2 → ℂ, gramForm w Rh = Phi (fourierEnergy Rh) := by
  obtain ⟨w, R1, R2, hE, hG⟩ := sameQ_not_function_of_residueEnergy
  refine ⟨w, ?_⟩
  rintro ⟨Phi, hPhi⟩
  exact hG (by rw [hPhi R1, hPhi R2, hE])

end Gate1B.SafeAlgebra
