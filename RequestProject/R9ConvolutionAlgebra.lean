import Mathlib

/-!
# Finite r=9 block convolution algebra

This file distinguishes ordered label assignments from injective (hence
unordered-after-quotient) assignments.  The correction is exactly the finite
sum over repeated labels.  No prime-counting estimate is asserted.
-/

namespace TwinPrimeProject

open scoped BigOperators

/-- Ordered choices of `j` labels from nine slots. -/
abbrev R9OrderedChoice (j : ℕ) := Fin j → Fin 9

/-- The ordered block sum. -/
def r9OrderedBlockSum {A : Type*} [AddCommMonoid A] (j : ℕ)
    (term : R9OrderedChoice j → A) : A :=
  ∑ f : R9OrderedChoice j, term f

/-- The distinct-label part, still in ordered coordinates. -/
def r9DistinctBlockSum {A : Type*} [AddCommMonoid A] (j : ℕ)
    (term : R9OrderedChoice j → A) : A :=
  ∑ f : R9OrderedChoice j, if Function.Injective f then term f else 0

/-- Repeated-label correction. -/
def r9RepeatedFactorCorrection {A : Type*} [AddCommMonoid A] (j : ℕ)
    (term : R9OrderedChoice j → A) : A :=
  ∑ f : R9OrderedChoice j, if Function.Injective f then 0 else term f

/-- Exact partition of ordered factorisations into distinct and repeated-label
parts.  It applies in particular for every `1 ≤ j ≤ 8`. -/
theorem r9RepeatedFactorCorrectionIdentity {A : Type*} [AddCommMonoid A]
    (j : ℕ) (term : R9OrderedChoice j → A) :
    r9OrderedBlockSum j term =
      r9DistinctBlockSum j term + r9RepeatedFactorCorrection j term := by
  simp only [r9OrderedBlockSum, r9DistinctBlockSum, r9RepeatedFactorCorrection,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases h : Function.Injective f <;> simp [h]

/-- Symmetrisation statement: if an unordered block convolution `conv` is
normalised so that its ordered distinct-label sum is `κ • conv`, then the full
ordered cell is that convolution plus the repeated-label correction. -/
theorem r9BlockConvolutionDecomposition {A : Type*} [AddCommMonoid A]
    (j : ℕ) (_hj : 1 ≤ j ∧ j ≤ 8) (term : R9OrderedChoice j → A)
    (κ : ℕ) (conv : A) (hsymm : r9DistinctBlockSum j term = κ • conv) :
    r9OrderedBlockSum j term = κ • conv + r9RepeatedFactorCorrection j term := by
  rw [r9RepeatedFactorCorrectionIdentity, hsymm]

end TwinPrimeProject
