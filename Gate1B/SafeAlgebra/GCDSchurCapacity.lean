/-
# Gate 1B v8.2 — GCD-stratified Schur capacity

A finite Schur-type capacity statement for a GCD-stratified family, obtained by
specialising the banked weighted Schur bound
`Universal.SafeAlgebra.weightedBlockSchur`, together with the exact rational
capacity arithmetic used to compare row sums against a budget.

**Capacity arithmetic only.**  The kernel majorant `k` and the row budget `η`
are *inputs*: nothing here proves any bound on an actual GCD kernel, and no
`X^{o(1)}` statement is asserted in Lean (such language appears only in
comments).
-/
import Mathlib
import Universal.SafeAlgebra.WeightedSchur

namespace Gate1B.SafeAlgebra

open Finset

/-- **GCD-stratified Schur capacity.**  With a symmetric nonnegative majorant of
the block cross terms whose rows are bounded by `η`, the synthesised vector has
energy at most `η` times the coefficient energy. -/
theorem gcdSchurCapacity {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {Γ : Type*} [Fintype Γ] (B : Γ → (H →L[ℂ] K)) (f : Γ → H) (k : Γ → Γ → ℝ) (η : ℝ)
    (hk : ∀ γ γ', ‖ContinuousLinearMap.adjoint (B γ) ∘L B γ'‖ ≤ k γ γ')
    (hknn : ∀ γ γ', 0 ≤ k γ γ') (hsymm : ∀ γ γ', k γ γ' = k γ' γ)
    (hrow : ∀ γ, ∑ γ', k γ γ' ≤ η) :
    ‖UniversalV8.synthesis B f‖ ^ 2 ≤ η * ∑ γ, ‖f γ‖ ^ 2 :=
  Universal.SafeAlgebra.weightedBlockSchur B f k η hk hknn hsymm hrow

/-- A uniform-entry majorant: if every cross term is at most `c ≥ 0` and there
are `#Γ` strata, the row budget is `#Γ · c`. -/
theorem gcdSchur_rowBudget_of_uniform {Γ : Type*} [Fintype Γ] (k : Γ → Γ → ℝ) (c : ℝ)
    (hc : ∀ γ γ', k γ γ' ≤ c) (γ : Γ) :
    ∑ γ', k γ γ' ≤ (Fintype.card Γ : ℝ) * c := by
  calc ∑ γ', k γ γ' ≤ ∑ _γ' : Γ, c := Finset.sum_le_sum fun γ' _ => hc γ γ'
    _ = (Fintype.card Γ : ℝ) * c := by simp [Finset.card_univ, mul_comm]

/-- **Capacity comparison in exact rational exponents.**  If the stratum count
has exponent `s` and the uniform cross-term majorant has exponent `t`, then the
row budget `Y^(s+t)` clears a target exponent `τ` as soon as `s + t ≤ τ`. -/
theorem gcdSchur_exponentCapacity {Y : ℝ} (hY : 1 ≤ Y) {s t τ : ℚ} (h : s + t ≤ τ) :
    Y ^ ((s : ℝ) + (t : ℝ)) ≤ Y ^ (τ : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hY (by exact_mod_cast h)

/-- The Schur budget is monotone in the row bound. -/
theorem gcdSchur_budget_mono {Γ : Type*} [Fintype Γ] (k : Γ → Γ → ℝ) {η η' : ℝ}
    (hle : η ≤ η') (hrow : ∀ γ, ∑ γ', k γ γ' ≤ η) (γ : Γ) : ∑ γ', k γ γ' ≤ η' :=
  (hrow γ).trans hle

end Gate1B.SafeAlgebra
