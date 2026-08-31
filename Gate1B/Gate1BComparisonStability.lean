import Mathlib

/-!
# Gate 1B · deterministic comparison-stability compiler (append-only)

**Deterministic algebra only.**  Nothing here is analytic: the theorems say
that a *finite family of linear compiler functionals* transforms in a
completely explicit way when the comparison sequence `b` is perturbed by `Δ`,
and that every compiler inequality survives if each `Δ`-contribution stays
inside its assigned budget.

With

```
b' = b + Δ,   w = c - b,   w' = c - b',
```

we prove

```
T_alpha(w') = T_alpha(w) - T_alpha(Delta),
Z_beta (b') = Z_beta (b) + Z_beta (Delta),
M_gamma(b') = M_gamma(b) + M_gamma(Delta),
```

introduce the normalised seminorm `comparisonCompilerSeminorm`, and prove
`gate1B_comparison_stability`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace ComparisonStability

open Finset

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ## 1. The exact perturbation algebra -/

omit [Module ℂ V] in
/-- The perturbed comparison error `w' = c − (b + Δ) = w − Δ`. -/
theorem error_shift (c b Δ : V) : c - (b + Δ) = (c - b) - Δ := by abel

/-- `T_α(w') = T_α(w) − T_α(Δ)` for every linear compiler functional `T_α`. -/
theorem T_of_perturbed (T : V →ₗ[ℂ] ℂ) (c b Δ : V) :
    T (c - (b + Δ)) = T (c - b) - T Δ := by
  rw [error_shift, map_sub]

/-- `Z_β(b') = Z_β(b) + Z_β(Δ)`. -/
theorem Z_of_perturbed (Z : V →ₗ[ℂ] ℂ) (b Δ : V) : Z (b + Δ) = Z b + Z Δ :=
  map_add _ _ _

/-- `M_γ(b') = M_γ(b) + M_γ(Δ)`. -/
theorem M_of_perturbed (M : V →ₗ[ℂ] ℂ) (b Δ : V) : M (b + Δ) = M b + M Δ :=
  map_add _ _ _

/-! ## 2. The normalised comparison-compiler seminorm -/

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- The normalised compiler seminorm of a perturbation: the total mass of all
compiler functionals evaluated at `Δ`. -/
noncomputable def comparisonCompilerSeminorm
    (T : α → V →ₗ[ℂ] ℂ) (Z : β → V →ₗ[ℂ] ℂ) (M : γ → V →ₗ[ℂ] ℂ) (Δ : V) : ℝ :=
  (∑ a, ‖T a Δ‖) + (∑ b, ‖Z b Δ‖) + ∑ g, ‖M g Δ‖

theorem comparisonCompilerSeminorm_nonneg
    (T : α → V →ₗ[ℂ] ℂ) (Z : β → V →ₗ[ℂ] ℂ) (M : γ → V →ₗ[ℂ] ℂ) (Δ : V) :
    0 ≤ comparisonCompilerSeminorm T Z M Δ := by
  unfold comparisonCompilerSeminorm
  have h1 : (0:ℝ) ≤ ∑ a, ‖T a Δ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : (0:ℝ) ≤ ∑ b, ‖Z b Δ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h3 : (0:ℝ) ≤ ∑ g, ‖M g Δ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

@[simp] theorem comparisonCompilerSeminorm_zero
    (T : α → V →ₗ[ℂ] ℂ) (Z : β → V →ₗ[ℂ] ℂ) (M : γ → V →ₗ[ℂ] ℂ) :
    comparisonCompilerSeminorm T Z M (0 : V) = 0 := by
  simp [comparisonCompilerSeminorm]

theorem comparisonCompilerSeminorm_add_le
    (T : α → V →ₗ[ℂ] ℂ) (Z : β → V →ₗ[ℂ] ℂ) (M : γ → V →ₗ[ℂ] ℂ) (Δ Δ' : V) :
    comparisonCompilerSeminorm T Z M (Δ + Δ')
      ≤ comparisonCompilerSeminorm T Z M Δ + comparisonCompilerSeminorm T Z M Δ' := by
  unfold comparisonCompilerSeminorm
  have h1 : ∑ a, ‖T a (Δ + Δ')‖ ≤ (∑ a, ‖T a Δ‖) + ∑ a, ‖T a Δ'‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => by rw [map_add]; exact norm_add_le _ _
  have h2 : ∑ b, ‖Z b (Δ + Δ')‖ ≤ (∑ b, ‖Z b Δ‖) + ∑ b, ‖Z b Δ'‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun b _ => by rw [map_add]; exact norm_add_le _ _
  have h3 : ∑ g, ‖M g (Δ + Δ')‖ ≤ (∑ g, ‖M g Δ‖) + ∑ g, ‖M g Δ'‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun g _ => by rw [map_add]; exact norm_add_le _ _
  linarith

theorem comparisonCompilerSeminorm_smul
    (T : α → V →ₗ[ℂ] ℂ) (Z : β → V →ₗ[ℂ] ℂ) (M : γ → V →ₗ[ℂ] ℂ) (c : ℂ) (Δ : V) :
    comparisonCompilerSeminorm T Z M (c • Δ) =
      ‖c‖ * comparisonCompilerSeminorm T Z M Δ := by
  unfold comparisonCompilerSeminorm
  simp [map_smul, Finset.mul_sum, mul_add]

/-- Every individual functional is dominated by the seminorm. -/
theorem norm_T_le_seminorm
    (T : α → V →ₗ[ℂ] ℂ) (Z : β → V →ₗ[ℂ] ℂ) (M : γ → V →ₗ[ℂ] ℂ) (Δ : V) (a : α) :
    ‖T a Δ‖ ≤ comparisonCompilerSeminorm T Z M Δ := by
  unfold comparisonCompilerSeminorm
  have h0 : ‖T a Δ‖ ≤ ∑ a', ‖T a' Δ‖ :=
    Finset.single_le_sum (f := fun a' => ‖T a' Δ‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h2 : (0:ℝ) ≤ ∑ b, ‖Z b Δ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h3 : (0:ℝ) ≤ ∑ g, ‖M g Δ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

/-! ## 3. The stability theorem -/

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- **`gate1B_comparison_stability`.**  Deterministic and kernel-safe: if every
`Δ`-contribution lies inside its assigned budget, and each compiler inequality
was proved with that budget in reserve, then every compiler inequality remains
valid after the comparison sequence is perturbed from `b` to `b' = b + Δ`.

No analytic input is used: the budgets and the original inequalities are
hypotheses. -/
theorem gate1B_comparison_stability
    (T : α → V →ₗ[ℂ] ℂ) (Z : β → V →ₗ[ℂ] ℂ) (M : γ → V →ₗ[ℂ] ℂ)
    (c b Δ : V)
    (budgetT : α → ℝ) (budgetZ : β → ℝ) (budgetM : γ → ℝ)
    (boundT : α → ℝ) (boundZ : β → ℝ) (boundM : γ → ℝ)
    (hΔT : ∀ a, ‖T a Δ‖ ≤ budgetT a)
    (hΔZ : ∀ x, ‖Z x Δ‖ ≤ budgetZ x)
    (hΔM : ∀ g, ‖M g Δ‖ ≤ budgetM g)
    (hT : ∀ a, ‖T a (c - b)‖ ≤ boundT a - budgetT a)
    (hZ : ∀ x, ‖Z x b‖ ≤ boundZ x - budgetZ x)
    (hM : ∀ g, ‖M g b‖ ≤ boundM g - budgetM g) :
    (∀ a, ‖T a (c - (b + Δ))‖ ≤ boundT a) ∧
      (∀ x, ‖Z x (b + Δ)‖ ≤ boundZ x) ∧
        ∀ g, ‖M g (b + Δ)‖ ≤ boundM g := by
  refine ⟨fun a => ?_, fun x => ?_, fun g => ?_⟩
  · rw [T_of_perturbed]
    calc ‖T a (c - b) - T a Δ‖ ≤ ‖T a (c - b)‖ + ‖T a Δ‖ := norm_sub_le _ _
      _ ≤ (boundT a - budgetT a) + budgetT a := add_le_add (hT a) (hΔT a)
      _ = boundT a := by ring
  · rw [Z_of_perturbed]
    calc ‖Z x b + Z x Δ‖ ≤ ‖Z x b‖ + ‖Z x Δ‖ := norm_add_le _ _
      _ ≤ (boundZ x - budgetZ x) + budgetZ x := add_le_add (hZ x) (hΔZ x)
      _ = boundZ x := by ring
  · rw [M_of_perturbed]
    calc ‖M g b + M g Δ‖ ≤ ‖M g b‖ + ‖M g Δ‖ := norm_add_le _ _
      _ ≤ (boundM g - budgetM g) + budgetM g := add_le_add (hM g) (hΔM g)
      _ = boundM g := by ring

/-- Seminorm form of the same statement: a perturbation of total compiler
seminorm at most `ε` moves every compiler functional by at most `ε`. -/
theorem comparison_stability_seminorm_form
    (T : α → V →ₗ[ℂ] ℂ) (Z : β → V →ₗ[ℂ] ℂ) (M : γ → V →ₗ[ℂ] ℂ)
    (c b Δ : V) (ε : ℝ) (hΔ : comparisonCompilerSeminorm T Z M Δ ≤ ε) (a : α) :
    ‖T a (c - (b + Δ))‖ ≤ ‖T a (c - b)‖ + ε := by
  rw [T_of_perturbed]
  calc ‖T a (c - b) - T a Δ‖ ≤ ‖T a (c - b)‖ + ‖T a Δ‖ := norm_sub_le _ _
    _ ≤ ‖T a (c - b)‖ + ε := by
        gcongr
        exact le_trans (norm_T_le_seminorm T Z M Δ a) hΔ

end ComparisonStability
end CurrentProgramme
end TwinPrimeProject
