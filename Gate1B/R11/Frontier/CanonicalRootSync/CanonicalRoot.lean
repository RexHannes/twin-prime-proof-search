/-
# Gate1B / R11 / Frontier / CanonicalRootSync : the canonical scalar root object  (P1)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

The latest informal/analytic representation of the frontier scalar is

```
F₁₁^new  =  ∑_n g(n) [ Λ(n+2) − b(n) ]  +  O( x L^{−S₀−2} ).
```

This module formalises that representation with the three layers **kept apart**, exactly as the
brief requires:

* §1 the **exact algebraic identity**: the canonical root sum, its linearity, and the proof that
  it *is* the pre-existing exact owner `Gate1B.R11.R11Residual` — so the root identity is
  derived from an existing exact owner, not postulated;
* §2 the **error-budget proposition** `CanonicalRootErrorBudget`: a named interface, never
  inhabited, no axiom;
* §3 the **separation theorem**: the exact identity does *not* imply the budget (an explicit
  countermodel), so the analytic estimate is genuinely load-bearing and cannot be silently
  upgraded.

No `sorry`, no `admit`, no custom axiom, no `native_decide`.
-/
import Mathlib
import Gate1B.R11.Bank
import Gate1B.R11.Frontier.Latest.GlobalCoreAggregation

namespace Gate1B.R11.Frontier.CanonicalRootSync

open Finset ArithmeticFunction

/-! ## 1. The exact algebraic identity -/

/-- The **canonical scalar root sum** `∑_{n ∈ s} g(n) [ Λ(n+2) − b(n) ]` at the fixed shift `2`.
The shift is fixed throughout: nothing here averages over the shift. -/
noncomputable def rootSum (s : Finset ℕ) (g b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ s, g n * ((vonMangoldt (n + 2) : ℝ) - b n)

/-- The canonical root sum splits exactly into the shifted von Mangoldt pairing minus the
comparison pairing. -/
theorem rootSum_split (s : Finset ℕ) (g b : ℕ → ℝ) :
    rootSum s g b
      = (∑ n ∈ s, g n * (vonMangoldt (n + 2) : ℝ)) - ∑ n ∈ s, g n * b n := by
  unfold rootSum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **The root identity is derived from an existing exact owner.**  With the bracket-local
comparison `bLoc Bc` of the banked comparison typing, the canonical root sum is *exactly* the
pre-existing `R11Residual` of `Gate1B/R11/Bank.lean`.  No new object, no missing bridge. -/
theorem rootSum_eq_R11Residual (s : Finset ℕ) (g Bc : ℕ → ℝ) :
    rootSum s g (bLoc Bc) = Gate1B.R11.R11Residual s g Bc := by
  rw [rootSum_split, Gate1B.R11.R11Residual]

/-- Linearity of the canonical root sum in the source weight. -/
theorem rootSum_add_source (s : Finset ℕ) (g₁ g₂ b : ℕ → ℝ) :
    rootSum s (fun n => g₁ n + g₂ n) b = rootSum s g₁ b + rootSum s g₂ b := by
  unfold rootSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Exact mask split of the canonical root sum: no double charge. -/
theorem rootSum_mask_split (s : Finset ℕ) (g b : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p] :
    rootSum s g b = rootSum (s.filter p) g b + rootSum (s.filter (fun n => ¬ p n)) g b := by
  unfold rootSum
  exact (Finset.sum_filter_add_sum_filter_not s p _).symm

/-- **The canonical root error**, defined so that the root identity is an exact identity and
carries no hidden estimate. -/
noncomputable def rootError (F : ℝ) (s : Finset ℕ) (g b : ℕ → ℝ) : ℝ := F - rootSum s g b

/-- **The canonical root identity** (exact, unconditional):
`F₁₁^new = ∑_n g(n)[Λ(n+2) − b(n)] + Err`. -/
theorem canonical_root_identity (F : ℝ) (s : Finset ℕ) (g b : ℕ → ℝ) :
    F = rootSum s g b + rootError F s g b := by
  unfold rootError; ring

/-- Equivalent difference form: `F₁₁^new − ∑_n g(n)[Λ(n+2) − b(n)] = Err`. -/
theorem canonical_root_difference (F : ℝ) (s : Finset ℕ) (g b : ℕ → ℝ) :
    F - rootSum s g b = rootError F s g b := rfl

/-! ## 2. The error-budget proposition (interface only) -/

/-- **Canonical root error budget** at logarithmic precision `S₀ + 2`:

`|F₁₁^new(x) − ∑_n g(n)[Λ(n+2) − b(n)]| ≤ C · x / (log x)^{S₀+2}` for all large `x`.

EXTERNAL_ANALYTIC — stated, never inhabited, not an axiom. -/
def ScalarBudget (R : ℝ → ℝ) (S0 : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → |R x| ≤ C * x / (Real.log x) ^ S0

/-- **Canonical root error budget** at logarithmic precision `S₀ + 2`.
EXTERNAL_ANALYTIC — stated, never inhabited, not an axiom. -/
def CanonicalRootErrorBudget (Err : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget Err (S0 + 2)

/-- `log x ≥ 1` for `x ≥ 3`: the elementary fact used by every budget comparison here. -/
theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have h1 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h2 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    have := Real.log_le_log (Real.exp_pos 1) h2
    rwa [Real.log_exp] at this
  linarith

/-- Budgets add. -/
theorem scalarBudget_add {A B : ℝ → ℝ} {k : ℕ} (hA : ScalarBudget A k) (hB : ScalarBudget B k) :
    ScalarBudget (fun x => A x + B x) k := by
  obtain ⟨C₁, hC₁, h₁⟩ := hA
  obtain ⟨C₂, hC₂, h₂⟩ := hB
  refine ⟨C₁ + C₂, by linarith, fun x hx => ?_⟩
  calc |A x + B x| ≤ |A x| + |B x| := abs_add_le _ _
    _ ≤ C₁ * x / (Real.log x) ^ k + C₂ * x / (Real.log x) ^ k := add_le_add (h₁ x hx) (h₂ x hx)
    _ = (C₁ + C₂) * x / (Real.log x) ^ k := by ring

/-- A budget transfers along a pointwise identity. -/
theorem scalarBudget_congr {A B : ℝ → ℝ} {k : ℕ} (h : ∀ x, A x = B x) (hB : ScalarBudget B k) :
    ScalarBudget A k := by
  obtain ⟨C, hC, hb⟩ := hB
  exact ⟨C, hC, fun x hx => by rw [h x]; exact hb x hx⟩

/-- A budget at higher logarithmic precision implies the budget at lower precision. -/
theorem scalarBudget_mono {A : ℝ → ℝ} {j k : ℕ} (hjk : j ≤ k) (hA : ScalarBudget A k) :
    ScalarBudget A j := by
  obtain ⟨C, hC, hb⟩ := hA
  refine ⟨C, hC, fun x hx => ?_⟩
  have hlog : 1 ≤ Real.log x := one_le_log_of_three_le hx
  have hpow0 : (0 : ℝ) < (Real.log x) ^ j := by positivity
  have hmono : (Real.log x) ^ j ≤ (Real.log x) ^ k := pow_le_pow_right₀ hlog hjk
  have hx0 : (0 : ℝ) < x := by linarith
  exact (hb x hx).trans (div_le_div_of_nonneg_left (by positivity) hpow0 hmono)

/-- **Deterministic budget adapter.**  If the root sum family obeys its budget and the error
family obeys the canonical root error budget, the total obeys the budget: the analytic content
is entirely in the two hypotheses. -/
theorem scalarBudget_of_parts {F Srep Err : ℝ → ℝ} {S0 : ℕ}
    (hid : ∀ x, F x = Srep x + Err x)
    (hS : ScalarBudget Srep S0) (hE : CanonicalRootErrorBudget Err S0) :
    ScalarBudget F S0 :=
  scalarBudget_congr hid (scalarBudget_add hS (scalarBudget_mono (by omega) hE))

/-! ## 3. Separation: the exact identity does not imply the budget -/

/-- The identity family `x ↦ x` violates every budget of positive logarithmic precision: the
reference countermodel of this layer. -/
theorem identity_not_budgeted (k : ℕ) : ¬ ScalarBudget (fun x : ℝ => x) (k + 1) := by
  rintro ⟨C, hC, h⟩
  have hx3 : (3 : ℝ) ≤ Real.exp (C + 3) := by
    have h3 : Real.exp (C + 3) = Real.exp C * Real.exp 3 := by rw [← Real.exp_add]
    have h4 : (1 : ℝ) ≤ Real.exp C := Real.one_le_exp (le_of_lt hC)
    have h5 : (3 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ)
      linarith
    nlinarith [Real.exp_pos C, Real.exp_pos (3 : ℝ)]
  have hxpos : (0 : ℝ) < Real.exp (C + 3) := Real.exp_pos _
  have hb := h (Real.exp (C + 3)) hx3
  rw [abs_of_pos hxpos, Real.log_exp] at hb
  have hden : (0 : ℝ) < (C + 3) ^ (k + 1) := by positivity
  rw [le_div_iff₀ hden] at hb
  have hmono : (C + 3) ^ 1 ≤ (C + 3) ^ (k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  simp only [pow_one] at hmono
  nlinarith [hxpos, hC]

/-- The zero family satisfies every budget (used to isolate a single failing component in the
countermodels of this layer). -/
theorem zero_budgeted (k : ℕ) : ScalarBudget (fun _ : ℝ => (0 : ℝ)) k :=
  ⟨1, by norm_num, fun x hx => by
    have hx0 : (0 : ℝ) < x := by linarith
    have hlog : 1 ≤ Real.log x := one_le_log_of_three_le hx
    have : (0 : ℝ) < (Real.log x) ^ k := by positivity
    simp only [abs_zero]
    positivity⟩

/-- **The canonical root identity alone proves nothing analytic.**  The identity is universally
valid, yet there is a family for which the error budget fails: hence
`CanonicalRootErrorBudget` is genuinely load-bearing and must stay an uninhabited interface. -/
theorem errorBudget_not_implied_by_identity :
    (∀ (F : ℝ) (s : Finset ℕ) (g b : ℕ → ℝ), F = rootSum s g b + rootError F s g b)
      ∧ ∃ Err : ℝ → ℝ, ¬ CanonicalRootErrorBudget Err 0 :=
  ⟨canonical_root_identity, ⟨fun x => x, identity_not_budgeted 1⟩⟩

end Gate1B.R11.Frontier.CanonicalRootSync
