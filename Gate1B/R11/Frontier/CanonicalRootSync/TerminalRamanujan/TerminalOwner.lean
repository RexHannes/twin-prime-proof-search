/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the terminal analytic owner
(T10)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

Exactly **one** new terminal analytic proposition is created here, `EPM2TopBound`, together
with the two reduction budgets it is combined with (`LowRamanujanBudget`, `CrossTermBudget`) and
the EP-M2 target `EPM2Bound`.  All four are stated in the repository's existing `ScalarBudget`
style, and **none of them is inhabited**: they occur only as hypotheses of downstream theorems.
No axiom is introduced.

The only theorem proved here is the *deterministic* implication

```
EPM2TopBound + CrossTermBudget + LowRamanujanBudget  ⇒  EPM2Bound
```

given the exact moment decomposition of `RowOperator.lean`, plus the countermodel showing the
terminal owner is load-bearing.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.CanonicalRoot
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.RowOperator

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. Scaling of budgets -/

/-- A nonnegative constant multiple of a budgeted family is budgeted. -/
theorem scalarBudget_const_mul {A : ℝ → ℝ} {k : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hA : ScalarBudget A k) : ScalarBudget (fun x => c * A x) k := by
  obtain ⟨C, hC, hb⟩ := hA
  refine ⟨(c + 1) * C, by nlinarith, fun x hx => ?_⟩
  have hlog : 1 ≤ Real.log x := one_le_log_of_three_le hx
  have hpow : (0 : ℝ) < (Real.log x) ^ k := by positivity
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 : |c * A x| = c * |A x| := by
    rw [abs_mul, abs_of_nonneg hc]
  rw [h1]
  have h2 : c * |A x| ≤ c * (C * x / (Real.log x) ^ k) :=
    mul_le_mul_of_nonneg_left (hb x hx) hc
  have ht : 0 ≤ C * x / (Real.log x) ^ k := by positivity
  have h3 : (c + 1) * C * x / (Real.log x) ^ k = (c + 1) * (C * x / (Real.log x) ^ k) := by
    ring
  rw [h3]
  nlinarith

/-! ## 2. The EP-M2 propositions -/

/-- **`EPM2Bound`** — the EP-M2 moment target: the raw EP-M2 moment family obeys the required
budget.  EXTERNAL_ANALYTIC — stated, never inhabited, not an axiom. -/
def EPM2Bound (M : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget M (S0 + 2)

/-- **`EPM2TopBound`** — *the* new terminal analytic owner: the terminal (top-band) Ramanujan
moment family obeys the required EP-M2 budget.  EXTERNAL_ANALYTIC / OPEN — stated, never
inhabited, not an axiom. -/
def EPM2TopBound (Mtop : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget Mtop (S0 + 2)

/-- **`LowRamanujanBudget`** — the low-band reduction budget (subterminal Ramanujan modes).
EXTERNAL_ANALYTIC — stated, never inhabited, not an axiom. -/
def LowRamanujanBudget (Mlow : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget Mlow (S0 + 2)

/-- **`CrossTermBudget`** — the cross-term reduction budget.
EXTERNAL_ANALYTIC — stated, never inhabited, not an axiom. -/
def CrossTermBudget (Cross : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget Cross (S0 + 2)

/-! ## 3. The deterministic reduction -/

/-- **`EPM2TopBound` + `CrossTermBudget` + `LowRamanujanBudget` ⇒ `EPM2Bound`.**  The only
input beyond the three budgets is the exact moment decomposition
`M = M_top + 2·Cross + M_low` of `moment_split`; no analytic content is created. -/
theorem epM2_of_terminal_parts {M Mtop Cross Mlow : ℝ → ℝ} {S0 : ℕ}
    (hsplit : ∀ x, M x = Mtop x + 2 * Cross x + Mlow x)
    (htop : EPM2TopBound Mtop S0) (hcross : CrossTermBudget Cross S0)
    (hlow : LowRamanujanBudget Mlow S0) :
    EPM2Bound M S0 := by
  have h2 : ScalarBudget (fun x => 2 * Cross x) (S0 + 2) :=
    scalarBudget_const_mul (by norm_num) hcross
  have hsum : ScalarBudget (fun x => Mtop x + 2 * Cross x + Mlow x) (S0 + 2) :=
    scalarBudget_add (scalarBudget_add htop h2) hlow
  exact scalarBudget_congr hsplit hsum

/-- The terminal owner is load-bearing: the two reduction budgets alone do not give `EPM2Bound`
(take a vanishing low band and cross term and a raw moment equal to `x`). -/
theorem epM2_needs_terminal_owner :
    ∃ (M Mtop Cross Mlow : ℝ → ℝ),
      (∀ x, M x = Mtop x + 2 * Cross x + Mlow x)
        ∧ CrossTermBudget Cross 0 ∧ LowRamanujanBudget Mlow 0
        ∧ ¬ EPM2TopBound Mtop 0 ∧ ¬ EPM2Bound M 0 := by
  refine ⟨fun x => x, fun x => x, fun _ => 0, fun _ => 0, fun x => by ring,
    zero_budgeted 2, zero_budgeted 2, ?_, ?_⟩
  · exact identity_not_budgeted 1
  · exact identity_not_budgeted 1

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
