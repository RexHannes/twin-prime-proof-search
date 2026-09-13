/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the bridge to the canonical
`j = 2` owner  (T11)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted; in
particular the canonical owner `J2ResidualCenteredBound` is **not** discharged, renamed or
weakened.

This module places the new terminal owner strictly *below* the existing canonical `j = 2`
owner, in the only honest way available:

```
EPM2TopBound + CrossTermBudget + LowRamanujanBudget            (analytic, all open)
      ⇒ EPM2Bound                                              (proved here)
EPM2Bound + epM2Realisation                                    (exact identification, OPEN)
      ⇒ J2ResidualCenteredBound                                (proved here)
J2ResidualCenteredBound + principal budget
      ⇒ raw j = 2 budget                                       (pre-existing adapter)
```

`epM2Realisation` is the **single new missing exact bridge**: the statement that the canonical
centered `j = 2` residual family *is* the EP-M2 row moment family.  It is a proposition, never
inhabited, and is not an axiom.  It is not a duplicate of the three pre-existing missing
bridges (`rootChartRealisation`, `rankDecompositionRealisation`, `j2CenteredSplitRealisation`):
those identify the canonical root, the rank decomposition and the centered `j = 2` chart, all
*above* the `j = 2` owner, whereas `epM2Realisation` identifies the object *below* it.

Because no exact realisation is established, `J2ResidualCenteredBound` is **retained** in the
canonical cut and `EPM2TopBound` is recorded as a subordinate experimental route (see
`TerminalCut.lean`).

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.J2ResidualOperator
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TerminalOwner

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. The single missing exact bridge -/

/-- **`epM2Realisation`** — the exact identification of the canonical centered `j = 2` residual
family `D_B` with the EP-M2 raw moment family.  MISSING EXACT BRIDGE — stated, never inhabited,
not an axiom. -/
def epM2Realisation (DB M : ℝ → ℝ) : Prop := ∀ x, DB x = M x

/-! ## 2. The bridge theorems -/

/-- **`EPM2Bound` + `epM2Realisation` ⇒ `J2ResidualCenteredBound`.** -/
theorem j2_of_epM2 {DB M : ℝ → ℝ} {S0 : ℕ} (hreal : epM2Realisation DB M)
    (hM : EPM2Bound M S0) : J2ResidualCenteredBound DB S0 :=
  scalarBudget_congr hreal hM

/-- **The full terminal route to the canonical `j = 2` owner.**  Every arrow is machine-checked;
the four hypotheses are exactly the open nodes of the route (one exact bridge, three analytic
budgets), and the conclusion is the *existing* canonical owner, not a new one. -/
theorem j2_of_terminal_route {DB M Mtop Cross Mlow : ℝ → ℝ} {S0 : ℕ}
    (hreal : epM2Realisation DB M)
    (hsplit : ∀ x, M x = Mtop x + 2 * Cross x + Mlow x)
    (htop : EPM2TopBound Mtop S0) (hcross : CrossTermBudget Cross S0)
    (hlow : LowRamanujanBudget Mlow S0) :
    J2ResidualCenteredBound DB S0 :=
  j2_of_epM2 hreal (epM2_of_terminal_parts hsplit htop hcross hlow)

/-- The terminal route, continued along the pre-existing adapter, to the raw `j = 2` operator
budget.  This is the full chain `canonical root → j = 2 → EP-M2 → EP-M2-top`, read upwards. -/
theorem dbRaw_budget_of_terminal_route {Raw Cen Prin M Mtop Cross Mlow : ℝ → ℝ} {S0 : ℕ}
    (hrawsplit : ∀ x, Raw x = Cen x + Prin x)
    (hreal : epM2Realisation Cen M)
    (hsplit : ∀ x, M x = Mtop x + 2 * Cross x + Mlow x)
    (htop : EPM2TopBound Mtop S0) (hcross : CrossTermBudget Cross S0)
    (hlow : LowRamanujanBudget Mlow S0) (hP : ScalarBudget Prin (S0 + 2)) :
    ScalarBudget Raw (S0 + 2) :=
  raw_budget_of_centered_and_principal hrawsplit
    (j2_of_terminal_route hreal hsplit htop hcross hlow) hP

/-! ## 3. What the route does *not* prove -/

/-- **The exact realisation is load-bearing.**  Even a fully budgeted EP-M2 moment family says
nothing about an unrelated `j = 2` family: without `epM2Realisation` the bridge fails. -/
theorem epM2Realisation_load_bearing :
    ∃ DB M : ℝ → ℝ, EPM2Bound M 0 ∧ ¬ J2ResidualCenteredBound DB 0 :=
  ⟨fun x => x, fun _ => 0, zero_budgeted 2, identity_not_budgeted 1⟩

/-- **The canonical `j = 2` owner is not discharged.**  `J2ResidualCenteredBound` is not a
theorem: there are families violating it, so the route above is conditional and the owner
stays open. -/
theorem j2_owner_still_open : ∃ DB : ℝ → ℝ, ¬ J2ResidualCenteredBound DB 0 :=
  ⟨fun x => x, identity_not_budgeted 1⟩

/-- **The terminal owner is not discharged either.**  `EPM2TopBound` is not a theorem. -/
theorem terminal_owner_still_open : ∃ Mtop : ℝ → ℝ, ¬ EPM2TopBound Mtop 0 :=
  ⟨fun x => x, identity_not_budgeted 1⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
