/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : the bridge back to EP-M2  (J11)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted; no analytic
proposition is inhabited.

The chain assembled here is

```
JCoreOffCleanBound + SourceCoreOverlapBudget + JCoreEqualBudget   (analytic, all open)
      ⇒ JCoreBound                                                (Owners.lean)
JCoreBound + jCoreMomentRealisation                               (exact identification, OPEN)
      ⇒ EPM2TopBound                                              (proved here)
      ⇒ EPM2Bound        (with the banked cross/low budgets)      (banked)
      ⇒ J2ResidualCenteredBound  (for the realised EP-M2 data)    (RowIdentification.lean)
```

Exactly one exact identification is missing on this route: `jCoreMomentRealisation`, the
statement that the EP-M2 terminal moment family *is* the JCORE moment family.  It is a
proposition, never inhabited, not an axiom, and is proved load-bearing in §3.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.RowIdentification
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.Owners

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

/-! ## 1. The one missing exact identification -/

/-- **`jCoreMomentRealisation`** — the exact identification of the EP-M2 terminal moment family
with the JCORE moment family.  MISSING EXACT BRIDGE — stated, never inhabited, not an axiom. -/
def jCoreMomentRealisation (Mtop J : ℝ → ℝ) : Prop := ∀ x, Mtop x = J x

/-! ## 2. The bridge -/

/-- **`JCoreBound` + `jCoreMomentRealisation` ⇒ `EPM2TopBound`.** -/
theorem epM2TopBound_of_jCore {Mtop J : ℝ → ℝ} {S0 : ℕ}
    (hreal : jCoreMomentRealisation Mtop J) (hJ : JCoreBound J S0) : EPM2TopBound Mtop S0 :=
  scalarBudget_congr hreal hJ

/-- **The JCORE route to `EPM2Bound`.**  The terminal EP-M2 owner is replaced by the three JCORE
owners; the cross-term and low-band budgets are the banked ones. -/
theorem epM2Bound_of_jCore_owners {M Mtop Cross Mlow J JEq JCl JOv : ℝ → ℝ} {S0 : ℕ}
    (hsplit : ∀ x, M x = Mtop x + 2 * Cross x + Mlow x)
    (hreal : jCoreMomentRealisation Mtop J)
    (hjsplit : ∀ x, J x = JEq x + JCl x + JOv x)
    (heq : JCoreEqualBudget JEq S0) (hcl : JCoreOffCleanBound JCl S0)
    (hov : SourceCoreOverlapBudget JOv S0)
    (hcross : CrossTermBudget Cross S0) (hlow : LowRamanujanBudget Mlow S0) :
    EPM2Bound M S0 :=
  epM2_of_terminal_parts hsplit
    (epM2TopBound_of_jCore hreal (jCoreBound_of_owners hjsplit heq hcl hov)) hcross hlow

/-- **The full advertised chain, for the realised EP-M2 data.**  Because the row identification
is discharged in `RowIdentification.lean`, this reaches the *existing* canonical `j = 2` owner
with no exact bridge left between EP-M2 and canonical `j = 2`; the only exact bridge remaining on
the route is `jCoreMomentRealisation`, and the only analytic inputs are the three JCORE owners
plus the two banked EP-M2 budgets. -/
theorem j2_of_jCore_route (I : Cutoffs) (Z : Finset ℕ) (beta5 W : ℕ → ℝ) (E0 S0 : Finset ℕ)
    {Mtop Cross Mlow J JEq JCl JOv : ℝ → ℝ} {S0' : ℕ}
    (hsplit : ∀ x, (rowDataClosed I Z beta5 W E0 S0).epM2Family x
      = Mtop x + 2 * Cross x + Mlow x)
    (hreal : jCoreMomentRealisation Mtop J)
    (hjsplit : ∀ x, J x = JEq x + JCl x + JOv x)
    (heq : JCoreEqualBudget JEq S0') (hcl : JCoreOffCleanBound JCl S0')
    (hov : SourceCoreOverlapBudget JOv S0')
    (hcross : CrossTermBudget Cross S0') (hlow : LowRamanujanBudget Mlow S0') :
    J2ResidualCenteredBound (rowDataClosed I Z beta5 W E0 S0).canonicalFamily S0' :=
  j2_of_epM2Bound_rowDataClosed I Z beta5 W E0 S0
    (epM2Bound_of_jCore_owners hsplit hreal hjsplit heq hcl hov hcross hlow)

/-! ## 3. What the bridge does *not* prove -/

/-- **`jCoreMomentRealisation` is load-bearing**: a budgeted JCORE family says nothing about an
unrelated EP-M2 terminal family. -/
theorem jCoreMomentRealisation_load_bearing :
    ∃ Mtop J : ℝ → ℝ, JCoreBound J 0 ∧ ¬ EPM2TopBound Mtop 0 :=
  ⟨fun x => x, fun _ => 0, zero_budgeted 2, identity_not_budgeted 1⟩

/-- **The route closes no owner.**  `JCoreOffCleanBound`, `EPM2TopBound` and
`J2ResidualCenteredBound` all remain refutable by explicit families. -/
theorem jCore_route_closes_no_owner :
    (∃ JCl : ℝ → ℝ, ¬ JCoreOffCleanBound JCl 0)
      ∧ (∃ Mtop : ℝ → ℝ, ¬ EPM2TopBound Mtop 0)
      ∧ (∃ DB : ℝ → ℝ, ¬ J2ResidualCenteredBound DB 0) :=
  ⟨jCoreOffCleanBound_open, terminal_owner_still_open, j2_owner_still_open⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
