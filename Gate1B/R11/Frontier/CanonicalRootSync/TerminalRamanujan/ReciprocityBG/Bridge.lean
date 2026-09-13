/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
the bridge back to EP-M2 and to the canonical `j = 2` owner  (B10)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted; the canonical
owner `J2ResidualCenteredBound` is **not** discharged.

Every arrow below is machine-checked.  The hypotheses are exactly the open nodes:

```
LowDualBourgainGaraevBound (external, open)
HighDualJointAverageBound  (external, open)
CrossTermBudget            (banked, open)
   + exact dual identifications (low band = low dual row, top band = high dual row)
      ⇒ EPM2Bound                                            (proved here)
EPM2Bound + epM2Realisation (exact, open — reduced in `Realisation.lean`
                             to the single sub-bridge `epM2RowIdentification`)
      ⇒ J2ResidualCenteredBound                              (pre-existing arrow)
```

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.PowerBudget

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. Dual owners ⇒ EP-M2 -/

/-- **The dual-frequency route to `EPM2Bound`.**  The low band is owned by the external
low-frequency proposition, the terminal band by the high-frequency joint average, and the cross
term by the pre-existing banked budget. -/
theorem epM2Bound_of_dual_owners {D : DualData} {M Mtop Cross Mlow : ℝ → ℝ} {S0 : ℕ}
    (hsplit : ∀ x, M x = Mtop x + 2 * Cross x + Mlow x)
    (hlowid : ∀ x, Mlow x = lowBGRow D x) (htopid : ∀ x, Mtop x = highBGRow D x)
    (hbg : LowDualBourgainGaraevBound D S0) (hhigh : HighDualJointAverageBound D S0)
    (hcross : CrossTermBudget Cross S0) :
    EPM2Bound M S0 :=
  epM2_of_terminal_parts hsplit (epM2TopBound_of_high htopid hhigh) hcross
    (lowDualBudget_of_bg hlowid hbg)

/-! ## 2. Dual owners + the exact realisation ⇒ the canonical `j = 2` owner -/

/-- **The full route to the canonical `j = 2` owner.**  Conditional on the two external
frequency owners, the banked cross-term budget and the exact identification `epM2Realisation`. -/
theorem j2_of_dual_owners {D : DualData} {DB M Mtop Cross Mlow : ℝ → ℝ} {S0 : ℕ}
    (hreal : epM2Realisation DB M)
    (hsplit : ∀ x, M x = Mtop x + 2 * Cross x + Mlow x)
    (hlowid : ∀ x, Mlow x = lowBGRow D x) (htopid : ∀ x, Mtop x = highBGRow D x)
    (hbg : LowDualBourgainGaraevBound D S0) (hhigh : HighDualJointAverageBound D S0)
    (hcross : CrossTermBudget Cross S0) :
    J2ResidualCenteredBound DB S0 :=
  j2_of_epM2 hreal (epM2Bound_of_dual_owners hsplit hlowid htopid hbg hhigh hcross)

/-- **The same route with the realisation replaced by its exact sub-bridges.**  The only
realisation input is the chart bookkeeping plus the single missing identification
`epM2RowIdentification`; everything else is kernel-proved. -/
theorem j2_of_subBridges_and_dual_owners {Dr : RealisationData} {D : DualData}
    {Mtop Cross Mlow : ℝ → ℝ} {S0 : ℕ}
    (hidx : indexSetRealisation Dr) (hinj : chartInjectivity Dr) (hmask : maskRealisation Dr)
    (hsupp : sourceSupportRealisation Dr) (hw : sourceWeightRealisation Dr)
    (hnrm : normalisationRealisation Dr) (hrow : epM2RowIdentification Dr)
    (hsplit : ∀ x, Dr.epM2Family x = Mtop x + 2 * Cross x + Mlow x)
    (hlowid : ∀ x, Mlow x = lowBGRow D x) (htopid : ∀ x, Mtop x = highBGRow D x)
    (hbg : LowDualBourgainGaraevBound D S0) (hhigh : HighDualJointAverageBound D S0)
    (hcross : CrossTermBudget Cross S0) :
    J2ResidualCenteredBound Dr.canonicalFamily S0 :=
  j2_of_dual_owners (epM2Realisation_of_subBridges hidx hinj hmask hsupp hw hnrm hrow)
    hsplit hlowid htopid hbg hhigh hcross

/-! ## 3. Every hypothesis of the bridge is load-bearing -/

/-- The bridge does not discharge the canonical owner: it is still refuted by explicit
families, so the canonical cut is unchanged. -/
theorem bridge_does_not_close_j2 : ∃ DB : ℝ → ℝ, ¬ J2ResidualCenteredBound DB 0 :=
  j2_owner_still_open

/-- The two frequency owners are both open, and the exact identification is load-bearing. -/
theorem bridge_open_nodes :
    (∃ D : DualData, ¬ LowDualBourgainGaraevBound D 0)
      ∧ (∃ D : DualData, ¬ HighDualJointAverageBound D 0)
      ∧ (∃ DB M : ℝ → ℝ, EPM2Bound M 0 ∧ ¬ J2ResidualCenteredBound DB 0) :=
  ⟨lowDualBourgainGaraevBound_open, highDualJointAverageBound_open,
    epM2Realisation_load_bearing⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
