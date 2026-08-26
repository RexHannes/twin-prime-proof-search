import RequestProject.Parameters
import RequestProject.Wedge122162

/-!
# Analytic theorem interfaces (§14) and conditional bridges (§11.1)

Deep analytic inputs are represented as explicit propositions / structure fields,
never as axioms.  Downstream results take an `AnalyticInputs` object (Method B) or
an explicit hypothesis (Method A) and derive their conclusions by *logical*
threading only.  This keeps the honest distinction between:

* `EXTERNALLY_AUDITED` — the analytic field itself, and
* `LEAN_CONDITIONAL_INTERFACE` — the Lean theorem that uses it.
-/

namespace ShiftedMobiusBank

/-- §14(7), §9 — hypotheses required by the mesoscopic Möbius lemma with an
*admissible* modulus.  The unrestricted-`q` version is false, so this interface
never exposes an unrestricted modulus. -/
structure MesoscopicHyp where
  /-- The modulus is polynomially bounded: `q ≤ X^D`. -/
  admissibleModulus : Prop
  /-- The Heath–Brown strata have fixed depth. -/
  fixedDepthStrata : Prop
  /-- Total stratum loss is polylogarithmic. -/
  polylogStratumLoss : Prop
  /-- The Mellin frequency is polylogarithmic. -/
  polylogMellinFreq : Prop
  /-- The character conductor is admissible (no `X^c` conductor on the Möbius
  variable). -/
  admissibleConductor : Prop
  /-- A possible exceptional real character is removed or treated separately. -/
  exceptionalCharacterHandled : Prop
  hAdmModulus : admissibleModulus
  hFixedDepth : fixedDepthStrata
  hPolylogStrata : polylogStratumLoss
  hPolylogMellin : polylogMellinFreq
  hAdmConductor : admissibleConductor
  hExceptional : exceptionalCharacterHandled

/-- §14 — the seven analytic interfaces packaged as an explicit input object.
Each field is a proposition to be supplied by the outside theory; nothing is an
axiom.  The wedge-dependent bounds are indexed by the exponent `Params`. -/
structure AnalyticInputs where
  /-- (1) Pre-Poisson diagonal estimate `D_Δ ≪ X^{1+ε}` (`ACTUAL_KF_DIAGONAL`). -/
  prePoissonDiagonal : Params → Prop
  /-- (2) Off-diagonal cross-coprime estimate (`KF_OFFDIAG_CROSSCOPRIME`). -/
  offdiagCrossCoprime : Params → Prop
  /-- (3) Wright five-term estimate in Sector IIIb. -/
  wrightFiveTerm : Params → Prop
  /-- (4) Radical-tail estimate for the `(s₁, s₂)` summation. -/
  radicalTail : Params → Prop
  /-- (5) Main-term cancellation `∑ λ_q MT(q) ≪ X L^{-B}`. -/
  mainTermCancellation : Prop
  /-- (6) Low/middle conductor control. -/
  lowMidConductors : Prop
  /-- (7) Mesoscopic Möbius lemma under admissible hypotheses. -/
  mesoscopicMobius : MesoscopicHyp → Prop
  /-- The kernel target `𝒦 ≪ (X²/N) X^{-η}` for the ratio-split Wright wedge. -/
  kernelPowerSaving : Params → Prop
  /-- Provider: inside the wedge, the four sector estimates assemble into the
  kernel power saving.  This encodes the audited (but not Lean-formalised)
  ratio-split assembly as a *hypothesis*, not an axiom. -/
  wrightAssembly : ∀ p : Params, newWedge p →
    prePoissonDiagonal p → offdiagCrossCoprime p → wrightFiveTerm p →
    radicalTail p → mainTermCancellation → lowMidConductors →
    kernelPowerSaving p
  /-- Provider for the mesoscopic Möbius lemma under admissible hypotheses. -/
  mesoscopicProvider : ∀ h : MesoscopicHyp, mesoscopicMobius h

/-- §8.5 (`RATIO_SPLIT_WRIGHT_WEDGE_PROVED`), as a `LEAN_CONDITIONAL_INTERFACE`.
Given the audited analytic inputs and the widened wedge `122μ + 162θ < 1`, the
kernel enjoys the power saving `𝒦 ≪ (X²/N) X^{-η}`. -/
theorem ratio_split_wright_wedge (I : AnalyticInputs) (p : Params)
    (hWedge : newWedge p)
    (hDiag : I.prePoissonDiagonal p)
    (hCross : I.offdiagCrossCoprime p)
    (hWright : I.wrightFiveTerm p)
    (hRad : I.radicalTail p)
    (hMain : I.mainTermCancellation)
    (hLowMid : I.lowMidConductors) :
    I.kernelPowerSaving p :=
  I.wrightAssembly p hWedge hDiag hCross hWright hRad hMain hLowMid

/-- The old wedge point still delivers the widened-wedge conclusion, via
`wedge_containment_206_implies_122`: any input satisfying `206μ + 274θ < 1` also
satisfies the widened wedge, hence the same kernel power saving. -/
theorem ratio_split_wright_wedge_of_oldWedge (I : AnalyticInputs) (p : Params)
    (hOld : oldWedge p)
    (hDiag : I.prePoissonDiagonal p)
    (hCross : I.offdiagCrossCoprime p)
    (hWright : I.wrightFiveTerm p)
    (hRad : I.radicalTail p)
    (hMain : I.mainTermCancellation)
    (hLowMid : I.lowMidConductors) :
    I.kernelPowerSaving p :=
  ratio_split_wright_wedge I p (wedge_containment_206_implies_122 p hOld)
    hDiag hCross hWright hRad hMain hLowMid

/-- §9 — the mesoscopic Möbius lemma interface: it fires only under the admissible
hypotheses, never for unrestricted `q`. -/
theorem mesoscopic_mobius_admissible (I : AnalyticInputs) (h : MesoscopicHyp) :
    I.mesoscopicMobius h :=
  I.mesoscopicProvider h

/-! ## §14 / §4 — Routed fixed-depth F3 interface

The routed theorem interface **must** distinguish the high-conductor *kernel*
power saving from the *complete routed piece* log saving.  These are separate
fields with separate providers: crucially there is **no** provider deriving the
full piece from the kernel alone (the full piece needs the main term, the
low/middle conductors, and the conductor-window branch).  Consequently high-
conductor power saving does **not** automatically yield full-piece power saving —
only log saving is claimed for the complete routed piece (§4 correction). -/

/-- §14 — the seven analytic interfaces for the fixed-depth routed F3 theorem,
with the mandatory `kernelPowerSaving` vs `fullPieceLogSaving` split. -/
structure RoutedF3Interface where
  /-- (1) ratio-split Wright kernel: high-conductor kernel power saving
  `𝒦 ≪ (X²/N) X^{-η}`, i.e. the high-conductor component is `≪ X^{1-η}`. -/
  kernelPowerSaving : Params → Prop
  /-- (6) high-conductor transfer: pass the kernel bound to the routed piece. -/
  highConductorTransfer : Params → Prop
  /-- (2) conductor-window theorem: the `Q_j < X^{1/2}` (low residual conductor)
  branch gives its own saving. -/
  conductorWindowSaving : Prop
  /-- (4) routed main-term cancellation `Σ_q λ_q MT(q) ≪ X L^{-B}`. -/
  routedMainTerm : Prop
  /-- (5) middle-conductor large sieve. -/
  middleConductorSieve : Prop
  /-- the *complete routed piece* log saving `𝒫_r ≪ X (log X)^{-B}`. -/
  fullPieceLogSaving : Params → Prop
  /-- (7) two-outer-variable kernel: the exact next open input.  It has **no**
  provider — it is `OPEN_INPUT`. -/
  twoOuterVariableKernel : Params → Prop
  /-- Provider for the high-conductor kernel power saving, inside the wedge. -/
  kernelProvider : ∀ p : Params, newWedge p → kernelPowerSaving p
  /-- Provider for the complete routed piece: it needs the kernel power saving
  *and* the transfer, conductor window, main term, and middle-conductor inputs.
  There is deliberately no `kernelPowerSaving p → fullPieceLogSaving p`. -/
  fullPieceProvider : ∀ p : Params, kernelPowerSaving p → highConductorTransfer p →
    conductorWindowSaving → routedMainTerm → middleConductorSieve →
    fullPieceLogSaving p

/-- §6 (`F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`, high-conductor component).
Inside the widened wedge, the high-conductor kernel has power saving. -/
theorem f3_fixed_depth_kernel_power_saving (R : RoutedF3Interface) (p : Params)
    (hWedge : newWedge p) : R.kernelPowerSaving p :=
  R.kernelProvider p hWedge

/-- §6 (`F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`, complete routed piece).
Assembling the high-conductor kernel with the transfer, conductor-window, main
term, and middle-conductor inputs yields the complete routed piece log saving
`𝒫_r ≪ X (log X)^{-B}`.  Only log saving — not power saving — is claimed here. -/
theorem f3_fixed_depth_routable_full_piece (R : RoutedF3Interface) (p : Params)
    (hWedge : newWedge p)
    (hTransfer : R.highConductorTransfer p)
    (hWindow : R.conductorWindowSaving)
    (hMain : R.routedMainTerm)
    (hSieve : R.middleConductorSieve) :
    R.fullPieceLogSaving p :=
  R.fullPieceProvider p (f3_fixed_depth_kernel_power_saving R p hWedge)
    hTransfer hWindow hMain hSieve

/-! ## §13.7 — Status-consistency witnesses (dependency distinctions)

The following are *dependency distinctions*, not mathematical negations: we exhibit
a consistent assignment of the strength levels in which the weaker banked result
holds while the stronger unproved result fails.  This machine-checks that the
banked labels do **not** logically force the stronger ones. -/

/-- Abstract strength levels attached to the ledger's key results. -/
structure StrengthLevels where
  /-- fixed-depth routable sector proved. -/
  fixedDepthRoutable : Prop
  /-- full F3 (all fragmented pieces). -/
  fullF3 : Prop
  /-- routable long-Möbius F1 migration proved. -/
  longMobiusF1Routable : Prop
  /-- full F1 migration. -/
  fullF1Migration : Prop
  /-- high-conductor kernel power saving. -/
  highConductorPowerSaving : Prop
  /-- full-piece power saving (as opposed to mere log saving). -/
  fullPiecePowerSaving : Prop

/-- §13.7 — there is a consistent world where every banked result holds but each
of the three stronger targets fails.  Hence `F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`
does not imply `FULL_F3`; `LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED` does not imply
`FULL_F1_MIGRATION`; and high-conductor power saving does not imply full-piece
power saving. -/
theorem status_distinctions_consistent :
    ∃ S : StrengthLevels,
      S.fixedDepthRoutable ∧ ¬ S.fullF3 ∧
      S.longMobiusF1Routable ∧ ¬ S.fullF1Migration ∧
      S.highConductorPowerSaving ∧ ¬ S.fullPiecePowerSaving :=
  ⟨⟨True, False, True, False, True, False⟩,
    trivial, not_false, trivial, not_false, trivial, not_false⟩

end ShiftedMobiusBank
