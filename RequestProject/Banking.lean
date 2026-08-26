import RequestProject.Status
import RequestProject.Parameters
import RequestProject.Wedge206274
import RequestProject.Wedge122162
import RequestProject.SectorPartition
import RequestProject.WrightExponentAudit
import RequestProject.DoubleCrossArithmetic
import RequestProject.MesoscopicParameters
import RequestProject.RoutingThreshold
import RequestProject.FixedDepthConvolution
import RequestProject.FixedDepthRouting
import RequestProject.F1Migration
import RequestProject.DependencyInterfaces
import RequestProject.FordMaynardInterface
import RequestProject.OuterHierarchyArithmetic
import RequestProject.F1GlobalCentering
import RequestProject.CharacterExpansion
import RequestProject.F2DoubleMellinStatus
import RequestProject.ReciprocalTensorExponents
import RequestProject.F2SectorLedger
import RequestProject.FullTypeIIStatus
import RequestProject.CollisionSector
import RequestProject.CenteredCRTRootNormalForm

/-!
# Shifted Möbius Type-II / F3 (r = 2) — master banking module

This file is the top-level aggregator of the consolidated ledger.  It imports the
modular files (status taxonomy, parameter algebra, wedge inequalities, Wright
exponent audit, sector partition, double-cross arithmetic, mesoscopic product
bound, and analytic interfaces) and preserves the historical interface layer from
the previous Aristotle run, now marked `SUPERSEDED_BY_LATER_AUDIT`.

Everything here is kernel-checked.  Deep analytic estimates are represented by
explicit hypotheses / structure fields (`DependencyInterfaces.AnalyticInputs`),
never by axioms, `sorry`, `admit`, or `implemented_by`.
-/

namespace ShiftedMobiusBank

/-! ## Historical interface layer (SUPERSEDED_BY_LATER_AUDIT)

The following declarations reproduce the previous Aristotle run's interface layer,
whose *analytic status labels* (diagonal / double-cross / KF-wedge only
conditional, `F3_R2_PARTIALLY_KILLED` not claimed) have since been superseded by
later hostile audits.  The Lean content itself remains valid and is retained for
provenance; the updated statuses live in `Status.ledger`. -/
namespace Superseded

/-- (Superseded) hypothesis package for the corrected conductor window. -/
structure CWWindowHyp where
  X : ℝ
  U : ℝ
  W : ℝ
  B0 : ℝ
  eps0 : ℝ
  Y : ℝ
  hX : 1 < X
  hU : U ≤ X ^ (1 / 2 : ℝ) * (Real.log X) ^ (-B0)
  hW : X ^ (1 / 2 : ℝ) * (Real.log X) ^ B0 ≤ W
  hY : X ^ eps0 ≤ Y
  smoothVWindow : Prop
  genuineUSideMuBlock : Prop
  divisorBoundedAlphaBeta : Prop
  hsmooth : smoothVWindow
  hmu : genuineUSideMuBlock
  hdiv : divisorBoundedAlphaBeta

/-- (Superseded) abstract claim propositions. -/
structure Claims where
  CW_mu_powerSaving : CWWindowHyp → Prop
  F3_R2_original : Prop
  F3_R2_BD_form : Prop
  mainTermBound : Prop
  lowMidConductorBound : Prop
  offdiagCrossCoprimeBound : Prop
  actualDiagonalBound : Prop
  doubleCrossGCDBound : Prop
  actualKFTinyWedgeBound : Prop

/-- (Superseded) outside analytic inputs. -/
structure AnalyticImports (C : Claims) where
  corrected_CW_mu : ∀ h : CWWindowHyp, C.CW_mu_powerSaving h
  F3_R2_reduction : C.F3_R2_original → C.F3_R2_BD_form
  zeroFreeMobius_mainTerm : C.F3_R2_BD_form → C.mainTermBound
  largeSieve_lowMid : C.F3_R2_BD_form → C.lowMidConductorBound
  bettinChandee_crossCoprime : C.F3_R2_BD_form → C.offdiagCrossCoprimeBound

theorem CW_mu_window {C : Claims} (I : AnalyticImports C) (h : CWWindowHyp) :
    C.CW_mu_powerSaving h := I.corrected_CW_mu h

theorem F3_R2_BD_reduction {C : Claims} (I : AnalyticImports C)
    (h : C.F3_R2_original) : C.F3_R2_BD_form := I.F3_R2_reduction h

theorem MainTermKilled {C : Claims} (I : AnalyticImports C)
    (h : C.F3_R2_BD_form) : C.mainTermBound := I.zeroFreeMobius_mainTerm h

theorem LowMidConductorsControlled {C : Claims} (I : AnalyticImports C)
    (h : C.F3_R2_BD_form) : C.lowMidConductorBound := I.largeSieve_lowMid h

theorem OffdiagCrossCoprime {C : Claims} (I : AnalyticImports C)
    (h : C.F3_R2_BD_form) : C.offdiagCrossCoprimeBound :=
  I.bettinChandee_crossCoprime h

theorem ActualDiagonal {C : Claims}
    (centeredSquareAudit : C.F3_R2_BD_form → C.actualDiagonalBound)
    (h : C.F3_R2_BD_form) : C.actualDiagonalBound := centeredSquareAudit h

theorem DoubleCrossGCD {C : Claims}
    (sparseBettinChandeeAudit : C.F3_R2_BD_form → C.doubleCrossGCDBound)
    (h : C.F3_R2_BD_form) : C.doubleCrossGCDBound := sparseBettinChandeeAudit h

theorem ActualKFTinyWedge {C : Claims}
    (assemble : C.F3_R2_BD_form → C.mainTermBound →
      C.lowMidConductorBound → C.offdiagCrossCoprimeBound →
      C.actualDiagonalBound → C.doubleCrossGCDBound →
      C.actualKFTinyWedgeBound)
    (hBD : C.F3_R2_BD_form) (hMain : C.mainTermBound)
    (hLM : C.lowMidConductorBound) (hCross : C.offdiagCrossCoprimeBound)
    (hDiag : C.actualDiagonalBound) (hDouble : C.doubleCrossGCDBound) :
    C.actualKFTinyWedgeBound :=
  assemble hBD hMain hLM hCross hDiag hDouble

end Superseded

/-! ## Sanity check: the machine-checked algebra is discharged unconditionally.

This theorem re-exports the key kernel-checked facts of the updated ledger, so
that building `Banking` witnesses that the parameter algebra, Wright exponents,
sector partition, double-cross coprimality, and finite-product bound all hold. -/
theorem banking_algebra_summary (p : Params) (hWedge : newWedge p) :
    (oldWedge p → newWedge p) ∧
    0 < gap p ∧
    2 * sigmaSplit p + 2 * p.mu ≤ 1 / 5 := by
  refine ⟨wedge_containment_206_implies_122 p, gap_pos p hWedge, fixed_factor_le p⟩

/-! ## New in this update: fixed-depth routing summary.

Re-exports the machine-checked routing content of this update: the routing
threshold equivalence, the fixed-depth convolution reindexing, and the honest
status distinction (routable ⇸ full). -/
theorem banking_routing_summary (mu w : ℝ) :
    (122 * mu + 162 * thetaOfW w < 1 ↔ w > wStar mu) ∧
    (∃ S : StrengthLevels,
      S.fixedDepthRoutable ∧ ¬ S.fullF3 ∧
      S.longMobiusF1Routable ∧ ¬ S.fullF1Migration ∧
      S.highConductorPowerSaving ∧ ¬ S.fullPiecePowerSaving) :=
  ⟨block_routable_iff mu w, status_distinctions_consistent⟩

end ShiftedMobiusBank
