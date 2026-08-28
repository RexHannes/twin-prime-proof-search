/-
# Gate 1B v13 — counterguards A–H

**Status: all kernel-checked.**

Each guard blocks one silent upgrade that the v13 material could otherwise
invite:

* **A** the same-`q` diagonal is not automatically negligible;
* **B** the modular-hyperbola discrepancy interface is not vacuous;
* **C** `ℓ² ≤ ℓ¹` is not a saving — the two masses can coincide;
* **D** edge-dependent weights are not absorbed by a common-weight theorem;
* **E** four Cauchy copies are not four independent physical parameters;
* **F** a conditional compiler is not a closure;
* **G** the FM → Gate census is source-blocked;
* **H** SHAPE metadata does not transport from the determinant to the trace.
-/
import Gate1B.SafeExtensions.QK56ConditionalClosure
import Gate1B.SafeExtensions.ShiftTTStarLiteralSource
import Gate1B.SafeExtensions.FMToGateCoordinateCensus
import Universal.SafeAlgebra.WeightDependenceCompiler

namespace Gate1B.SafeExtensions

open Finset Gate1B.SafeAlgebra TwinPrimeProject.Gate1BV11

/-- **Guard A.**  With a flat kernel and a nonzero coefficient the same-`q`
diagonal is nonzero: it cannot be discarded without an analytic input. -/
theorem v13_guardA_diagonal_not_negligible
    {Ch : Type*} [Fintype Ch] [DecidableEq Ch] [CommGroup Ch]
    (c : Ch → ℂ) (x0 : Ch) (hx0 : c x0 ≠ 0) :
    sameQGramDiag c (fun _ => 1) ≠ 0 :=
  sameQGramDiag_ne_zero_of_flat_kernel c x0 hx0

/-- **Guard B.**  The discrepancy interface is not vacuous. -/
theorem v13_guardB_discrepancy_not_vacuous
    {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G] [Nonempty G] (u v : G → ℂ) :
    ¬ ModularHyperbolaDiscrepancyInput u v (-1) :=
  modularHyperbolaDiscrepancyInput_not_vacuous u v

/-- **Guard C.**  The comparison `‖A‖₂ ≤ ‖A‖₁` is not a saving: on a
one-point source the two masses are equal, so no spread constant `ρ < 1` is
automatic. -/
theorem v13_guardC_l2_eq_l1_possible :
    crossL2 (fun _ : Unit => (1 : ℂ)) = crossL1 (fun _ : Unit => (1 : ℂ)) := by
  unfold crossL1 crossL2
  simp

/-- **Guard D.**  A non-constant weight is not absorbed by a common-weight
statement. -/
theorem v13_guardD_edgeDependent_not_common :
    ¬ ∃ c : ℂ, ∀ f : Bool → ℂ,
        Universal.SafeAlgebra.packetSum (fun e => if e then 1 else 0) f
          = c * ∑ e : Bool, f e :=
  Universal.SafeAlgebra.edgeDependent_not_absorbed_by_common

/-- **Guard E.**  Four Cauchy copies are not four independent physical
parameters. -/
theorem v13_guardE_fourCopies_ne_fourParameters :
    quadMoment fullCube * diagonalSource.card
      ≠ quadMoment diagonalSource * fullCube.card :=
  fourCopies_ne_fourIndependentParameters

/-- **Guard F.**  A conditional analytic compiler is not a closure: the QK5/6
conclusion is not automatic. -/
theorem v13_guardF_conditional_is_not_closure :
    ¬ QK56FullCovarianceBound (fun _ => 2) 1 qkLowerEndpointSaving :=
  qk56FullCovarianceBound_not_automatic

/-- **Guard G.**  The FM → Gate census is blocked at the literal Ford
provenance certificate. -/
theorem v13_guardG_census_source_blocked {E : Type}
    (h : Nonempty (FMToGateCoordinateCensus E)) :
    Nonempty TwinPrimeProject.Gate1BV11.RealFordGrammarCertificate :=
  census_requires_fordProvenance h

/-- **Guard H.**  SHAPE metadata does not transport from the four-cycle
determinant to the four-cycle trace. -/
theorem v13_guardH_shape_not_transportable :
    ¬ DeterminantCharacterShape
        (fun a1 a2 a3 a4 : ℤ => Matrix.trace (cycleMatrix a1 a2 a3 a4 0 0 0 0)) :=
  fourCycle_trace_not_determinantShape

end Gate1B.SafeExtensions
