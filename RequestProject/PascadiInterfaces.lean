import Mathlib
import RequestProject.Status

/-!
# Explicit source interfaces

The mandatory source audit was not supplied with this task.  Consequently this
file does not guess Proposition 4.4 or 6.3.  It supplies proposition-valued,
explicit-argument interfaces that can be instantiated only after an exact
source transcription is available.  No global inhabitant is defined.
-/

namespace HighP3

/-- Exact-source wrapper.  Supplying a value is supplying the source theorem;
the wrapper itself is not a kernel proof of that analytic theorem. -/
structure PascadiProp44Input (hypotheses conclusion : Prop) : Prop where
  source_hypotheses : hypotheses
  source_conclusion : hypotheses → conclusion

/-- `PASCADI_PROP_4_4_INTERFACE` (`CONDITIONAL_INTERFACE`). -/
theorem PASCADI_PROP_4_4_INTERFACE {hypotheses conclusion : Prop}
    (hPas : PascadiProp44Input hypotheses conclusion) : conclusion :=
  hPas.source_conclusion hPas.source_hypotheses

/-- Conditional wrapper for the source theorem behind Proposition 6.3. -/
structure PascadiProp63Input (hypotheses conclusion : Prop) : Prop where
  source_hypotheses : hypotheses
  source_conclusion : hypotheses → conclusion

/-- The source application remains explicitly conditional. -/
theorem PASCADI_PROP_6_3_INTERFACE {hypotheses conclusion : Prop}
    (hPas : PascadiProp63Input hypotheses conclusion) : conclusion :=
  hPas.source_conclusion hPas.source_hypotheses

/-- A candidate conductor-preserving residual theorem must specify its
coefficient class, ranges, norms, gcd restrictions, cancellation condition and
packet implication.  This record is an `OPEN_INPUT`, not an inhabitant. -/
structure ConductorPreservingP3ReductionInput
    (CoefficientClass Ranges NormBounds GCDConditions CancellationCondition
      ResidualPacketConclusion : Prop) : Prop where
  coefficient_class : CoefficientClass
  exact_ranges : Ranges
  coefficient_norms : NormBounds
  gcd_conditions : GCDConditions
  zero_or_main_term_condition : CancellationCondition
  residual_packet_implication :
    CoefficientClass → Ranges → NormBounds → GCDConditions →
      CancellationCondition → ResidualPacketConclusion

/-- `CONDUCTOR_PRESERVING_P3_REDUCTION` (`CONDITIONAL_INTERFACE` only): an
explicit candidate input implies its stated residual packet conclusion.  The
existence of such an input remains `OPEN_INPUT`. -/
theorem CONDUCTOR_PRESERVING_P3_REDUCTION_INTERFACE
    {CoefficientClass Ranges NormBounds GCDConditions CancellationCondition
      ResidualPacketConclusion : Prop}
    (h : ConductorPreservingP3ReductionInput CoefficientClass Ranges NormBounds
      GCDConditions CancellationCondition ResidualPacketConclusion) :
    ResidualPacketConclusion :=
  h.residual_packet_implication h.coefficient_class h.exact_ranges
    h.coefficient_norms h.gcd_conditions h.zero_or_main_term_condition

end HighP3
