import Mathlib

namespace TwinPrimeProject.NANC.D4

/-! These are source/analytic obligations, not proved declarations.
No global inhabitant is supplied for any interface. -/

structure Prop44SourceFidelity where
  exponentConditionsMatchSource : Prop
  roughnessHypothesis : Prop
  siegelWalfiszHypothesis : Prop

structure PacketExponentDictionary where
  packetType : Type
  exponents : packetType → ℚ × ℚ × ℚ × ℚ

structure FordMaynardCoefficientDictionary where
  statement : Prop

structure PascadiTheorem3Interface where
  statement : Prop

structure RouteACompletionInterface where
  sourcePhase : Prop
  completionFormula : Prop
  completionPrefactor : Prop
  BRange : Prop
  rawTargetEquivalence : Prop

structure RouteATheoremA4 where
  statement : Prop

/-- Interface-only obligations for the cited corollaries. -/
structure PascadiCorollaries16And17Interface where
  corollary16 : Prop
  corollary17 : Prop

/-- Interface-only full-conductor directional analytic bound. -/
structure FullCDirectionalAnalyticBound where
  statement : Prop

/-- Interface-only generic D4 assertion. -/
structure GenericD4InterfaceRouteAB where
  statement : Prop

end TwinPrimeProject.NANC.D4
