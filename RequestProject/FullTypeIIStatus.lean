import Mathlib

/-! Explicit F1/F2/F3 dependency graph as propositions and arrows. -/

namespace ShiftedMobiusBank

structure TypeIIDependencyClaims where
  f1GlobalCentering : Prop
  comparisonSequenceAxioms : Prop
  f1AggregateOffDiagonal : Prop
  fullF1 : Prop
  fullF2 : Prop
  fullF3 : Prop
  uniformProjectTypeII : Prop
  fordTransference : Prop
  positivityGate : Prop

/-- Final assembly remains conditional on all three full families and on a
separate transference theorem. -/
theorem full_typeII_dependency (C : TypeIIDependencyClaims)
    (assembleTypeII : C.fullF1 → C.fullF2 → C.fullF3 → C.uniformProjectTypeII)
    (transfer : C.uniformProjectTypeII → C.fordTransference)
    (positivity : C.fordTransference → C.positivityGate)
    (hF1 : C.fullF1) (hF2 : C.fullF2) (hF3 : C.fullF3) : C.positivityGate :=
  positivity (transfer (assembleTypeII hF1 hF2 hF3))

end ShiftedMobiusBank
