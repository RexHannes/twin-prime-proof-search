/-
# Universal safe algebra — status and axiom audit

`#print axioms` on every principal declaration of this layer (the re-exported UniversalV8
theorems are audited in `UniversalV8/Status.lean`; audited here are the declarations that
are new in `Universal/SafeAlgebra`).
-/
import Universal.SafeAlgebra.FiniteAbel
import Universal.SafeAlgebra.DiscreteVariation
import Universal.SafeAlgebra.SynthesisBudget
import Universal.SafeAlgebra.Gram
import Universal.SafeAlgebra.WeightedSchur
import Universal.SafeAlgebra.OpenChain
import Universal.SafeAlgebra.DefectCapacity
import Universal.SafeAlgebra.Counterexamples
import Universal.SafeAlgebra.ExponentLedger
import Universal.SafeAlgebra.Interfaces

namespace Universal.SafeAlgebra.Status

#print axioms Universal.SafeAlgebra.backendDualNorm_discreteBV
#print axioms Universal.SafeAlgebra.variation_indicator_le
#print axioms Universal.SafeAlgebra.weightedBlockSchur
#print axioms Universal.SafeAlgebra.openChain_two
#print axioms Universal.SafeAlgebra.closedCycle_trace_invariant
#print axioms Universal.SafeAlgebra.closedCycle_sign_telescopes

end Universal.SafeAlgebra.Status
