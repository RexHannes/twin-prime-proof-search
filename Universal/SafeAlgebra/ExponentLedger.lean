/-
# Universal safe algebra — rational exponent ledger (re-export)

Exact `ℚ` arithmetic only, proved in `Gate1A/SafeAlgebra/BPExponentRepair.lean` and
`Gate1B/SafeAlgebra/NPLBudget.lean`.  No real powers, no floating point, no asymptotics.
-/
import Gate1A.SafeAlgebra.BPExponentRepair
import Gate1B.SafeAlgebra.NPLBudget

namespace Universal.SafeAlgebra

export Gate1A.SafeAlgebra (sigmaExp rhoExp tauExp bp_vertex1_energy bp_vertex1_surplus
  bp_vertex2_energy bp_vertex2_surplus bp_vertex3_energy bp_vertex3_surplus
  bp_worst_energy_surplus bp_worstEnergyMargin bp_amplitudeTaxMargin)

export Gate1B.SafeAlgebra (uExp vExp rExp u_add_v omega_add_r v_gt_u
  nearPrimitiveNoWrapExponent diagonal_exponent_identity gate1B_R_exponent_lower
  npl_diagonal_saving_floor gate1B_diagSavingExponent npl_diagonal_saving_endpoint
  X_div_Q_eq_R npl_allowedCongestion)

end Universal.SafeAlgebra
