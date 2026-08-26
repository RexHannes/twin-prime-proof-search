/-
# Universal safe algebra — defect capacity (re-export)

Proved in `UniversalV8/DefectCapacity.lean`.  Multiplicative divisibility bound; the
logarithmic form is a corollary.  This does NOT control source-weighted Gram congestion.
-/
import UniversalV8.DefectCapacity

namespace Universal.SafeAlgebra

export UniversalV8 (nat_prod_dvd_of_pairwiseCoprime defectValuation_product_le
  defectCapacity pow_card_le_of_pairwiseCoprime_product_dvd defectCapacity_pow
  defectCapacity_log)

end Universal.SafeAlgebra
