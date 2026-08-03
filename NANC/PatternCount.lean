import Mathlib

namespace NANC

 theorem rough_dimension_pair_count :
    ((Finset.range 4).product (Finset.range 4)).card = 16 := by native_decide

 theorem labelled_rough_assignment_count :
    (∑ j ∈ Finset.range 4, ∑ k ∈ Finset.range 4, Nat.choose (j + k) j) = 69 := by
  norm_num [Finset.sum_range_succ, Nat.choose]

 theorem labelled_rough_assignment_breakdown : 4 + 10 + 20 + 35 = 69 := by norm_num

end NANC
