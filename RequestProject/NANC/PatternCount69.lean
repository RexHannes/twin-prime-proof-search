import RequestProject.Options
-- Repair (Universal v8 safe-bank audit): the two finite counts below were originally
-- discharged by `native_decide`.  They are now discharged by the kernel-checked `decide`,
-- so the whole project uses no `native_decide` anywhere.
namespace TwinPrimeProject.NANC
open scoped BigOperators

theorem rough_dimension_pair_count :
    (Finset.Icc 0 3 ×ˢ Finset.Icc 0 3).card = 16 := by decide

theorem labelled_rough_assignment_count :
    ∑ j ∈ Finset.range 4, ∑ k ∈ Finset.range 4, Nat.choose (j+k) j = 69 := by decide

theorem labelled_rough_assignment_row_breakdown : 4 + 10 + 20 + 35 = 69 := by norm_num
end NANC
