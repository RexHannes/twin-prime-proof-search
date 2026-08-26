import RequestProject.EqualCellFiniteDifference

namespace HalfSieve

noncomputable section

def linearKernelRat (t : ℚ) : ℚ := 1 - 2 * t

lemma linearKernel_C2 : equalCellCoeff 2 linearKernelRat = 1 := by
  norm_num [equalCellCoeff, linearKernelRat, Finset.sum_range_succ, Nat.choose]

lemma linearKernel_C4 : equalCellCoeff 4 linearKernelRat = -1 := by
  norm_num [equalCellCoeff, linearKernelRat, Finset.sum_range_succ, Nat.choose]

lemma linearKernel_C6 : equalCellCoeff 6 linearKernelRat = 2 := by
  norm_num [equalCellCoeff, linearKernelRat, Finset.sum_range_succ, Nat.choose]

lemma linearKernel_C8 : equalCellCoeff 8 linearKernelRat = -5 := by
  norm_num [equalCellCoeff, linearKernelRat, Finset.sum_range_succ, Nat.choose]

lemma linearKernel_C10 : equalCellCoeff 10 linearKernelRat = 14 := by
  norm_num [equalCellCoeff, linearKernelRat, Finset.sum_range_succ, Nat.choose]

lemma linearKernel_C12 : equalCellCoeff 12 linearKernelRat = -42 := by
  norm_num [equalCellCoeff, linearKernelRat, Finset.sum_range_succ, Nat.choose]

end

end HalfSieve
