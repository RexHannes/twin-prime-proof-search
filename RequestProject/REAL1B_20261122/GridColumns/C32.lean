import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_8_9_11_32 : boxUpper ⟨8, 9, 11, 32⟩ = 33817971667422783 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_11_32 : boxUpper ⟨8, 10, 11, 32⟩ = 32935502671067063 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_11_32 : boxUpper ⟨9, 10, 11, 32⟩ = 30251577267621055 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_11 : pairUpper 32 11 = 97005051606110901 := by
  have members : atPair 32 11 = [
    ⟨8, 9, 11, 32⟩,
    ⟨8, 10, 11, 32⟩,
    ⟨9, 10, 11, 32⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_11_32, box_8_10_11_32, box_9_10_11_32]
  all_goals decide +kernel

private theorem box_7_8_12_32 : boxUpper ⟨7, 8, 12, 32⟩ = 20198968326588403 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_12_32 : boxUpper ⟨7, 9, 12, 32⟩ = 23411975224186478 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_12_32 : boxUpper ⟨8, 9, 12, 32⟩ = 31931907256820242 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_12_32 : boxUpper ⟨7, 10, 12, 32⟩ = 32756816282783467 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_12_32 : boxUpper ⟨8, 10, 12, 32⟩ = 31120198871658776 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_12_32 : boxUpper ⟨9, 10, 12, 32⟩ = 28606008217724346 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_12_32 : boxUpper ⟨7, 11, 12, 32⟩ = 32223774123277488 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_12_32 : boxUpper ⟨8, 11, 12, 32⟩ = 29201656803061437 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_12 : pairUpper 32 12 = 229451305106100637 := by
  have members : atPair 32 12 = [
    ⟨7, 8, 12, 32⟩,
    ⟨7, 9, 12, 32⟩,
    ⟨8, 9, 12, 32⟩,
    ⟨7, 10, 12, 32⟩,
    ⟨8, 10, 12, 32⟩,
    ⟨9, 10, 12, 32⟩,
    ⟨7, 11, 12, 32⟩,
    ⟨8, 11, 12, 32⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_12_32, box_7_9_12_32, box_8_9_12_32, box_7_10_12_32, box_8_10_12_32, box_9_10_12_32, box_7_11_12_32, box_8_11_12_32]
  all_goals decide +kernel

private theorem box_6_7_13_32 : boxUpper ⟨6, 7, 13, 32⟩ = 23890781394793121 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_13_32 : boxUpper ⟨6, 8, 13, 32⟩ = 21589162892236764 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_13_32 : boxUpper ⟨7, 8, 13, 32⟩ = 19183204901157189 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_13_32 : boxUpper ⟨6, 9, 13, 32⟩ = 19819578087110817 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_13_32 : boxUpper ⟨7, 9, 13, 32⟩ = 22251882202462093 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_13_32 : boxUpper ⟨8, 9, 13, 32⟩ = 30369729506451553 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_13_32 : boxUpper ⟨6, 10, 13, 32⟩ = 23241709268642203 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_13_32 : boxUpper ⟨7, 10, 13, 32⟩ = 31154272417948878 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_13_32 : boxUpper ⟨8, 10, 13, 32⟩ = 29619385112045635 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_13_32 : boxUpper ⟨6, 11, 13, 32⟩ = 32852198686515027 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_13_32 : boxUpper ⟨7, 11, 13, 32⟩ = 30669723991398943 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_13_32 : boxUpper ⟨6, 12, 13, 32⟩ = 32597029380323591 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_13 : pairUpper 32 13 = 317238657841085814 := by
  have members : atPair 32 13 = [
    ⟨6, 7, 13, 32⟩,
    ⟨6, 8, 13, 32⟩,
    ⟨7, 8, 13, 32⟩,
    ⟨6, 9, 13, 32⟩,
    ⟨7, 9, 13, 32⟩,
    ⟨8, 9, 13, 32⟩,
    ⟨6, 10, 13, 32⟩,
    ⟨7, 10, 13, 32⟩,
    ⟨8, 10, 13, 32⟩,
    ⟨6, 11, 13, 32⟩,
    ⟨7, 11, 13, 32⟩,
    ⟨6, 12, 13, 32⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_13_32, box_6_8_13_32, box_7_8_13_32, box_6_9_13_32, box_7_9_13_32, box_8_9_13_32, box_6_10_13_32, box_7_10_13_32, box_8_10_13_32, box_6_11_13_32, box_7_11_13_32, box_6_12_13_32]
  all_goals decide +kernel

private theorem box_5_6_14_32 : boxUpper ⟨5, 6, 14, 32⟩ = 29711858627245777 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_14_32 : boxUpper ⟨5, 7, 14, 32⟩ = 26343586525699685 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_14_32 : boxUpper ⟨6, 7, 14, 32⟩ = 22801160332365159 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_14_32 : boxUpper ⟨5, 8, 14, 32⟩ = 23805637606786440 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_14_32 : boxUpper ⟨6, 8, 14, 32⟩ = 20617917202603466 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_14_32 : boxUpper ⟨7, 8, 14, 32⟩ = 18332767800115049 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_14_32 : boxUpper ⟨5, 9, 14, 32⟩ = 21834900808476336 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_14_32 : boxUpper ⟨6, 9, 14, 32⟩ = 18940919855695129 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_14_32 : boxUpper ⟨7, 9, 14, 32⟩ = 21282797377347019 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_14_32 : boxUpper ⟨8, 9, 14, 32⟩ = 29067410412486220 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_14_32 : boxUpper ⟨5, 10, 14, 32⟩ = 20287705597676988 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_14_32 : boxUpper ⟨6, 10, 14, 32⟩ = 22229500809531584 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_14_32 : boxUpper ⟨7, 10, 14, 32⟩ = 29818300543154103 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_14_32 : boxUpper ⟨5, 11, 14, 32⟩ = 24010732923068566 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_14_32 : boxUpper ⟨6, 11, 14, 32⟩ = 31443392964356999 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_14_32 : boxUpper ⟨5, 12, 14, 32⟩ = 34244778400513763 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 32 14 = 394773367787122283 := by
  have members : atPair 32 14 = [
    ⟨5, 6, 14, 32⟩,
    ⟨5, 7, 14, 32⟩,
    ⟨6, 7, 14, 32⟩,
    ⟨5, 8, 14, 32⟩,
    ⟨6, 8, 14, 32⟩,
    ⟨7, 8, 14, 32⟩,
    ⟨5, 9, 14, 32⟩,
    ⟨6, 9, 14, 32⟩,
    ⟨7, 9, 14, 32⟩,
    ⟨8, 9, 14, 32⟩,
    ⟨5, 10, 14, 32⟩,
    ⟨6, 10, 14, 32⟩,
    ⟨7, 10, 14, 32⟩,
    ⟨5, 11, 14, 32⟩,
    ⟨6, 11, 14, 32⟩,
    ⟨5, 12, 14, 32⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_14_32, box_5_7_14_32, box_6_7_14_32, box_5_8_14_32, box_6_8_14_32, box_7_8_14_32, box_5_9_14_32, box_6_9_14_32, box_7_9_14_32, box_8_9_14_32, box_5_10_14_32, box_6_10_14_32, box_7_10_14_32, box_5_11_14_32, box_6_11_14_32, box_5_12_14_32]
  all_goals decide +kernel

private theorem box_4_5_15_32 : boxUpper ⟨4, 5, 15, 32⟩ = 39437186108258740 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_15_32 : boxUpper ⟨4, 6, 15, 32⟩ = 34092725429809829 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_15_32 : boxUpper ⟨5, 6, 15, 32⟩ = 28476080715449810 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_15_32 : boxUpper ⟨4, 7, 15, 32⟩ = 30227762487862721 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_15_32 : boxUpper ⟨5, 7, 15, 32⟩ = 25263520575821473 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_15_32 : boxUpper ⟨6, 7, 15, 32⟩ = 21880566960792605 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_15_32 : boxUpper ⟨4, 8, 15, 32⟩ = 27315557973204508 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_15_32 : boxUpper ⟨5, 8, 15, 32⟩ = 22844472711614197 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_15_32 : boxUpper ⟨6, 8, 15, 32⟩ = 19799023417517664 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_15_32 : boxUpper ⟨7, 8, 15, 32⟩ = 17617371574997815 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_15_32 : boxUpper ⟨4, 9, 15, 32⟩ = 25054203240084768 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_15_32 : boxUpper ⟨5, 9, 15, 32⟩ = 20967651894155762 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_15_32 : boxUpper ⟨6, 9, 15, 32⟩ = 18201782502636515 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_15_32 : boxUpper ⟨7, 9, 15, 32⟩ = 20469950433276407 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_15_32 : boxUpper ⟨4, 10, 15, 32⟩ = 23258271531749590 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_15_32 : boxUpper ⟨5, 10, 15, 32⟩ = 19495990107213350 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_15_32 : boxUpper ⟨6, 10, 15, 32⟩ = 21380480485812687 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_11_15_32 : boxUpper ⟨4, 11, 15, 32⟩ = 21826703138929313 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_15_32 : boxUpper ⟨5, 11, 15, 32⟩ = 23093648215090338 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_12_15_32 : boxUpper ⟨4, 12, 15, 32⟩ = 26015670191954853 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 32 15 = 486718619696232945 := by
  have members : atPair 32 15 = [
    ⟨4, 5, 15, 32⟩,
    ⟨4, 6, 15, 32⟩,
    ⟨5, 6, 15, 32⟩,
    ⟨4, 7, 15, 32⟩,
    ⟨5, 7, 15, 32⟩,
    ⟨6, 7, 15, 32⟩,
    ⟨4, 8, 15, 32⟩,
    ⟨5, 8, 15, 32⟩,
    ⟨6, 8, 15, 32⟩,
    ⟨7, 8, 15, 32⟩,
    ⟨4, 9, 15, 32⟩,
    ⟨5, 9, 15, 32⟩,
    ⟨6, 9, 15, 32⟩,
    ⟨7, 9, 15, 32⟩,
    ⟨4, 10, 15, 32⟩,
    ⟨5, 10, 15, 32⟩,
    ⟨6, 10, 15, 32⟩,
    ⟨4, 11, 15, 32⟩,
    ⟨5, 11, 15, 32⟩,
    ⟨4, 12, 15, 32⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_15_32, box_4_6_15_32, box_5_6_15_32, box_4_7_15_32, box_5_7_15_32, box_6_7_15_32, box_4_8_15_32, box_5_8_15_32, box_6_8_15_32, box_7_8_15_32, box_4_9_15_32, box_5_9_15_32, box_6_9_15_32, box_7_9_15_32, box_4_10_15_32, box_5_10_15_32, box_6_10_15_32, box_4_11_15_32, box_5_11_15_32, box_4_12_15_32]
  all_goals decide +kernel

theorem column_32 : columnUpper 32 = 1525187002036652580 := by
  unfold columnUpper
  have indices : List.range 32 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_11, pair_12, pair_13, pair_14, pair_15]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_32
