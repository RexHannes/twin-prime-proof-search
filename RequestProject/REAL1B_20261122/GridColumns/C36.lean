import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_6_7_9_36 : boxUpper ⟨6, 7, 9, 36⟩ = 57698198222835963 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_9_36 : boxUpper ⟨6, 8, 9, 36⟩ = 54751565189724471 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_9 : pairUpper 36 9 = 112449763412560434 := by
  have members : atPair 36 9 = [
    ⟨6, 7, 9, 36⟩,
    ⟨6, 8, 9, 36⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_9_36, box_6_8_9_36]
  all_goals decide +kernel

private theorem box_5_6_10_36 : boxUpper ⟨5, 6, 10, 36⟩ = 36629145685015306 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_10_36 : boxUpper ⟨5, 7, 10, 36⟩ = 40902904035167936 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_10_36 : boxUpper ⟨6, 7, 10, 36⟩ = 53492356391098425 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_10_36 : boxUpper ⟨5, 8, 10, 36⟩ = 55838636227459570 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_10 : pairUpper 36 10 = 186863042338741237 := by
  have members : atPair 36 10 = [
    ⟨5, 6, 10, 36⟩,
    ⟨5, 7, 10, 36⟩,
    ⟨6, 7, 10, 36⟩,
    ⟨5, 8, 10, 36⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_10_36, box_5_7_10_36, box_6_7_10_36, box_5_8_10_36]
  all_goals decide +kernel

private theorem box_4_5_11_36 : boxUpper ⟨4, 5, 11, 36⟩ = 47396939077072204 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_11_36 : boxUpper ⟨4, 6, 11, 36⟩ = 40973748889100507 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_11_36 : boxUpper ⟨5, 6, 11, 36⟩ = 34252909552719862 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_11_36 : boxUpper ⟨4, 7, 11, 36⟩ = 36359670617295804 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_11_36 : boxUpper ⟨5, 7, 11, 36⟩ = 38276198810212962 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_11_36 : boxUpper ⟨4, 8, 11, 36⟩ = 41339446463960834 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_11 : pairUpper 36 11 = 238598913410362173 := by
  have members : atPair 36 11 = [
    ⟨4, 5, 11, 36⟩,
    ⟨4, 6, 11, 36⟩,
    ⟨5, 6, 11, 36⟩,
    ⟨4, 7, 11, 36⟩,
    ⟨5, 7, 11, 36⟩,
    ⟨4, 8, 11, 36⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_11_36, box_4_6_11_36, box_5_6_11_36, box_4_7_11_36, box_5_7_11_36, box_4_8_11_36]
  all_goals decide +kernel

theorem column_36 : columnUpper 36 = 537911719161663844 := by
  unfold columnUpper
  have indices : List.range 36 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_9, pair_10, pair_11]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_36
