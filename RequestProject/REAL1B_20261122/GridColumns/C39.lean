import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_4_5_8_39 : boxUpper ⟨4, 5, 8, 39⟩ = 74566262237909366 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_8 : pairUpper 39 8 = 74566262237909366 := by
  have members : atPair 39 8 = [
    ⟨4, 5, 8, 39⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_8_39]
  all_goals decide +kernel

theorem column_39 : columnUpper 39 = 74566262237909366 := by
  unfold columnUpper
  have indices : List.range 39 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_8]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_39
