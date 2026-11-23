import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_6_7_8_37 : boxUpper ⟨6, 7, 8, 37⟩ = 65972877910781918 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_8 : pairUpper 37 8 = 65972877910781918 := by
  have members : atPair 37 8 = [
    ⟨6, 7, 8, 37⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_8_37]
  all_goals decide +kernel

private theorem box_5_6_9_37 : boxUpper ⟨5, 6, 9, 37⟩ = 49618681056274246 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_9_37 : boxUpper ⟨5, 7, 9, 37⟩ = 66506897623361262 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_9 : pairUpper 37 9 = 116125578679635508 := by
  have members : atPair 37 9 = [
    ⟨5, 6, 9, 37⟩,
    ⟨5, 7, 9, 37⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_9_37, box_5_7_9_37]
  all_goals decide +kernel

private theorem box_4_5_10_37 : boxUpper ⟨4, 5, 10, 37⟩ = 50556099359275977 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_10_37 : boxUpper ⟨4, 6, 10, 37⟩ = 43741700055480346 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_10_37 : boxUpper ⟨5, 6, 10, 37⟩ = 45975618320761390 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_10_37 : boxUpper ⟨4, 7, 10, 37⟩ = 48760295521833934 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_10 : pairUpper 37 10 = 189033713257351647 := by
  have members : atPair 37 10 = [
    ⟨4, 5, 10, 37⟩,
    ⟨4, 6, 10, 37⟩,
    ⟨5, 6, 10, 37⟩,
    ⟨4, 7, 10, 37⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_10_37, box_4_6_10_37, box_5_6_10_37, box_4_7_10_37]
  all_goals decide +kernel

theorem column_37 : columnUpper 37 = 371132169847769073 := by
  unfold columnUpper
  have indices : List.range 37 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_8, pair_9, pair_10]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_37
