import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_5_6_8_38 : boxUpper ⟨5, 6, 8, 38⟩ = 81708299588343441 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_8 : pairUpper 38 8 = 81708299588343441 := by
  have members : atPair 38 8 = [
    ⟨5, 6, 8, 38⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_8_38]
  all_goals decide +kernel

private theorem box_4_5_9_38 : boxUpper ⟨4, 5, 9, 38⟩ = 54511833274505878 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_9_38 : boxUpper ⟨4, 6, 9, 38⟩ = 59192828214749520 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_9 : pairUpper 38 9 = 113704661489255398 := by
  have members : atPair 38 9 = [
    ⟨4, 5, 9, 38⟩,
    ⟨4, 6, 9, 38⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_9_38, box_4_6_9_38]
  all_goals decide +kernel

theorem column_38 : columnUpper 38 = 195412961077598839 := by
  unfold columnUpper
  have indices : List.range 38 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_8, pair_9]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_38
