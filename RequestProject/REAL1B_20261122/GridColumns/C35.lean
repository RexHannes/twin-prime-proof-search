import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_7_8_9_35 : boxUpper ⟨7, 8, 9, 35⟩ = 48705228114364560 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_9 : pairUpper 35 9 = 48705228114364560 := by
  have members : atPair 35 9 = [
    ⟨7, 8, 9, 35⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_9_35]
  all_goals decide +kernel

private theorem box_6_7_10_35 : boxUpper ⟨6, 7, 10, 35⟩ = 35540256051259224 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_10_35 : boxUpper ⟨6, 8, 10, 35⟩ = 48479400188093213 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_10_35 : boxUpper ⟨7, 8, 10, 35⟩ = 45183131576169348 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_10_35 : boxUpper ⟨6, 9, 10, 35⟩ = 46682162209521699 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_10 : pairUpper 35 10 = 175884950025043484 := by
  have members : atPair 35 10 = [
    ⟨6, 7, 10, 35⟩,
    ⟨6, 8, 10, 35⟩,
    ⟨7, 8, 10, 35⟩,
    ⟨6, 9, 10, 35⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_10_35, box_6_8_10_35, box_7_8_10_35, box_6_9_10_35]
  all_goals decide +kernel

private theorem box_5_6_11_35 : boxUpper ⟨5, 6, 11, 35⟩ = 34336626146746001 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_11_35 : boxUpper ⟨5, 7, 11, 35⟩ = 30470481850025500 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_11_35 : boxUpper ⟨6, 7, 11, 35⟩ = 33257982664195130 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_11_35 : boxUpper ⟨5, 8, 11, 35⟩ = 34704122079270913 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_11_35 : boxUpper ⟨6, 8, 11, 35⟩ = 45393280930454140 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_11_35 : boxUpper ⟨5, 9, 11, 35⟩ = 48061496424338935 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_11 : pairUpper 35 11 = 226223990095030619 := by
  have members : atPair 35 11 = [
    ⟨5, 6, 11, 35⟩,
    ⟨5, 7, 11, 35⟩,
    ⟨6, 7, 11, 35⟩,
    ⟨5, 8, 11, 35⟩,
    ⟨6, 8, 11, 35⟩,
    ⟨5, 9, 11, 35⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_11_35, box_5_7_11_35, box_6_7_11_35, box_5_8_11_35, box_6_8_11_35, box_5_9_11_35]
  all_goals decide +kernel

private theorem box_4_5_12_35 : boxUpper ⟨4, 5, 12, 35⟩ = 44812433278704021 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_12_35 : boxUpper ⟨4, 6, 12, 35⟩ = 38739504411555943 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_12_35 : boxUpper ⟨5, 6, 12, 35⟩ = 32357299936686664 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_12_35 : boxUpper ⟨4, 7, 12, 35⟩ = 34347731631655820 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_12_35 : boxUpper ⟨5, 7, 12, 35⟩ = 28731805622284620 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_12_35 : boxUpper ⟨6, 7, 12, 35⟩ = 31383361358109604 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_12_35 : boxUpper ⟨4, 8, 12, 35⟩ = 31065259056067171 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_12_35 : boxUpper ⟨5, 8, 12, 35⟩ = 32747962560708224 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_12_35 : boxUpper ⟨4, 9, 12, 35⟩ = 35870682535215374 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_12 : pairUpper 35 12 = 310056040390987441 := by
  have members : atPair 35 12 = [
    ⟨4, 5, 12, 35⟩,
    ⟨4, 6, 12, 35⟩,
    ⟨5, 6, 12, 35⟩,
    ⟨4, 7, 12, 35⟩,
    ⟨5, 7, 12, 35⟩,
    ⟨6, 7, 12, 35⟩,
    ⟨4, 8, 12, 35⟩,
    ⟨5, 8, 12, 35⟩,
    ⟨4, 9, 12, 35⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_12_35, box_4_6_12_35, box_5_6_12_35, box_4_7_12_35, box_5_7_12_35, box_6_7_12_35, box_4_8_12_35, box_5_8_12_35, box_4_9_12_35]
  all_goals decide +kernel

theorem column_35 : columnUpper 35 = 760870208625426104 := by
  unfold columnUpper
  have indices : List.range 35 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_9, pair_10, pair_11, pair_12]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_35
