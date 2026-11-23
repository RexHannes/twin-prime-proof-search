import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_7_8_10_34 : boxUpper ⟨7, 8, 10, 34⟩ = 43172596870402216 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_10_34 : boxUpper ⟨7, 9, 10, 34⟩ = 41560096201208359 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_10_34 : boxUpper ⟨8, 9, 10, 34⟩ = 37606442306519512 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_10 : pairUpper 34 10 = 122339135378130087 := by
  have members : atPair 34 10 = [
    ⟨7, 8, 10, 34⟩,
    ⟨7, 9, 10, 34⟩,
    ⟨8, 9, 10, 34⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_10_34, box_7_9_10_34, box_8_9_10_34]
  all_goals decide +kernel

private theorem box_6_7_11_34 : boxUpper ⟨6, 7, 11, 34⟩ = 26465272453382404 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_11_34 : boxUpper ⟨6, 8, 11, 34⟩ = 30178251817676999 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_11_34 : boxUpper ⟨7, 8, 11, 34⟩ = 40424339566014933 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_11_34 : boxUpper ⟨6, 9, 11, 34⟩ = 41760483514594772 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_11_34 : boxUpper ⟨7, 9, 11, 34⟩ = 38940048795882046 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_11_34 : boxUpper ⟨6, 10, 11, 34⟩ = 40691137254913602 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_11 : pairUpper 34 11 = 218459533402464756 := by
  have members : atPair 34 11 = [
    ⟨6, 7, 11, 34⟩,
    ⟨6, 8, 11, 34⟩,
    ⟨7, 8, 11, 34⟩,
    ⟨6, 9, 11, 34⟩,
    ⟨7, 9, 11, 34⟩,
    ⟨6, 10, 11, 34⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_11_34, box_6_8_11_34, box_7_8_11_34, box_6_9_11_34, box_7_9_11_34, box_6_10_11_34]
  all_goals decide +kernel

private theorem box_5_6_12_34 : boxUpper ⟨5, 6, 12, 34⟩ = 32490174250001408 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_12_34 : boxUpper ⟨5, 7, 12, 34⟩ = 28806926254861426 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_12_34 : boxUpper ⟨6, 7, 12, 34⟩ = 24955173850015779 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_12_34 : boxUpper ⟨5, 8, 12, 34⟩ = 26054418651280196 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_12_34 : boxUpper ⟨6, 8, 12, 34⟩ = 28477248654699249 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_12_34 : boxUpper ⟨7, 8, 12, 34⟩ = 38169778655183395 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_12_34 : boxUpper ⟨5, 9, 12, 34⟩ = 30137215981261343 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_12_34 : boxUpper ⟨6, 9, 12, 34⟩ = 39431385780573599 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_12_34 : boxUpper ⟨5, 10, 12, 34⟩ = 42224207005485594 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_12 : pairUpper 34 12 = 290746529083361989 := by
  have members : atPair 34 12 = [
    ⟨5, 6, 12, 34⟩,
    ⟨5, 7, 12, 34⟩,
    ⟨6, 7, 12, 34⟩,
    ⟨5, 8, 12, 34⟩,
    ⟨6, 8, 12, 34⟩,
    ⟨7, 8, 12, 34⟩,
    ⟨5, 9, 12, 34⟩,
    ⟨6, 9, 12, 34⟩,
    ⟨5, 10, 12, 34⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_12_34, box_5_7_12_34, box_6_7_12_34, box_5_8_12_34, box_6_8_12_34, box_7_8_12_34, box_5_9_12_34, box_6_9_12_34, box_5_10_12_34]
  all_goals decide +kernel

private theorem box_4_5_13_34 : boxUpper ⟨4, 5, 13, 34⟩ = 42679329582997942 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_13_34 : boxUpper ⟨4, 6, 13, 34⟩ = 36895485441871526 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_13_34 : boxUpper ⟨5, 6, 13, 34⟩ = 30817084851668262 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_13_34 : boxUpper ⟨4, 7, 13, 34⟩ = 32712771515343664 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_13_34 : boxUpper ⟨5, 7, 13, 34⟩ = 27340410603833028 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_13_34 : boxUpper ⟨6, 7, 13, 34⟩ = 23700185105177471 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_13_34 : boxUpper ⟨4, 8, 13, 34⟩ = 29561144072532487 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_13_34 : boxUpper ⟨5, 8, 13, 34⟩ = 24744131867032201 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_13_34 : boxUpper ⟨6, 8, 13, 34⟩ = 27066110691817668 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_13_34 : boxUpper ⟨4, 9, 13, 34⟩ = 27137319922722622 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_13_34 : boxUpper ⟨5, 9, 13, 34⟩ = 28643792165584008 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_13_34 : boxUpper ⟨4, 10, 13, 34⟩ = 31729887666637628 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_13 : pairUpper 34 13 = 363027653487218507 := by
  have members : atPair 34 13 = [
    ⟨4, 5, 13, 34⟩,
    ⟨4, 6, 13, 34⟩,
    ⟨5, 6, 13, 34⟩,
    ⟨4, 7, 13, 34⟩,
    ⟨5, 7, 13, 34⟩,
    ⟨6, 7, 13, 34⟩,
    ⟨4, 8, 13, 34⟩,
    ⟨5, 8, 13, 34⟩,
    ⟨6, 8, 13, 34⟩,
    ⟨4, 9, 13, 34⟩,
    ⟨5, 9, 13, 34⟩,
    ⟨4, 10, 13, 34⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_13_34, box_4_6_13_34, box_5_6_13_34, box_4_7_13_34, box_5_7_13_34, box_6_7_13_34, box_4_8_13_34, box_5_8_13_34, box_6_8_13_34, box_4_9_13_34, box_5_9_13_34, box_4_10_13_34]
  all_goals decide +kernel

theorem column_34 : columnUpper 34 = 994572851351175339 := by
  unfold columnUpper
  have indices : List.range 34 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_10, pair_11, pair_12, pair_13]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_34
