import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_8_9_10_33 : boxUpper ⟨8, 9, 10, 33⟩ = 37718929549370875 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_10 : pairUpper 33 10 = 37718929549370875 := by
  have members : atPair 33 10 = [
    ⟨8, 9, 10, 33⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_10_33]
  all_goals decide +kernel

private theorem box_7_8_11_33 : boxUpper ⟨7, 8, 11, 33⟩ = 26912902929450565 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_11_33 : boxUpper ⟨7, 9, 11, 33⟩ = 37220536349759138 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_11_33 : boxUpper ⟨8, 9, 11, 33⟩ = 35341069206498401 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_11_33 : boxUpper ⟨7, 10, 11, 33⟩ = 36257042474327933 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_11_33 : boxUpper ⟨8, 10, 11, 33⟩ = 32831597437152610 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_11 : pairUpper 33 11 = 168563148397188647 := by
  have members : atPair 33 11 = [
    ⟨7, 8, 11, 33⟩,
    ⟨7, 9, 11, 33⟩,
    ⟨8, 9, 11, 33⟩,
    ⟨7, 10, 11, 33⟩,
    ⟨8, 10, 11, 33⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_11_33, box_7_9_11_33, box_8_9_11_33, box_7_10_11_33, box_8_10_11_33]
  all_goals decide +kernel

private theorem box_6_7_12_33 : boxUpper ⟨6, 7, 12, 33⟩ = 25041242707827172 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_12_33 : boxUpper ⟨6, 8, 12, 33⟩ = 22648818652057536 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_12_33 : boxUpper ⟨7, 8, 12, 33⟩ = 25395982372870060 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_12_33 : boxUpper ⟨6, 9, 12, 33⟩ = 26229073873025273 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_12_33 : boxUpper ⟨7, 9, 12, 33⟩ = 35144680180624385 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_12_33 : boxUpper ⟨8, 9, 12, 33⟩ = 33393159190986115 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_12_33 : boxUpper ⟨6, 10, 12, 33⟩ = 36719440661667206 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_12_33 : boxUpper ⟨7, 10, 12, 33⟩ = 34258634233856927 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_12_33 : boxUpper ⟨6, 11, 12, 33⟩ = 36132216202605742 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_12 : pairUpper 33 12 = 274963248075520416 := by
  have members : atPair 33 12 = [
    ⟨6, 7, 12, 33⟩,
    ⟨6, 8, 12, 33⟩,
    ⟨7, 8, 12, 33⟩,
    ⟨6, 9, 12, 33⟩,
    ⟨7, 9, 12, 33⟩,
    ⟨8, 9, 12, 33⟩,
    ⟨6, 10, 12, 33⟩,
    ⟨7, 10, 12, 33⟩,
    ⟨6, 11, 12, 33⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_12_33, box_6_8_12_33, box_7_8_12_33, box_6_9_12_33, box_7_9_12_33, box_8_9_12_33, box_6_10_12_33, box_7_10_12_33, box_6_11_12_33]
  all_goals decide +kernel

private theorem box_5_6_13_33 : boxUpper ⟨5, 6, 13, 33⟩ = 30969748310351312 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_13_33 : boxUpper ⟨5, 7, 13, 33⟩ = 27458870329467522 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_13_33 : boxUpper ⟨6, 7, 13, 33⟩ = 23766466509792361 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_13_33 : boxUpper ⟨5, 8, 13, 33⟩ = 24813469174910431 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_13_33 : boxUpper ⟨6, 8, 13, 33⟩ = 21509833733449245 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_13_33 : boxUpper ⟨7, 8, 13, 33⟩ = 24137561535271625 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_13_33 : boxUpper ⟨5, 9, 13, 33⟩ = 22779323878779821 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_13_33 : boxUpper ⟨6, 9, 13, 33⟩ = 24929358524331412 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_13_33 : boxUpper ⟨7, 9, 13, 33⟩ = 33425299462465611 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_13_33 : boxUpper ⟨5, 10, 13, 33⟩ = 26680829394421512 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_13_33 : boxUpper ⟨6, 10, 13, 33⟩ = 34922997671599724 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_13_33 : boxUpper ⟨5, 11, 13, 33⟩ = 37743415809638268 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_13 : pairUpper 33 13 = 333137174334478844 := by
  have members : atPair 33 13 = [
    ⟨5, 6, 13, 33⟩,
    ⟨5, 7, 13, 33⟩,
    ⟨6, 7, 13, 33⟩,
    ⟨5, 8, 13, 33⟩,
    ⟨6, 8, 13, 33⟩,
    ⟨7, 8, 13, 33⟩,
    ⟨5, 9, 13, 33⟩,
    ⟨6, 9, 13, 33⟩,
    ⟨7, 9, 13, 33⟩,
    ⟨5, 10, 13, 33⟩,
    ⟨6, 10, 13, 33⟩,
    ⟨5, 11, 13, 33⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_13_33, box_5_7_13_33, box_6_7_13_33, box_5_8_13_33, box_6_8_13_33, box_7_8_13_33, box_5_9_13_33, box_6_9_13_33, box_7_9_13_33, box_5_10_13_33, box_6_10_13_33, box_5_11_13_33]
  all_goals decide +kernel

private theorem box_4_5_14_33 : boxUpper ⟨4, 5, 14, 33⟩ = 40909192992570505 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_14_33 : boxUpper ⟨4, 6, 14, 33⟩ = 35365242484979099 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_14_33 : boxUpper ⟨5, 6, 14, 33⟩ = 29538950283192816 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_14_33 : boxUpper ⟨4, 7, 14, 33⟩ = 31356013578509733 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_14_33 : boxUpper ⟨5, 7, 14, 33⟩ = 26206476491329581 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_14_33 : boxUpper ⟨6, 7, 14, 33⟩ = 22697250366912373 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_14_33 : boxUpper ⟨4, 8, 14, 33⟩ = 28335105790644183 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_14_33 : boxUpper ⟨5, 8, 14, 33⟩ = 23697133519122703 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_14_33 : boxUpper ⟨6, 8, 14, 33⟩ = 20556227778980629 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_14_33 : boxUpper ⟨7, 8, 14, 33⟩ = 23086336161579391 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_14_33 : boxUpper ⟨4, 9, 14, 33⟩ = 25989341368251942 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_14_33 : boxUpper ⟨5, 9, 14, 33⟩ = 21769416657074579 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_14_33 : boxUpper ⟨6, 9, 14, 33⟩ = 23843635946405150 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_14_33 : boxUpper ⟨4, 10, 14, 33⟩ = 24147339296927742 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_14_33 : boxUpper ⟨5, 10, 14, 33⟩ = 25518795259816820 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_11_14_33 : boxUpper ⟨4, 11, 14, 33⟩ = 28528912015017613 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 33 14 = 431545369991314859 := by
  have members : atPair 33 14 = [
    ⟨4, 5, 14, 33⟩,
    ⟨4, 6, 14, 33⟩,
    ⟨5, 6, 14, 33⟩,
    ⟨4, 7, 14, 33⟩,
    ⟨5, 7, 14, 33⟩,
    ⟨6, 7, 14, 33⟩,
    ⟨4, 8, 14, 33⟩,
    ⟨5, 8, 14, 33⟩,
    ⟨6, 8, 14, 33⟩,
    ⟨7, 8, 14, 33⟩,
    ⟨4, 9, 14, 33⟩,
    ⟨5, 9, 14, 33⟩,
    ⟨6, 9, 14, 33⟩,
    ⟨4, 10, 14, 33⟩,
    ⟨5, 10, 14, 33⟩,
    ⟨4, 11, 14, 33⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_14_33, box_4_6_14_33, box_5_6_14_33, box_4_7_14_33, box_5_7_14_33, box_6_7_14_33, box_4_8_14_33, box_5_8_14_33, box_6_8_14_33, box_7_8_14_33, box_4_9_14_33, box_5_9_14_33, box_6_9_14_33, box_4_10_14_33, box_5_10_14_33, box_4_11_14_33]
  all_goals decide +kernel

theorem column_33 : columnUpper 33 = 1245927870347873641 := by
  unfold columnUpper
  have indices : List.range 33 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_10, pair_11, pair_12, pair_13, pair_14]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_33
