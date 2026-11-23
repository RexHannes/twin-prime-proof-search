import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_14_15_16_21 : boxUpper ⟨14, 15, 16, 21⟩ = 15807076844328848 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 21 16 = 15807076844328848 := by
  have members : atPair 21 16 = [
    ⟨14, 15, 16, 21⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_14_15_16_21]
  all_goals decide +kernel

private theorem box_13_14_17_21 : boxUpper ⟨13, 14, 17, 21⟩ = 10542952702136776 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_17_21 : boxUpper ⟨13, 15, 17, 21⟩ = 15278583358373188 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_17_21 : boxUpper ⟨14, 15, 17, 21⟩ = 15377029930811952 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_17_21 : boxUpper ⟨13, 16, 17, 21⟩ = 15516528436399248 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_16_17_21 : boxUpper ⟨14, 16, 17, 21⟩ = 14925551686210315 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_15_16_17_21 : boxUpper ⟨15, 16, 17, 21⟩ = 16383617879185283 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 21 17 = 88024263993116762 := by
  have members : atPair 21 17 = [
    ⟨13, 14, 17, 21⟩,
    ⟨13, 15, 17, 21⟩,
    ⟨14, 15, 17, 21⟩,
    ⟨13, 16, 17, 21⟩,
    ⟨14, 16, 17, 21⟩,
    ⟨15, 16, 17, 21⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_13_14_17_21, box_13_15_17_21, box_14_15_17_21, box_13_16_17_21, box_14_16_17_21, box_15_16_17_21]
  all_goals decide +kernel

private theorem box_12_13_18_21 : boxUpper ⟨12, 13, 18, 21⟩ = 8849268291246631 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_18_21 : boxUpper ⟨12, 14, 18, 21⟩ = 8491540522594769 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_18_21 : boxUpper ⟨13, 14, 18, 21⟩ = 10281357826695149 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_18_21 : boxUpper ⟨12, 15, 18, 21⟩ = 10388016581735595 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_18_21 : boxUpper ⟨13, 15, 18, 21⟩ = 14912625921756871 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_18_21 : boxUpper ⟨14, 15, 18, 21⟩ = 15030575163858421 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_18_21 : boxUpper ⟨12, 16, 18, 21⟩ = 15131478662661732 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_18_21 : boxUpper ⟨13, 16, 18, 21⟩ = 15166925329477683 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_16_18_21 : boxUpper ⟨14, 16, 18, 21⟩ = 16567991239215772 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_15_16_18_21 : boxUpper ⟨15, 16, 18, 21⟩ = 20551618240926878 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_17_18_21 : boxUpper ⟨12, 17, 18, 21⟩ = 15447195994294367 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_17_18_21 : boxUpper ⟨13, 17, 18, 21⟩ = 16779809986843033 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_17_18_21 : boxUpper ⟨14, 17, 18, 21⟩ = 20714958390088934 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_15_17_18_21 : boxUpper ⟨15, 17, 18, 21⟩ = 20710799124029579 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_16_17_18_21 : boxUpper ⟨16, 17, 18, 21⟩ = 20191415474161399 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 21 18 = 229215576749586813 := by
  have members : atPair 21 18 = [
    ⟨12, 13, 18, 21⟩,
    ⟨12, 14, 18, 21⟩,
    ⟨13, 14, 18, 21⟩,
    ⟨12, 15, 18, 21⟩,
    ⟨13, 15, 18, 21⟩,
    ⟨14, 15, 18, 21⟩,
    ⟨12, 16, 18, 21⟩,
    ⟨13, 16, 18, 21⟩,
    ⟨14, 16, 18, 21⟩,
    ⟨15, 16, 18, 21⟩,
    ⟨12, 17, 18, 21⟩,
    ⟨13, 17, 18, 21⟩,
    ⟨14, 17, 18, 21⟩,
    ⟨15, 17, 18, 21⟩,
    ⟨16, 17, 18, 21⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_12_13_18_21, box_12_14_18_21, box_13_14_18_21, box_12_15_18_21, box_13_15_18_21, box_14_15_18_21, box_12_16_18_21, box_13_16_18_21, box_14_16_18_21, box_15_16_18_21, box_12_17_18_21, box_13_17_18_21, box_14_17_18_21, box_15_17_18_21, box_16_17_18_21]
  all_goals decide +kernel

theorem column_21 : columnUpper 21 = 333046917587032423 := by
  unfold columnUpper
  have indices : List.range 21 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_16, pair_17, pair_18]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_21
