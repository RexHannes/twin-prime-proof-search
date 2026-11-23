import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_13_14_15_23 : boxUpper ⟨13, 14, 15, 23⟩ = 17155849209939317 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 23 15 = 17155849209939317 := by
  have members : atPair 23 15 = [
    ⟨13, 14, 15, 23⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_13_14_15_23]
  all_goals decide +kernel

private theorem box_12_13_16_23 : boxUpper ⟨12, 13, 16, 23⟩ = 11524701260362042 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_16_23 : boxUpper ⟨12, 14, 16, 23⟩ = 16610873531161154 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_16_23 : boxUpper ⟨13, 14, 16, 23⟩ = 16611231732395644 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_16_23 : boxUpper ⟨12, 15, 16, 23⟩ = 16784646066822983 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_16_23 : boxUpper ⟨13, 15, 16, 23⟩ = 16031730613069070 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_16_23 : boxUpper ⟨14, 15, 16, 23⟩ = 15413875798284407 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 23 16 = 92977059002095300 := by
  have members : atPair 23 16 = [
    ⟨12, 13, 16, 23⟩,
    ⟨12, 14, 16, 23⟩,
    ⟨13, 14, 16, 23⟩,
    ⟨12, 15, 16, 23⟩,
    ⟨13, 15, 16, 23⟩,
    ⟨14, 15, 16, 23⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_12_13_16_23, box_12_14_16_23, box_13_14_16_23, box_12_15_16_23, box_13_15_16_23, box_14_15_16_23]
  all_goals decide +kernel

private theorem box_11_12_17_23 : boxUpper ⟨11, 12, 17, 23⟩ = 9771025649661397 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_17_23 : boxUpper ⟨11, 13, 17, 23⟩ = 9315982354980861 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_17_23 : boxUpper ⟨12, 13, 17, 23⟩ = 11191505724765397 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_17_23 : boxUpper ⟨11, 14, 17, 23⟩ = 11326489778180933 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_17_23 : boxUpper ⟨12, 14, 17, 23⟩ = 16144011334537983 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_17_23 : boxUpper ⟨13, 14, 17, 23⟩ = 16159299540529162 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_17_23 : boxUpper ⟨11, 15, 17, 23⟩ = 16418399736754126 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_17_23 : boxUpper ⟨12, 15, 17, 23⟩ = 16327993896390453 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_17_23 : boxUpper ⟨13, 15, 17, 23⟩ = 15611573160054247 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_17_23 : boxUpper ⟨14, 15, 17, 23⟩ = 15026357946093651 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_17_23 : boxUpper ⟨11, 16, 17, 23⟩ = 16676193868061789 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_17_23 : boxUpper ⟨12, 16, 17, 23⟩ = 15841132981780278 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_17_23 : boxUpper ⟨13, 16, 17, 23⟩ = 15162671887028428 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_16_17_23 : boxUpper ⟨14, 16, 17, 23⟩ = 14618287547540529 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_15_16_17_23 : boxUpper ⟨15, 16, 17, 23⟩ = 16088281682202969 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 23 17 = 215679207088562203 := by
  have members : atPair 23 17 = [
    ⟨11, 12, 17, 23⟩,
    ⟨11, 13, 17, 23⟩,
    ⟨12, 13, 17, 23⟩,
    ⟨11, 14, 17, 23⟩,
    ⟨12, 14, 17, 23⟩,
    ⟨13, 14, 17, 23⟩,
    ⟨11, 15, 17, 23⟩,
    ⟨12, 15, 17, 23⟩,
    ⟨13, 15, 17, 23⟩,
    ⟨14, 15, 17, 23⟩,
    ⟨11, 16, 17, 23⟩,
    ⟨12, 16, 17, 23⟩,
    ⟨13, 16, 17, 23⟩,
    ⟨14, 16, 17, 23⟩,
    ⟨15, 16, 17, 23⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_11_12_17_23, box_11_13_17_23, box_12_13_17_23, box_11_14_17_23, box_12_14_17_23, box_13_14_17_23, box_11_15_17_23, box_12_15_17_23, box_13_15_17_23, box_14_15_17_23, box_11_16_17_23, box_12_16_17_23, box_13_16_17_23, box_14_16_17_23, box_15_16_17_23]
  all_goals decide +kernel

private theorem box_10_11_18_23 : boxUpper ⟨10, 11, 18, 23⟩ = 10709857225519845 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_18_23 : boxUpper ⟨10, 12, 18, 23⟩ = 10127308315616473 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_18_23 : boxUpper ⟨11, 12, 18, 23⟩ = 9510659648869046 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_18_23 : boxUpper ⟨10, 13, 18, 23⟩ = 9646707601768057 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_18_23 : boxUpper ⟨11, 13, 18, 23⟩ = 9075497496164424 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_18_23 : boxUpper ⟨12, 13, 18, 23⟩ = 10913812225096648 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_18_23 : boxUpper ⟨10, 14, 18, 23⟩ = 9256693457349210 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_18_23 : boxUpper ⟨11, 14, 18, 23⟩ = 11045445200320843 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_18_23 : boxUpper ⟨12, 14, 18, 23⟩ = 15757317468882349 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_18_23 : boxUpper ⟨13, 14, 18, 23⟩ = 15787787738625211 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_18_23 : boxUpper ⟨10, 15, 18, 23⟩ = 11318493348221997 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_18_23 : boxUpper ⟨11, 15, 18, 23⟩ = 16025130545260687 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_18_23 : boxUpper ⟨12, 15, 18, 23⟩ = 15952601634001173 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_18_23 : boxUpper ⟨13, 15, 18, 23⟩ = 15269365261147782 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_18_23 : boxUpper ⟨14, 15, 18, 23⟩ = 14721146605013734 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_18_23 : boxUpper ⟨10, 16, 18, 23⟩ = 16492346871824460 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_18_23 : boxUpper ⟨11, 16, 18, 23⟩ = 16292791858683017 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_18_23 : boxUpper ⟨12, 16, 18, 23⟩ = 15493890156244686 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_18_23 : boxUpper ⟨13, 16, 18, 23⟩ = 14854686302072104 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_16_18_23 : boxUpper ⟨14, 16, 18, 23⟩ = 16269326536045029 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_15_16_18_23 : boxUpper ⟨15, 16, 18, 23⟩ = 20231520287144467 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_17_18_23 : boxUpper ⟨10, 17, 18, 23⟩ = 16831234945734057 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_17_18_23 : boxUpper ⟨11, 17, 18, 23⟩ = 15883166049495073 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_17_18_23 : boxUpper ⟨12, 17, 18, 23⟩ = 15129179792659900 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_17_18_23 : boxUpper ⟨13, 17, 18, 23⟩ = 16477320859841248 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_17_18_23 : boxUpper ⟨14, 17, 18, 23⟩ = 20392312162633955 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 23 18 = 369465599594235475 := by
  have members : atPair 23 18 = [
    ⟨10, 11, 18, 23⟩,
    ⟨10, 12, 18, 23⟩,
    ⟨11, 12, 18, 23⟩,
    ⟨10, 13, 18, 23⟩,
    ⟨11, 13, 18, 23⟩,
    ⟨12, 13, 18, 23⟩,
    ⟨10, 14, 18, 23⟩,
    ⟨11, 14, 18, 23⟩,
    ⟨12, 14, 18, 23⟩,
    ⟨13, 14, 18, 23⟩,
    ⟨10, 15, 18, 23⟩,
    ⟨11, 15, 18, 23⟩,
    ⟨12, 15, 18, 23⟩,
    ⟨13, 15, 18, 23⟩,
    ⟨14, 15, 18, 23⟩,
    ⟨10, 16, 18, 23⟩,
    ⟨11, 16, 18, 23⟩,
    ⟨12, 16, 18, 23⟩,
    ⟨13, 16, 18, 23⟩,
    ⟨14, 16, 18, 23⟩,
    ⟨15, 16, 18, 23⟩,
    ⟨10, 17, 18, 23⟩,
    ⟨11, 17, 18, 23⟩,
    ⟨12, 17, 18, 23⟩,
    ⟨13, 17, 18, 23⟩,
    ⟨14, 17, 18, 23⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_10_11_18_23, box_10_12_18_23, box_11_12_18_23, box_10_13_18_23, box_11_13_18_23, box_12_13_18_23, box_10_14_18_23, box_11_14_18_23, box_12_14_18_23, box_13_14_18_23, box_10_15_18_23, box_11_15_18_23, box_12_15_18_23, box_13_15_18_23, box_14_15_18_23, box_10_16_18_23, box_11_16_18_23, box_12_16_18_23, box_13_16_18_23, box_14_16_18_23, box_15_16_18_23, box_10_17_18_23, box_11_17_18_23, box_12_17_18_23, box_13_17_18_23, box_14_17_18_23]
  all_goals decide +kernel

private theorem box_7_8_21_23 : boxUpper ⟨7, 8, 21, 23⟩ = 16200728734203474 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_21_23 : boxUpper ⟨7, 9, 21, 23⟩ = 14859609342864210 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_21_23 : boxUpper ⟨8, 9, 21, 23⟩ = 13446027284040379 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_21_23 : boxUpper ⟨7, 10, 21, 23⟩ = 13794522715606942 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_21_23 : boxUpper ⟨8, 10, 21, 23⟩ = 12491283310382391 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_21_23 : boxUpper ⟨9, 10, 21, 23⟩ = 11482132820818752 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_21_23 : boxUpper ⟨7, 11, 21, 23⟩ = 12934245478963334 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_21_23 : boxUpper ⟨8, 11, 21, 23⟩ = 11721219517293097 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_21_23 : boxUpper ⟨9, 11, 21, 23⟩ = 10782976103766175 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_21_23 : boxUpper ⟨10, 11, 21, 23⟩ = 10041633937361342 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_21_23 : boxUpper ⟨7, 12, 21, 23⟩ = 12230679353418754 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_21_23 : boxUpper ⟨8, 12, 21, 23⟩ = 11092582423376177 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_21_23 : boxUpper ⟨9, 12, 21, 23⟩ = 10213382592593035 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_21_23 : boxUpper ⟨10, 12, 21, 23⟩ = 9519827354157950 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_21_23 : boxUpper ⟨11, 12, 21, 23⟩ = 8964549282929773 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_21_23 : boxUpper ⟨7, 13, 21, 23⟩ = 11650236558906508 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_21_23 : boxUpper ⟨8, 13, 21, 23⟩ = 10575185118324930 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_21_23 : boxUpper ⟨9, 13, 21, 23⟩ = 9745826564597343 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_21_23 : boxUpper ⟨10, 13, 21, 23⟩ = 9092780222875381 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_21_23 : boxUpper ⟨11, 13, 21, 23⟩ = 8579209039896198 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_21_23 : boxUpper ⟨12, 13, 21, 23⟩ = 10353151168314790 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_21_23 : boxUpper ⟨7, 14, 21, 23⟩ = 11168821456224528 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_21_23 : boxUpper ⟨8, 14, 21, 23⟩ = 10147391408374998 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_21_23 : boxUpper ⟨9, 14, 21, 23⟩ = 9360600246224770 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_21_23 : boxUpper ⟨10, 14, 21, 23⟩ = 8750489440251502 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_21_23 : boxUpper ⟨11, 14, 21, 23⟩ = 10478016320884599 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_21_23 : boxUpper ⟨12, 14, 21, 23⟩ = 15000340441195458 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_21_23 : boxUpper ⟨13, 14, 21, 23⟩ = 17115199495839151 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_21_23 : boxUpper ⟨7, 15, 21, 23⟩ = 10768772391218523 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_21_23 : boxUpper ⟨8, 15, 21, 23⟩ = 9793364557601380 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_21_23 : boxUpper ⟨9, 15, 21, 23⟩ = 9051715525192193 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_21_23 : boxUpper ⟨10, 15, 21, 23⟩ = 10737025447636108 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_21_23 : boxUpper ⟨11, 15, 21, 23⟩ = 15255270203119391 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_21_23 : boxUpper ⟨12, 15, 21, 23⟩ = 17293234055826448 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_21_23 : boxUpper ⟨13, 15, 21, 23⟩ = 21285310926683249 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_21_23 : boxUpper ⟨7, 16, 21, 23⟩ = 10436927114128916 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_21_23 : boxUpper ⟨8, 16, 21, 23⟩ = 9510134127283404 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_21_23 : boxUpper ⟨9, 16, 21, 23⟩ = 11150530651784378 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_21_23 : boxUpper ⟨10, 16, 21, 23⟩ = 15700009409281485 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_21_23 : boxUpper ⟨11, 16, 21, 23⟩ = 17660671585185954 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_21_23 : boxUpper ⟨12, 16, 21, 23⟩ = 21597878546655715 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_17_21_23 : boxUpper ⟨7, 17, 21, 23⟩ = 10172729951722057 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_17_21_23 : boxUpper ⟨8, 17, 21, 23⟩ = 11754231028467842 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_17_21_23 : boxUpper ⟨9, 17, 21, 23⟩ = 16368160275400198 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_17_21_23 : boxUpper ⟨10, 17, 21, 23⟩ = 18242127236016103 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_17_21_23 : boxUpper ⟨11, 17, 21, 23⟩ = 22139771795863782 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_18_21_23 : boxUpper ⟨7, 18, 21, 23⟩ = 12607747246976587 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_18_21_23 : boxUpper ⟨8, 18, 21, 23⟩ = 17315825247892865 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_18_21_23 : boxUpper ⟨9, 18, 21, 23⟩ = 19079826873298042 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_18_21_23 : boxUpper ⟨10, 18, 21, 23⟩ = 22945855228294842 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_21 : pairUpper 23 21 = 652659767159215403 := by
  have members : atPair 23 21 = [
    ⟨7, 8, 21, 23⟩,
    ⟨7, 9, 21, 23⟩,
    ⟨8, 9, 21, 23⟩,
    ⟨7, 10, 21, 23⟩,
    ⟨8, 10, 21, 23⟩,
    ⟨9, 10, 21, 23⟩,
    ⟨7, 11, 21, 23⟩,
    ⟨8, 11, 21, 23⟩,
    ⟨9, 11, 21, 23⟩,
    ⟨10, 11, 21, 23⟩,
    ⟨7, 12, 21, 23⟩,
    ⟨8, 12, 21, 23⟩,
    ⟨9, 12, 21, 23⟩,
    ⟨10, 12, 21, 23⟩,
    ⟨11, 12, 21, 23⟩,
    ⟨7, 13, 21, 23⟩,
    ⟨8, 13, 21, 23⟩,
    ⟨9, 13, 21, 23⟩,
    ⟨10, 13, 21, 23⟩,
    ⟨11, 13, 21, 23⟩,
    ⟨12, 13, 21, 23⟩,
    ⟨7, 14, 21, 23⟩,
    ⟨8, 14, 21, 23⟩,
    ⟨9, 14, 21, 23⟩,
    ⟨10, 14, 21, 23⟩,
    ⟨11, 14, 21, 23⟩,
    ⟨12, 14, 21, 23⟩,
    ⟨13, 14, 21, 23⟩,
    ⟨7, 15, 21, 23⟩,
    ⟨8, 15, 21, 23⟩,
    ⟨9, 15, 21, 23⟩,
    ⟨10, 15, 21, 23⟩,
    ⟨11, 15, 21, 23⟩,
    ⟨12, 15, 21, 23⟩,
    ⟨13, 15, 21, 23⟩,
    ⟨7, 16, 21, 23⟩,
    ⟨8, 16, 21, 23⟩,
    ⟨9, 16, 21, 23⟩,
    ⟨10, 16, 21, 23⟩,
    ⟨11, 16, 21, 23⟩,
    ⟨12, 16, 21, 23⟩,
    ⟨7, 17, 21, 23⟩,
    ⟨8, 17, 21, 23⟩,
    ⟨9, 17, 21, 23⟩,
    ⟨10, 17, 21, 23⟩,
    ⟨11, 17, 21, 23⟩,
    ⟨7, 18, 21, 23⟩,
    ⟨8, 18, 21, 23⟩,
    ⟨9, 18, 21, 23⟩,
    ⟨10, 18, 21, 23⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_21_23, box_7_9_21_23, box_8_9_21_23, box_7_10_21_23, box_8_10_21_23, box_9_10_21_23, box_7_11_21_23, box_8_11_21_23, box_9_11_21_23, box_10_11_21_23, box_7_12_21_23, box_8_12_21_23, box_9_12_21_23, box_10_12_21_23, box_11_12_21_23, box_7_13_21_23, box_8_13_21_23, box_9_13_21_23, box_10_13_21_23, box_11_13_21_23, box_12_13_21_23, box_7_14_21_23, box_8_14_21_23, box_9_14_21_23, box_10_14_21_23, box_11_14_21_23, box_12_14_21_23, box_13_14_21_23, box_7_15_21_23, box_8_15_21_23, box_9_15_21_23, box_10_15_21_23, box_11_15_21_23, box_12_15_21_23, box_13_15_21_23, box_7_16_21_23, box_8_16_21_23, box_9_16_21_23, box_10_16_21_23, box_11_16_21_23, box_12_16_21_23, box_7_17_21_23, box_8_17_21_23, box_9_17_21_23, box_10_17_21_23, box_11_17_21_23, box_7_18_21_23, box_8_18_21_23, box_9_18_21_23, box_10_18_21_23]
  all_goals decide +kernel

private theorem box_6_7_22_23 : boxUpper ⟨6, 7, 22, 23⟩ = 19798431205059844 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_22_23 : boxUpper ⟨6, 8, 22, 23⟩ = 17891083165632515 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_22_23 : boxUpper ⟨7, 8, 22, 23⟩ = 15883067912024927 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_22_23 : boxUpper ⟨6, 9, 22, 23⟩ = 16410016874356820 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_22_23 : boxUpper ⟨7, 9, 22, 23⟩ = 14578220197084199 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_22_23 : boxUpper ⟨8, 9, 22, 23⟩ = 13200934367985622 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_22_23 : boxUpper ⟨6, 10, 22, 23⟩ = 15233785688668933 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_22_23 : boxUpper ⟨7, 10, 22, 23⟩ = 13543072674271819 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_22_23 : boxUpper ⟨8, 10, 22, 23⟩ = 12272943451951432 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_22_23 : boxUpper ⟨9, 10, 22, 23⟩ = 11290531583215062 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_22_23 : boxUpper ⟨6, 11, 22, 23⟩ = 14283734309019521 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_22_23 : boxUpper ⟨7, 11, 22, 23⟩ = 12708156720012475 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_22_23 : boxUpper ⟨8, 11, 22, 23⟩ = 11525625373863037 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_22_23 : boxUpper ⟨9, 11, 22, 23⟩ = 10612098694623128 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_22_23 : boxUpper ⟨10, 11, 22, 23⟩ = 9891464277141550 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_22_23 : boxUpper ⟨6, 12, 22, 23⟩ = 13506745529391979 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_22_23 : boxUpper ⟨7, 12, 22, 23⟩ = 12026576447628768 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_22_23 : boxUpper ⟨8, 12, 22, 23⟩ = 10916794328611060 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_22_23 : boxUpper ⟨9, 12, 22, 23⟩ = 10060642069724755 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_22_23 : boxUpper ⟨10, 12, 22, 23⟩ = 9386497643814147 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_22_23 : boxUpper ⟨11, 12, 22, 23⟩ = 8848070623282662 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_22_23 : boxUpper ⟨6, 13, 22, 23⟩ = 12865726743800461 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_22_23 : boxUpper ⟨7, 13, 22, 23⟩ = 11465602862922127 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_22_23 : boxUpper ⟨8, 13, 22, 23⟩ = 10417028599052010 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_22_23 : boxUpper ⟨9, 13, 22, 23⟩ = 9609328354948813 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_22_23 : boxUpper ⟨10, 13, 22, 23⟩ = 8974633555579021 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_22_23 : boxUpper ⟨11, 13, 22, 23⟩ = 8477026738177615 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_22_23 : boxUpper ⟨12, 13, 22, 23⟩ = 10251017230512511 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_22_23 : boxUpper ⟨6, 14, 22, 23⟩ = 12334067940781564 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_22_23 : boxUpper ⟨7, 14, 22, 23⟩ = 11001777730324055 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_22_23 : boxUpper ⟨8, 14, 22, 23⟩ = 10005262902990506 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_22_23 : boxUpper ⟨9, 14, 22, 23⟩ = 9238969648833686 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_22_23 : boxUpper ⟨10, 14, 22, 23⟩ = 8646264503614541 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_22_23 : boxUpper ⟨11, 14, 22, 23⟩ = 10374642884401677 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_22_23 : boxUpper ⟨12, 14, 22, 23⟩ = 16957785925070935 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_22_23 : boxUpper ⟨13, 14, 22, 23⟩ = 21745354472185533 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_22_23 : boxUpper ⟨6, 15, 22, 23⟩ = 11892264439320267 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_22_23 : boxUpper ⟨7, 15, 22, 23⟩ = 10617930630267598 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_22_23 : boxUpper ⟨8, 15, 22, 23⟩ = 9666103870995678 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_22_23 : boxUpper ⟨9, 15, 22, 23⟩ = 8943898016091981 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_22_23 : boxUpper ⟨10, 15, 22, 23⟩ = 10631080331906065 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_22_23 : boxUpper ⟨11, 15, 22, 23⟩ = 17244953208593076 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_22_23 : boxUpper ⟨12, 15, 22, 23⟩ = 21972047043133784 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_22_23 : boxUpper ⟨6, 16, 22, 23⟩ = 11525780439857006 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_22_23 : boxUpper ⟨7, 16, 22, 23⟩ = 10301292829394847 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_22_23 : boxUpper ⟨8, 16, 22, 23⟩ = 9396848684871369 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_22_23 : boxUpper ⟨9, 16, 22, 23⟩ = 11040478276064719 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_22_23 : boxUpper ⟨10, 16, 22, 23⟩ = 17745850600667414 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_22_23 : boxUpper ⟨11, 16, 22, 23⟩ = 22439939450943514 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_17_22_23 : boxUpper ⟨6, 17, 22, 23⟩ = 11223654947225229 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_17_22_23 : boxUpper ⟨7, 17, 22, 23⟩ = 10051539898466274 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_17_22_23 : boxUpper ⟨8, 17, 22, 23⟩ = 11638178693910060 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_17_22_23 : boxUpper ⟨9, 17, 22, 23⟩ = 18498174535317720 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_17_22_23 : boxUpper ⟨10, 17, 22, 23⟩ = 23180448508627744 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_18_22_23 : boxUpper ⟨6, 18, 22, 23⟩ = 10987627084943429 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_18_22_23 : boxUpper ⟨7, 18, 22, 23⟩ = 12483204999618727 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_18_22_23 : boxUpper ⟨8, 18, 22, 23⟩ = 19564822595060413 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_18_22_23 : boxUpper ⟨9, 18, 22, 23⟩ = 24247483611714000 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_21_22_23 : boxUpper ⟨6, 21, 22, 23⟩ = 30587499988323324 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_22 : pairUpper 23 22 = 792114085915873548 := by
  have members : atPair 23 22 = [
    ⟨6, 7, 22, 23⟩,
    ⟨6, 8, 22, 23⟩,
    ⟨7, 8, 22, 23⟩,
    ⟨6, 9, 22, 23⟩,
    ⟨7, 9, 22, 23⟩,
    ⟨8, 9, 22, 23⟩,
    ⟨6, 10, 22, 23⟩,
    ⟨7, 10, 22, 23⟩,
    ⟨8, 10, 22, 23⟩,
    ⟨9, 10, 22, 23⟩,
    ⟨6, 11, 22, 23⟩,
    ⟨7, 11, 22, 23⟩,
    ⟨8, 11, 22, 23⟩,
    ⟨9, 11, 22, 23⟩,
    ⟨10, 11, 22, 23⟩,
    ⟨6, 12, 22, 23⟩,
    ⟨7, 12, 22, 23⟩,
    ⟨8, 12, 22, 23⟩,
    ⟨9, 12, 22, 23⟩,
    ⟨10, 12, 22, 23⟩,
    ⟨11, 12, 22, 23⟩,
    ⟨6, 13, 22, 23⟩,
    ⟨7, 13, 22, 23⟩,
    ⟨8, 13, 22, 23⟩,
    ⟨9, 13, 22, 23⟩,
    ⟨10, 13, 22, 23⟩,
    ⟨11, 13, 22, 23⟩,
    ⟨12, 13, 22, 23⟩,
    ⟨6, 14, 22, 23⟩,
    ⟨7, 14, 22, 23⟩,
    ⟨8, 14, 22, 23⟩,
    ⟨9, 14, 22, 23⟩,
    ⟨10, 14, 22, 23⟩,
    ⟨11, 14, 22, 23⟩,
    ⟨12, 14, 22, 23⟩,
    ⟨13, 14, 22, 23⟩,
    ⟨6, 15, 22, 23⟩,
    ⟨7, 15, 22, 23⟩,
    ⟨8, 15, 22, 23⟩,
    ⟨9, 15, 22, 23⟩,
    ⟨10, 15, 22, 23⟩,
    ⟨11, 15, 22, 23⟩,
    ⟨12, 15, 22, 23⟩,
    ⟨6, 16, 22, 23⟩,
    ⟨7, 16, 22, 23⟩,
    ⟨8, 16, 22, 23⟩,
    ⟨9, 16, 22, 23⟩,
    ⟨10, 16, 22, 23⟩,
    ⟨11, 16, 22, 23⟩,
    ⟨6, 17, 22, 23⟩,
    ⟨7, 17, 22, 23⟩,
    ⟨8, 17, 22, 23⟩,
    ⟨9, 17, 22, 23⟩,
    ⟨10, 17, 22, 23⟩,
    ⟨6, 18, 22, 23⟩,
    ⟨7, 18, 22, 23⟩,
    ⟨8, 18, 22, 23⟩,
    ⟨9, 18, 22, 23⟩,
    ⟨6, 21, 22, 23⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_22_23, box_6_8_22_23, box_7_8_22_23, box_6_9_22_23, box_7_9_22_23, box_8_9_22_23, box_6_10_22_23, box_7_10_22_23, box_8_10_22_23, box_9_10_22_23, box_6_11_22_23, box_7_11_22_23, box_8_11_22_23, box_9_11_22_23, box_10_11_22_23, box_6_12_22_23, box_7_12_22_23, box_8_12_22_23, box_9_12_22_23, box_10_12_22_23, box_11_12_22_23, box_6_13_22_23, box_7_13_22_23, box_8_13_22_23, box_9_13_22_23, box_10_13_22_23, box_11_13_22_23, box_12_13_22_23, box_6_14_22_23, box_7_14_22_23, box_8_14_22_23, box_9_14_22_23, box_10_14_22_23, box_11_14_22_23, box_12_14_22_23, box_13_14_22_23, box_6_15_22_23, box_7_15_22_23, box_8_15_22_23, box_9_15_22_23, box_10_15_22_23, box_11_15_22_23, box_12_15_22_23, box_6_16_22_23, box_7_16_22_23, box_8_16_22_23, box_9_16_22_23, box_10_16_22_23, box_11_16_22_23, box_6_17_22_23, box_7_17_22_23, box_8_17_22_23, box_9_17_22_23, box_10_17_22_23, box_6_18_22_23, box_7_18_22_23, box_8_18_22_23, box_9_18_22_23, box_6_21_22_23]
  all_goals decide +kernel

theorem column_23 : columnUpper 23 = 2140051567969921246 := by
  unfold columnUpper
  have indices : List.range 23 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_15, pair_16, pair_17, pair_18, pair_21, pair_22]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_23
