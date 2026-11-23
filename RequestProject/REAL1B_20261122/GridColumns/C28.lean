import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_10_11_13_28 : boxUpper ⟨10, 11, 13, 28⟩ = 23105357362659837 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_13_28 : boxUpper ⟨10, 12, 13, 28⟩ = 22907959229071053 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_13_28 : boxUpper ⟨11, 12, 13, 28⟩ = 21513082115269347 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_13 : pairUpper 28 13 = 67526398707000237 := by
  have members : atPair 28 13 = [
    ⟨10, 11, 13, 28⟩,
    ⟨10, 12, 13, 28⟩,
    ⟨11, 12, 13, 28⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_10_11_13_28, box_10_12_13_28, box_11_12_13_28]
  all_goals decide +kernel

private theorem box_9_10_14_28 : boxUpper ⟨9, 10, 14, 28⟩ = 13311156672602244 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_14_28 : boxUpper ⟨9, 11, 14, 28⟩ = 15803763349585783 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_14_28 : boxUpper ⟨10, 11, 14, 28⟩ = 22114596816884708 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_14_28 : boxUpper ⟨9, 12, 14, 28⟩ = 22491855128081918 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_14_28 : boxUpper ⟨10, 12, 14, 28⟩ = 21942632990794930 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_14_28 : boxUpper ⟨11, 12, 14, 28⟩ = 20624142108951653 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_14_28 : boxUpper ⟨9, 13, 14, 28⟩ = 22463561627311448 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_14_28 : boxUpper ⟨10, 13, 14, 28⟩ = 20919162436909571 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_14_28 : boxUpper ⟨11, 13, 14, 28⟩ = 19679999557531179 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_14_28 : boxUpper ⟨12, 13, 14, 28⟩ = 18675327303630886 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 28 14 = 198026197992284320 := by
  have members : atPair 28 14 = [
    ⟨9, 10, 14, 28⟩,
    ⟨9, 11, 14, 28⟩,
    ⟨10, 11, 14, 28⟩,
    ⟨9, 12, 14, 28⟩,
    ⟨10, 12, 14, 28⟩,
    ⟨11, 12, 14, 28⟩,
    ⟨9, 13, 14, 28⟩,
    ⟨10, 13, 14, 28⟩,
    ⟨11, 13, 14, 28⟩,
    ⟨12, 13, 14, 28⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_9_10_14_28, box_9_11_14_28, box_10_11_14_28, box_9_12_14_28, box_10_12_14_28, box_11_12_14_28, box_9_13_14_28, box_10_13_14_28, box_11_13_14_28, box_12_13_14_28]
  all_goals decide +kernel

private theorem box_8_9_15_28 : boxUpper ⟨8, 9, 15, 28⟩ = 14988208222954812 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_15_28 : boxUpper ⟨8, 10, 15, 28⟩ = 13913908349831036 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_15_28 : boxUpper ⟨9, 10, 15, 28⟩ = 12791754592364397 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_15_28 : boxUpper ⟨8, 11, 15, 28⟩ = 13058092849272554 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_15_28 : boxUpper ⟨9, 11, 15, 28⟩ = 15200221050900463 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_15_28 : boxUpper ⟨10, 11, 15, 28⟩ = 21285753398597835 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_15_28 : boxUpper ⟨8, 12, 15, 28⟩ = 15632916269454049 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_15_28 : boxUpper ⟨9, 12, 15, 28⟩ = 21648868165018988 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_15_28 : boxUpper ⟨10, 12, 15, 28⟩ = 21137552203592629 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_15_28 : boxUpper ⟨11, 12, 15, 28⟩ = 19885450552441353 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_15_28 : boxUpper ⟨8, 13, 15, 28⟩ = 22413692814876201 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_15_28 : boxUpper ⟨9, 13, 15, 28⟩ = 21639361313497104 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_15_28 : boxUpper ⟨10, 13, 15, 28⟩ = 20169900479101764 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_15_28 : boxUpper ⟨11, 13, 15, 28⟩ = 18993411507092776 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_15_28 : boxUpper ⟨8, 14, 15, 28⟩ = 22530997506855504 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_15_28 : boxUpper ⟨9, 14, 15, 28⟩ = 20763996038104058 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_15_28 : boxUpper ⟨10, 14, 15, 28⟩ = 19372637815082034 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 28 15 = 315426723129037557 := by
  have members : atPair 28 15 = [
    ⟨8, 9, 15, 28⟩,
    ⟨8, 10, 15, 28⟩,
    ⟨9, 10, 15, 28⟩,
    ⟨8, 11, 15, 28⟩,
    ⟨9, 11, 15, 28⟩,
    ⟨10, 11, 15, 28⟩,
    ⟨8, 12, 15, 28⟩,
    ⟨9, 12, 15, 28⟩,
    ⟨10, 12, 15, 28⟩,
    ⟨11, 12, 15, 28⟩,
    ⟨8, 13, 15, 28⟩,
    ⟨9, 13, 15, 28⟩,
    ⟨10, 13, 15, 28⟩,
    ⟨11, 13, 15, 28⟩,
    ⟨8, 14, 15, 28⟩,
    ⟨9, 14, 15, 28⟩,
    ⟨10, 14, 15, 28⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_15_28, box_8_10_15_28, box_9_10_15_28, box_8_11_15_28, box_9_11_15_28, box_10_11_15_28, box_8_12_15_28, box_9_12_15_28, box_10_12_15_28, box_11_12_15_28, box_8_13_15_28, box_9_13_15_28, box_10_13_15_28, box_11_13_15_28, box_8_14_15_28, box_9_14_15_28, box_10_14_15_28]
  all_goals decide +kernel

private theorem box_7_8_16_28 : boxUpper ⟨7, 8, 16, 28⟩ = 17414871664510234 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_16_28 : boxUpper ⟨7, 9, 16, 28⟩ = 15973237946254975 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_16_28 : boxUpper ⟨8, 9, 16, 28⟩ = 14453711764674362 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_16_28 : boxUpper ⟨7, 10, 16, 28⟩ = 14828324462564906 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_16_28 : boxUpper ⟨8, 10, 16, 28⟩ = 13427411030404835 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_16_28 : boxUpper ⟨9, 10, 16, 28⟩ = 12353920401847514 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_16_28 : boxUpper ⟨7, 11, 16, 28⟩ = 13903569885013309 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_16_28 : boxUpper ⟨8, 11, 16, 28⟩ = 12611139054323631 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_16_28 : boxUpper ⟨9, 11, 16, 28⟩ = 14693366070732425 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_16_28 : boxUpper ⟨10, 11, 16, 28⟩ = 20592072935135176 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_16_28 : boxUpper ⟨7, 12, 16, 28⟩ = 13159232837159894 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_16_28 : boxUpper ⟨8, 12, 16, 28⟩ = 15111626731392252 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_16_28 : boxUpper ⟨9, 12, 16, 28⟩ = 20943349962662077 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_16_28 : boxUpper ⟨10, 12, 16, 28⟩ = 20466495119494327 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_16_28 : boxUpper ⟨11, 12, 16, 28⟩ = 19272702881543286 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_16_28 : boxUpper ⟨7, 13, 16, 28⟩ = 15864481498593027 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_16_28 : boxUpper ⟨8, 13, 16, 28⟩ = 21683240451230690 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_16_28 : boxUpper ⟨9, 13, 16, 28⟩ = 20952366512065217 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_16_28 : boxUpper ⟨10, 13, 16, 28⟩ = 19548383983537369 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_16_28 : boxUpper ⟨7, 14, 16, 28⟩ = 22896930241587179 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_16_28 : boxUpper ⟨8, 14, 16, 28⟩ = 21815683112031745 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_16_28 : boxUpper ⟨9, 14, 16, 28⟩ = 20124164830418432 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_16_28 : boxUpper ⟨7, 15, 16, 28⟩ = 23151578238668186 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_16_28 : boxUpper ⟨8, 15, 16, 28⟩ = 21054556063824089 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 28 16 = 426296417679669137 := by
  have members : atPair 28 16 = [
    ⟨7, 8, 16, 28⟩,
    ⟨7, 9, 16, 28⟩,
    ⟨8, 9, 16, 28⟩,
    ⟨7, 10, 16, 28⟩,
    ⟨8, 10, 16, 28⟩,
    ⟨9, 10, 16, 28⟩,
    ⟨7, 11, 16, 28⟩,
    ⟨8, 11, 16, 28⟩,
    ⟨9, 11, 16, 28⟩,
    ⟨10, 11, 16, 28⟩,
    ⟨7, 12, 16, 28⟩,
    ⟨8, 12, 16, 28⟩,
    ⟨9, 12, 16, 28⟩,
    ⟨10, 12, 16, 28⟩,
    ⟨11, 12, 16, 28⟩,
    ⟨7, 13, 16, 28⟩,
    ⟨8, 13, 16, 28⟩,
    ⟨9, 13, 16, 28⟩,
    ⟨10, 13, 16, 28⟩,
    ⟨7, 14, 16, 28⟩,
    ⟨8, 14, 16, 28⟩,
    ⟨9, 14, 16, 28⟩,
    ⟨7, 15, 16, 28⟩,
    ⟨8, 15, 16, 28⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_16_28, box_7_9_16_28, box_8_9_16_28, box_7_10_16_28, box_8_10_16_28, box_9_10_16_28, box_7_11_16_28, box_8_11_16_28, box_9_11_16_28, box_10_11_16_28, box_7_12_16_28, box_8_12_16_28, box_9_12_16_28, box_10_12_16_28, box_11_12_16_28, box_7_13_16_28, box_8_13_16_28, box_9_13_16_28, box_10_13_16_28, box_7_14_16_28, box_8_14_16_28, box_9_14_16_28, box_7_15_16_28, box_8_15_16_28]
  all_goals decide +kernel

private theorem box_6_7_17_28 : boxUpper ⟨6, 7, 17, 28⟩ = 20997221981127902 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_17_28 : boxUpper ⟨6, 8, 17, 28⟩ = 18974379216993170 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_17_28 : boxUpper ⟨7, 8, 17, 28⟩ = 16844774785354385 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_17_28 : boxUpper ⟨6, 9, 17, 28⟩ = 17403630083291594 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_17_28 : boxUpper ⟨7, 9, 17, 28⟩ = 15460914894550282 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_17_28 : boxUpper ⟨8, 9, 17, 28⟩ = 14000231472926385 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_17_28 : boxUpper ⟨6, 10, 17, 28⟩ = 16156174137538344 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_17_28 : boxUpper ⟨7, 10, 17, 28⟩ = 14363085751271013 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_17_28 : boxUpper ⟨8, 10, 17, 28⟩ = 13016047658538147 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_17_28 : boxUpper ⟨9, 10, 17, 28⟩ = 11985116943267897 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_17_28 : boxUpper ⟨6, 11, 17, 28⟩ = 15148593360823515 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_17_28 : boxUpper ⟨7, 11, 17, 28⟩ = 13477612294342160 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_17_28 : boxUpper ⟨8, 11, 17, 28⟩ = 12234653296625825 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_17_28 : boxUpper ⟨9, 11, 17, 28⟩ = 14268524968392047 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_17_28 : boxUpper ⟨10, 11, 17, 28⟩ = 20013280271515371 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_17_28 : boxUpper ⟨6, 12, 17, 28⟩ = 14324554196703860 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_17_28 : boxUpper ⟨7, 12, 17, 28⟩ = 12766376793303943 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_17_28 : boxUpper ⟨8, 12, 17, 28⟩ = 14674685705282713 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_17_28 : boxUpper ⟨9, 12, 17, 28⟩ = 20354679419215910 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_17_28 : boxUpper ⟨10, 12, 17, 28⟩ = 19909634349574599 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_17_28 : boxUpper ⟨6, 13, 17, 28⟩ = 13657066537181956 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_17_28 : boxUpper ⟨7, 13, 17, 28⟩ = 15405760121369951 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_17_28 : boxUpper ⟨8, 13, 17, 28⟩ = 21073763774206937 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_17_28 : boxUpper ⟨9, 13, 17, 28⟩ = 20382279011942232 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_17_28 : boxUpper ⟨6, 14, 17, 28⟩ = 16561367647842341 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_17_28 : boxUpper ⟨7, 14, 17, 28⟩ = 22253322530493118 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_17_28 : boxUpper ⟨8, 14, 17, 28⟩ = 21222093012018192 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_17_28 : boxUpper ⟨6, 15, 17, 28⟩ = 24048910799339874 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_17_28 : boxUpper ⟨7, 15, 17, 28⟩ = 22521618243298634 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_17_28 : boxUpper ⟨6, 16, 17, 28⟩ = 24447252126839725 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 28 17 = 517947605385172022 := by
  have members : atPair 28 17 = [
    ⟨6, 7, 17, 28⟩,
    ⟨6, 8, 17, 28⟩,
    ⟨7, 8, 17, 28⟩,
    ⟨6, 9, 17, 28⟩,
    ⟨7, 9, 17, 28⟩,
    ⟨8, 9, 17, 28⟩,
    ⟨6, 10, 17, 28⟩,
    ⟨7, 10, 17, 28⟩,
    ⟨8, 10, 17, 28⟩,
    ⟨9, 10, 17, 28⟩,
    ⟨6, 11, 17, 28⟩,
    ⟨7, 11, 17, 28⟩,
    ⟨8, 11, 17, 28⟩,
    ⟨9, 11, 17, 28⟩,
    ⟨10, 11, 17, 28⟩,
    ⟨6, 12, 17, 28⟩,
    ⟨7, 12, 17, 28⟩,
    ⟨8, 12, 17, 28⟩,
    ⟨9, 12, 17, 28⟩,
    ⟨10, 12, 17, 28⟩,
    ⟨6, 13, 17, 28⟩,
    ⟨7, 13, 17, 28⟩,
    ⟨8, 13, 17, 28⟩,
    ⟨9, 13, 17, 28⟩,
    ⟨6, 14, 17, 28⟩,
    ⟨7, 14, 17, 28⟩,
    ⟨8, 14, 17, 28⟩,
    ⟨6, 15, 17, 28⟩,
    ⟨7, 15, 17, 28⟩,
    ⟨6, 16, 17, 28⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_17_28, box_6_8_17_28, box_7_8_17_28, box_6_9_17_28, box_7_9_17_28, box_8_9_17_28, box_6_10_17_28, box_7_10_17_28, box_8_10_17_28, box_9_10_17_28, box_6_11_17_28, box_7_11_17_28, box_8_11_17_28, box_9_11_17_28, box_10_11_17_28, box_6_12_17_28, box_7_12_17_28, box_8_12_17_28, box_9_12_17_28, box_10_12_17_28, box_6_13_17_28, box_7_13_17_28, box_8_13_17_28, box_9_13_17_28, box_6_14_17_28, box_7_14_17_28, box_8_14_17_28, box_6_15_17_28, box_7_15_17_28, box_6_16_17_28]
  all_goals decide +kernel

private theorem box_5_6_18_28 : boxUpper ⟨5, 6, 18, 28⟩ = 26535606064047056 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_18_28 : boxUpper ⟨5, 7, 18, 28⟩ = 23527420923868360 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_18_28 : boxUpper ⟨6, 7, 18, 28⟩ = 20363696294632987 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_18_28 : boxUpper ⟨5, 8, 18, 28⟩ = 21260794054764066 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_18_28 : boxUpper ⟨6, 8, 18, 28⟩ = 18413854546703291 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_18_28 : boxUpper ⟨7, 8, 18, 28⟩ = 16358362082641052 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_18_28 : boxUpper ⟨5, 9, 18, 28⟩ = 19500742158327989 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_18_28 : boxUpper ⟨6, 9, 18, 28⟩ = 16901071618520860 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_18_28 : boxUpper ⟨7, 9, 18, 28⟩ = 15025304542990403 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_18_28 : boxUpper ⟨8, 9, 18, 28⟩ = 13616154261701041 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_18_28 : boxUpper ⟨5, 10, 18, 28⟩ = 18102942873050326 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_18_28 : boxUpper ⟨6, 10, 18, 28⟩ = 15700964595591254 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_18_28 : boxUpper ⟨7, 10, 18, 28⟩ = 13969048914529890 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_18_28 : boxUpper ⟨8, 10, 18, 28⟩ = 12669178739698949 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_18_28 : boxUpper ⟨9, 10, 18, 28⟩ = 11675702958719709 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_18_28 : boxUpper ⟨5, 11, 18, 28⟩ = 16973925317400649 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_18_28 : boxUpper ⟨6, 11, 18, 28⟩ = 14732995008967009 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_18_28 : boxUpper ⟨7, 11, 18, 28⟩ = 13118436216337897 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_18_28 : boxUpper ⟨8, 11, 18, 28⟩ = 11918793525397237 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_18_28 : boxUpper ⟨9, 11, 18, 28⟩ = 13914445556737041 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_18_28 : boxUpper ⟨10, 11, 18, 28⟩ = 19533869701497532 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_18_28 : boxUpper ⟨5, 12, 18, 28⟩ = 16050567026256366 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_18_28 : boxUpper ⟨6, 12, 18, 28⟩ = 13942794057707828 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_18_28 : boxUpper ⟨7, 12, 18, 28⟩ = 12436781552313378 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_18_28 : boxUpper ⟨8, 12, 18, 28⟩ = 14310520598930045 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_18_28 : boxUpper ⟨9, 12, 18, 28⟩ = 19867086249198483 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_18_28 : boxUpper ⟨5, 13, 18, 28⟩ = 15288788498530765 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_18_28 : boxUpper ⟨6, 13, 18, 28⟩ = 13304461518021525 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_18_28 : boxUpper ⟨7, 13, 18, 28⟩ = 15023440196943960 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_18_28 : boxUpper ⟨8, 13, 18, 28⟩ = 20568935210663061 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_18_28 : boxUpper ⟨5, 14, 18, 28⟩ = 14670114082342842 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_18_28 : boxUpper ⟨6, 14, 18, 28⟩ = 16150347983915548 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_18_28 : boxUpper ⟨7, 14, 18, 28⟩ = 21720220226017324 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_15_18_28 : boxUpper ⟨5, 15, 18, 28⟩ = 17875575902207130 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_18_28 : boxUpper ⟨6, 15, 18, 28⟩ = 23472765206815851 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_16_18_28 : boxUpper ⟨5, 16, 18, 28⟩ = 26107919621971408 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 28 18 = 614603627887960112 := by
  have members : atPair 28 18 = [
    ⟨5, 6, 18, 28⟩,
    ⟨5, 7, 18, 28⟩,
    ⟨6, 7, 18, 28⟩,
    ⟨5, 8, 18, 28⟩,
    ⟨6, 8, 18, 28⟩,
    ⟨7, 8, 18, 28⟩,
    ⟨5, 9, 18, 28⟩,
    ⟨6, 9, 18, 28⟩,
    ⟨7, 9, 18, 28⟩,
    ⟨8, 9, 18, 28⟩,
    ⟨5, 10, 18, 28⟩,
    ⟨6, 10, 18, 28⟩,
    ⟨7, 10, 18, 28⟩,
    ⟨8, 10, 18, 28⟩,
    ⟨9, 10, 18, 28⟩,
    ⟨5, 11, 18, 28⟩,
    ⟨6, 11, 18, 28⟩,
    ⟨7, 11, 18, 28⟩,
    ⟨8, 11, 18, 28⟩,
    ⟨9, 11, 18, 28⟩,
    ⟨10, 11, 18, 28⟩,
    ⟨5, 12, 18, 28⟩,
    ⟨6, 12, 18, 28⟩,
    ⟨7, 12, 18, 28⟩,
    ⟨8, 12, 18, 28⟩,
    ⟨9, 12, 18, 28⟩,
    ⟨5, 13, 18, 28⟩,
    ⟨6, 13, 18, 28⟩,
    ⟨7, 13, 18, 28⟩,
    ⟨8, 13, 18, 28⟩,
    ⟨5, 14, 18, 28⟩,
    ⟨6, 14, 18, 28⟩,
    ⟨7, 14, 18, 28⟩,
    ⟨5, 15, 18, 28⟩,
    ⟨6, 15, 18, 28⟩,
    ⟨5, 16, 18, 28⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_18_28, box_5_7_18_28, box_6_7_18_28, box_5_8_18_28, box_6_8_18_28, box_7_8_18_28, box_5_9_18_28, box_6_9_18_28, box_7_9_18_28, box_8_9_18_28, box_5_10_18_28, box_6_10_18_28, box_7_10_18_28, box_8_10_18_28, box_9_10_18_28, box_5_11_18_28, box_6_11_18_28, box_7_11_18_28, box_8_11_18_28, box_9_11_18_28, box_10_11_18_28, box_5_12_18_28, box_6_12_18_28, box_7_12_18_28, box_8_12_18_28, box_9_12_18_28, box_5_13_18_28, box_6_13_18_28, box_7_13_18_28, box_8_13_18_28, box_5_14_18_28, box_6_14_18_28, box_7_14_18_28, box_5_15_18_28, box_6_15_18_28, box_5_16_18_28]
  all_goals decide +kernel

theorem column_28 : columnUpper 28 = 2139826970781123385 := by
  unfold columnUpper
  have indices : List.range 28 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_13, pair_14, pair_15, pair_16, pair_17, pair_18]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_28
