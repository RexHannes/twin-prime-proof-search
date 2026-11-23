import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_12_13_14_25 : boxUpper ⟨12, 13, 14, 25⟩ = 19049465418513809 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 25 14 = 19049465418513809 := by
  have members : atPair 25 14 = [
    ⟨12, 13, 14, 25⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_12_13_14_25]
  all_goals decide +kernel

private theorem box_11_12_15_25 : boxUpper ⟨11, 12, 15, 25⟩ = 12901956362062169 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_15_25 : boxUpper ⟨11, 13, 15, 25⟩ = 18483690429151870 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_15_25 : boxUpper ⟨12, 13, 15, 25⟩ = 18350558531604266 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_15_25 : boxUpper ⟨11, 14, 15, 25⟩ = 18573400361340687 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_15_25 : boxUpper ⟨12, 14, 15, 25⟩ = 17608262322347277 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_15_25 : boxUpper ⟨13, 14, 15, 25⟩ = 16818394631442049 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 25 15 = 102736262637948318 := by
  have members : atPair 25 15 = [
    ⟨11, 12, 15, 25⟩,
    ⟨11, 13, 15, 25⟩,
    ⟨12, 13, 15, 25⟩,
    ⟨11, 14, 15, 25⟩,
    ⟨12, 14, 15, 25⟩,
    ⟨13, 14, 15, 25⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_11_12_15_25, box_11_13_15_25, box_12_13_15_25, box_11_14_15_25, box_12_14_15_25, box_13_14_15_25]
  all_goals decide +kernel

private theorem box_10_11_16_25 : boxUpper ⟨10, 11, 16, 25⟩ = 11068808856984038 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_16_25 : boxUpper ⟨10, 12, 16, 25⟩ = 10476399267526042 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_16_25 : boxUpper ⟨11, 12, 16, 25⟩ = 12471757427838012 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_16_25 : boxUpper ⟨10, 13, 16, 25⟩ = 12648850564661881 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_16_25 : boxUpper ⟨11, 13, 16, 25⟩ = 17881346072418525 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_16_25 : boxUpper ⟨12, 13, 16, 25⟩ = 17768004052740714 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_16_25 : boxUpper ⟨10, 14, 16, 25⟩ = 18237552251912445 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_16_25 : boxUpper ⟨11, 14, 16, 25⟩ = 17983768986428103 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_16_25 : boxUpper ⟨12, 14, 16, 25⟩ = 17065703151383560 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_16_25 : boxUpper ⟨13, 14, 16, 25⟩ = 16316907508298387 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_16_25 : boxUpper ⟨10, 15, 16, 25⟩ = 18431445059160206 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_16_25 : boxUpper ⟨11, 15, 16, 25⟩ = 17356371713780084 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_16_25 : boxUpper ⟨12, 15, 16, 25⟩ = 16487245059118187 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_16_25 : boxUpper ⟨13, 15, 16, 25⟩ = 15781105605236629 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_16_25 : boxUpper ⟨14, 15, 16, 25⟩ = 15207334666996643 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 25 16 = 235182600244483456 := by
  have members : atPair 25 16 = [
    ⟨10, 11, 16, 25⟩,
    ⟨10, 12, 16, 25⟩,
    ⟨11, 12, 16, 25⟩,
    ⟨10, 13, 16, 25⟩,
    ⟨11, 13, 16, 25⟩,
    ⟨12, 13, 16, 25⟩,
    ⟨10, 14, 16, 25⟩,
    ⟨11, 14, 16, 25⟩,
    ⟨12, 14, 16, 25⟩,
    ⟨13, 14, 16, 25⟩,
    ⟨10, 15, 16, 25⟩,
    ⟨11, 15, 16, 25⟩,
    ⟨12, 15, 16, 25⟩,
    ⟨13, 15, 16, 25⟩,
    ⟨14, 15, 16, 25⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_10_11_16_25, box_10_12_16_25, box_11_12_16_25, box_10_13_16_25, box_11_13_16_25, box_12_13_16_25, box_10_14_16_25, box_11_14_16_25, box_12_14_16_25, box_13_14_16_25, box_10_15_16_25, box_11_15_16_25, box_12_15_16_25, box_13_15_16_25, box_14_15_16_25]
  all_goals decide +kernel

private theorem box_9_10_17_25 : boxUpper ⟨9, 10, 17, 25⟩ = 12308605127618355 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_17_25 : boxUpper ⟨9, 11, 17, 25⟩ = 11541010075083731 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_17_25 : boxUpper ⟨10, 11, 17, 25⟩ = 10729722440936229 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_17_25 : boxUpper ⟨9, 12, 17, 25⟩ = 10913244713781083 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_17_25 : boxUpper ⟨10, 12, 17, 25⟩ = 10163660638786996 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_17_25 : boxUpper ⟨11, 12, 17, 25⟩ = 12111171932423048 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_17_25 : boxUpper ⟨9, 13, 17, 25⟩ = 10404933494556258 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_17_25 : boxUpper ⟨10, 13, 17, 25⟩ = 12283142602870331 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_17_25 : boxUpper ⟨11, 13, 17, 25⟩ = 17378765735017043 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_17_25 : boxUpper ⟨12, 13, 17, 25⟩ = 17284589249382542 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_17_25 : boxUpper ⟨9, 14, 17, 25⟩ = 12642201838348937 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_17_25 : boxUpper ⟨10, 14, 17, 25⟩ = 17724956337503525 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_17_25 : boxUpper ⟨11, 14, 17, 25⟩ = 17494481179081040 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_17_25 : boxUpper ⟨12, 14, 17, 25⟩ = 16618437199444332 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_17_25 : boxUpper ⟨13, 14, 17, 25⟩ = 15906677384081728 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_17_25 : boxUpper ⟨9, 15, 17, 25⟩ = 18333717864053598 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_17_25 : boxUpper ⟨10, 15, 17, 25⟩ = 17929971548177072 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_17_25 : boxUpper ⟨11, 15, 17, 25⟩ = 16901484042352999 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_17_25 : boxUpper ⟨12, 15, 17, 25⟩ = 16072730170964485 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_17_25 : boxUpper ⟨13, 15, 17, 25⟩ = 15402378007167218 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_17_25 : boxUpper ⟨9, 16, 17, 25⟩ = 18625532886328840 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_17_25 : boxUpper ⟨10, 16, 17, 25⟩ = 17395325327967939 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_17_25 : boxUpper ⟨11, 16, 17, 25⟩ = 16415477429583222 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_17_25 : boxUpper ⟨12, 16, 17, 25⟩ = 15628855579676997 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 25 17 = 358211072805187548 := by
  have members : atPair 25 17 = [
    ⟨9, 10, 17, 25⟩,
    ⟨9, 11, 17, 25⟩,
    ⟨10, 11, 17, 25⟩,
    ⟨9, 12, 17, 25⟩,
    ⟨10, 12, 17, 25⟩,
    ⟨11, 12, 17, 25⟩,
    ⟨9, 13, 17, 25⟩,
    ⟨10, 13, 17, 25⟩,
    ⟨11, 13, 17, 25⟩,
    ⟨12, 13, 17, 25⟩,
    ⟨9, 14, 17, 25⟩,
    ⟨10, 14, 17, 25⟩,
    ⟨11, 14, 17, 25⟩,
    ⟨12, 14, 17, 25⟩,
    ⟨13, 14, 17, 25⟩,
    ⟨9, 15, 17, 25⟩,
    ⟨10, 15, 17, 25⟩,
    ⟨11, 15, 17, 25⟩,
    ⟨12, 15, 17, 25⟩,
    ⟨13, 15, 17, 25⟩,
    ⟨9, 16, 17, 25⟩,
    ⟨10, 16, 17, 25⟩,
    ⟨11, 16, 17, 25⟩,
    ⟨12, 16, 17, 25⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_9_10_17_25, box_9_11_17_25, box_10_11_17_25, box_9_12_17_25, box_10_12_17_25, box_11_12_17_25, box_9_13_17_25, box_10_13_17_25, box_11_13_17_25, box_12_13_17_25, box_9_14_17_25, box_10_14_17_25, box_11_14_17_25, box_12_14_17_25, box_13_14_17_25, box_9_15_17_25, box_10_15_17_25, box_11_15_17_25, box_12_15_17_25, box_13_15_17_25, box_9_16_17_25, box_10_16_17_25, box_11_16_17_25, box_12_16_17_25]
  all_goals decide +kernel

private theorem box_8_9_18_25 : boxUpper ⟨8, 9, 18, 25⟩ = 14028585560194427 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_18_25 : boxUpper ⟨8, 10, 18, 25⟩ = 13023072726483845 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_18_25 : boxUpper ⟨9, 10, 18, 25⟩ = 11961836062782117 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_18_25 : boxUpper ⟨8, 11, 18, 25⟩ = 12210914672397342 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_18_25 : boxUpper ⟨9, 11, 18, 25⟩ = 11224417705197083 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_18_25 : boxUpper ⟨10, 11, 18, 25⟩ = 10443801721794157 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_18_25 : boxUpper ⟨8, 12, 18, 25⟩ = 11546703278152144 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_18_25 : boxUpper ⟨9, 12, 18, 25⟩ = 10622431315187177 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_18_25 : boxUpper ⟨10, 12, 18, 25⟩ = 9901285709472119 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_18_25 : boxUpper ⟨11, 12, 18, 25⟩ = 11810649319024472 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_18_25 : boxUpper ⟨8, 13, 18, 25⟩ = 10998729360802394 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_18_25 : boxUpper ⟨9, 13, 18, 25⟩ = 10136327033306722 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_18_25 : boxUpper ⟨10, 13, 18, 25⟩ = 11978350362724471 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_18_25 : boxUpper ⟨11, 13, 18, 25⟩ = 16962485199927899 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_18_25 : boxUpper ⟨12, 13, 18, 25⟩ = 16887194943046715 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_18_25 : boxUpper ⟨8, 14, 18, 25⟩ = 10553956812407434 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_18_25 : boxUpper ⟨9, 14, 18, 25⟩ = 12328494783852755 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_18_25 : boxUpper ⟨10, 14, 18, 25⟩ = 17300379306978373 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_18_25 : boxUpper ⟨11, 14, 18, 25⟩ = 17092258404641331 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_18_25 : boxUpper ⟨12, 14, 18, 25⟩ = 16254147949938721 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_18_25 : boxUpper ⟨13, 14, 18, 25⟩ = 15576227183716274 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_18_25 : boxUpper ⟨8, 15, 18, 25⟩ = 12893965643743970 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_18_25 : boxUpper ⟨9, 15, 18, 25⟩ = 17894551413325931 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_18_25 : boxUpper ⟨10, 15, 18, 25⟩ = 17517730303166499 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_18_25 : boxUpper ⟨11, 15, 18, 25⟩ = 16530986272857092 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_18_25 : boxUpper ⟨12, 15, 18, 25⟩ = 15738827993124060 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_18_25 : boxUpper ⟨8, 16, 18, 25⟩ = 18798609071479347 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_18_25 : boxUpper ⟨9, 16, 18, 25⟩ = 18197289632481332 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_18_25 : boxUpper ⟨10, 16, 18, 25⟩ = 17013995033022261 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_18_25 : boxUpper ⟨11, 16, 18, 25⟩ = 16074449919726839 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_17_18_25 : boxUpper ⟨8, 17, 18, 25⟩ = 19190076759678953 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_17_18_25 : boxUpper ⟨9, 17, 18, 25⟩ = 17739756789695159 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_17_18_25 : boxUpper ⟨10, 17, 18, 25⟩ = 16605661623771474 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 25 18 = 477038149868100889 := by
  have members : atPair 25 18 = [
    ⟨8, 9, 18, 25⟩,
    ⟨8, 10, 18, 25⟩,
    ⟨9, 10, 18, 25⟩,
    ⟨8, 11, 18, 25⟩,
    ⟨9, 11, 18, 25⟩,
    ⟨10, 11, 18, 25⟩,
    ⟨8, 12, 18, 25⟩,
    ⟨9, 12, 18, 25⟩,
    ⟨10, 12, 18, 25⟩,
    ⟨11, 12, 18, 25⟩,
    ⟨8, 13, 18, 25⟩,
    ⟨9, 13, 18, 25⟩,
    ⟨10, 13, 18, 25⟩,
    ⟨11, 13, 18, 25⟩,
    ⟨12, 13, 18, 25⟩,
    ⟨8, 14, 18, 25⟩,
    ⟨9, 14, 18, 25⟩,
    ⟨10, 14, 18, 25⟩,
    ⟨11, 14, 18, 25⟩,
    ⟨12, 14, 18, 25⟩,
    ⟨13, 14, 18, 25⟩,
    ⟨8, 15, 18, 25⟩,
    ⟨9, 15, 18, 25⟩,
    ⟨10, 15, 18, 25⟩,
    ⟨11, 15, 18, 25⟩,
    ⟨12, 15, 18, 25⟩,
    ⟨8, 16, 18, 25⟩,
    ⟨9, 16, 18, 25⟩,
    ⟨10, 16, 18, 25⟩,
    ⟨11, 16, 18, 25⟩,
    ⟨8, 17, 18, 25⟩,
    ⟨9, 17, 18, 25⟩,
    ⟨10, 17, 18, 25⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_18_25, box_8_10_18_25, box_9_10_18_25, box_8_11_18_25, box_9_11_18_25, box_10_11_18_25, box_8_12_18_25, box_9_12_18_25, box_10_12_18_25, box_11_12_18_25, box_8_13_18_25, box_9_13_18_25, box_10_13_18_25, box_11_13_18_25, box_12_13_18_25, box_8_14_18_25, box_9_14_18_25, box_10_14_18_25, box_11_14_18_25, box_12_14_18_25, box_13_14_18_25, box_8_15_18_25, box_9_15_18_25, box_10_15_18_25, box_11_15_18_25, box_12_15_18_25, box_8_16_18_25, box_9_16_18_25, box_10_16_18_25, box_11_16_18_25, box_8_17_18_25, box_9_17_18_25, box_10_17_18_25]
  all_goals decide +kernel

private theorem box_5_6_21_25 : boxUpper ⟨5, 6, 21, 25⟩ = 25512944364875620 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_21_25 : boxUpper ⟨5, 7, 21, 25⟩ = 22620696204568673 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_21_25 : boxUpper ⟨6, 7, 21, 25⟩ = 19578902062459439 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_21_25 : boxUpper ⟨5, 8, 21, 25⟩ = 20441426667625901 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_21_25 : boxUpper ⟨6, 8, 21, 25⟩ = 17704208385531619 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_21_25 : boxUpper ⟨7, 8, 21, 25⟩ = 15727935069598218 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_21_25 : boxUpper ⟨5, 9, 21, 25⟩ = 18749208748208619 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_21_25 : boxUpper ⟨6, 9, 21, 25⟩ = 16249729382600025 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_21_25 : boxUpper ⟨7, 9, 21, 25⟩ = 14446254616895985 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_21_25 : boxUpper ⟨8, 9, 21, 25⟩ = 13091413512987248 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_21_25 : boxUpper ⟨5, 10, 21, 25⟩ = 17405282295957425 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_21_25 : boxUpper ⟨6, 10, 21, 25⟩ = 15095875866381865 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_21_25 : boxUpper ⟨7, 10, 21, 25⟩ = 13430708274053849 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_21_25 : boxUpper ⟨8, 10, 21, 25⟩ = 12180935484872111 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_21_25 : boxUpper ⟨9, 10, 21, 25⟩ = 11215462852327122 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_21_25 : boxUpper ⟨5, 11, 21, 25⟩ = 16319778820260281 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_21_25 : boxUpper ⟨6, 11, 21, 25⟩ = 14165213332187592 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_21_25 : boxUpper ⟨7, 11, 21, 25⟩ = 12612879530140092 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_21_25 : boxUpper ⟨8, 11, 21, 25⟩ = 11448990082348743 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_21_25 : boxUpper ⟨9, 11, 21, 25⟩ = 10551095583430205 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_21_25 : boxUpper ⟨10, 11, 21, 25⟩ = 9844082179678205 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_21_25 : boxUpper ⟨5, 12, 21, 25⟩ = 15432008617332650 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_21_25 : boxUpper ⟨6, 12, 21, 25⟩ = 13405468366418509 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_21_25 : boxUpper ⟨7, 12, 21, 25⟩ = 11946602570478262 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_21_25 : boxUpper ⟨8, 12, 21, 25⟩ = 10854035079761015 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_21_25 : boxUpper ⟨9, 12, 21, 25⟩ = 10012447022188921 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_21_25 : boxUpper ⟨10, 12, 21, 25⟩ = 9359814079160308 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_21_25 : boxUpper ⟨11, 12, 21, 25⟩ = 11203885334571784 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_21_25 : boxUpper ⟨5, 13, 21, 25⟩ = 14699591031577685 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_21_25 : boxUpper ⟨6, 13, 21, 25⟩ = 12780158921034043 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_21_25 : boxUpper ⟨7, 13, 21, 25⟩ = 11399679864566319 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_21_25 : boxUpper ⟨8, 13, 21, 25⟩ = 10367120726747445 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_21_25 : boxUpper ⟨9, 13, 21, 25⟩ = 9581991830865996 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_21_25 : boxUpper ⟨10, 13, 21, 25⟩ = 11362963076367648 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_21_25 : boxUpper ⟨11, 13, 21, 25⟩ = 16139626678100206 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_21_25 : boxUpper ⟨5, 14, 21, 25⟩ = 14092122379273324 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_21_25 : boxUpper ⟨6, 14, 21, 25⟩ = 12263136748742021 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_21_25 : boxUpper ⟨7, 14, 21, 25⟩ = 10949058678679149 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_21_25 : boxUpper ⟨8, 14, 21, 25⟩ = 9976764031341312 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_21_25 : boxUpper ⟨9, 14, 21, 25⟩ = 11695102123861976 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_21_25 : boxUpper ⟨10, 14, 21, 25⟩ = 16461116160773233 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_15_21_25 : boxUpper ⟨5, 15, 21, 25⟩ = 13587317218300764 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_21_25 : boxUpper ⟨6, 15, 21, 25⟩ = 11835262410185192 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_21_25 : boxUpper ⟨7, 15, 21, 25⟩ = 10587627767588718 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_21_25 : boxUpper ⟨8, 15, 21, 25⟩ = 12231492915813855 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_21_25 : boxUpper ⟨9, 15, 21, 25⟩ = 17026440195965726 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_16_21_25 : boxUpper ⟨5, 16, 21, 25⟩ = 13168567322543481 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_21_25 : boxUpper ⟨6, 16, 21, 25⟩ = 11492792505126646 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_21_25 : boxUpper ⟨7, 16, 21, 25⟩ = 13028461862614217 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_21_25 : boxUpper ⟨8, 16, 21, 25⟩ = 17886601248063590 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_17_21_25 : boxUpper ⟨5, 17, 21, 25⟩ = 12834937253824065 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_17_21_25 : boxUpper ⟨6, 17, 21, 25⟩ = 14184269529567685 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_17_21_25 : boxUpper ⟨7, 17, 21, 25⟩ = 19129503637971503 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_18_21_25 : boxUpper ⟨5, 18, 21, 25⟩ = 15875618606741336 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_18_21_25 : boxUpper ⟨6, 18, 21, 25⟩ = 20905866835155444 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_21 : pairUpper 25 21 = 776150475948292865 := by
  have members : atPair 25 21 = [
    ⟨5, 6, 21, 25⟩,
    ⟨5, 7, 21, 25⟩,
    ⟨6, 7, 21, 25⟩,
    ⟨5, 8, 21, 25⟩,
    ⟨6, 8, 21, 25⟩,
    ⟨7, 8, 21, 25⟩,
    ⟨5, 9, 21, 25⟩,
    ⟨6, 9, 21, 25⟩,
    ⟨7, 9, 21, 25⟩,
    ⟨8, 9, 21, 25⟩,
    ⟨5, 10, 21, 25⟩,
    ⟨6, 10, 21, 25⟩,
    ⟨7, 10, 21, 25⟩,
    ⟨8, 10, 21, 25⟩,
    ⟨9, 10, 21, 25⟩,
    ⟨5, 11, 21, 25⟩,
    ⟨6, 11, 21, 25⟩,
    ⟨7, 11, 21, 25⟩,
    ⟨8, 11, 21, 25⟩,
    ⟨9, 11, 21, 25⟩,
    ⟨10, 11, 21, 25⟩,
    ⟨5, 12, 21, 25⟩,
    ⟨6, 12, 21, 25⟩,
    ⟨7, 12, 21, 25⟩,
    ⟨8, 12, 21, 25⟩,
    ⟨9, 12, 21, 25⟩,
    ⟨10, 12, 21, 25⟩,
    ⟨11, 12, 21, 25⟩,
    ⟨5, 13, 21, 25⟩,
    ⟨6, 13, 21, 25⟩,
    ⟨7, 13, 21, 25⟩,
    ⟨8, 13, 21, 25⟩,
    ⟨9, 13, 21, 25⟩,
    ⟨10, 13, 21, 25⟩,
    ⟨11, 13, 21, 25⟩,
    ⟨5, 14, 21, 25⟩,
    ⟨6, 14, 21, 25⟩,
    ⟨7, 14, 21, 25⟩,
    ⟨8, 14, 21, 25⟩,
    ⟨9, 14, 21, 25⟩,
    ⟨10, 14, 21, 25⟩,
    ⟨5, 15, 21, 25⟩,
    ⟨6, 15, 21, 25⟩,
    ⟨7, 15, 21, 25⟩,
    ⟨8, 15, 21, 25⟩,
    ⟨9, 15, 21, 25⟩,
    ⟨5, 16, 21, 25⟩,
    ⟨6, 16, 21, 25⟩,
    ⟨7, 16, 21, 25⟩,
    ⟨8, 16, 21, 25⟩,
    ⟨5, 17, 21, 25⟩,
    ⟨6, 17, 21, 25⟩,
    ⟨7, 17, 21, 25⟩,
    ⟨5, 18, 21, 25⟩,
    ⟨6, 18, 21, 25⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_21_25, box_5_7_21_25, box_6_7_21_25, box_5_8_21_25, box_6_8_21_25, box_7_8_21_25, box_5_9_21_25, box_6_9_21_25, box_7_9_21_25, box_8_9_21_25, box_5_10_21_25, box_6_10_21_25, box_7_10_21_25, box_8_10_21_25, box_9_10_21_25, box_5_11_21_25, box_6_11_21_25, box_7_11_21_25, box_8_11_21_25, box_9_11_21_25, box_10_11_21_25, box_5_12_21_25, box_6_12_21_25, box_7_12_21_25, box_8_12_21_25, box_9_12_21_25, box_10_12_21_25, box_11_12_21_25, box_5_13_21_25, box_6_13_21_25, box_7_13_21_25, box_8_13_21_25, box_9_13_21_25, box_10_13_21_25, box_11_13_21_25, box_5_14_21_25, box_6_14_21_25, box_7_14_21_25, box_8_14_21_25, box_9_14_21_25, box_10_14_21_25, box_5_15_21_25, box_6_15_21_25, box_7_15_21_25, box_8_15_21_25, box_9_15_21_25, box_5_16_21_25, box_6_16_21_25, box_7_16_21_25, box_8_16_21_25, box_5_17_21_25, box_6_17_21_25, box_7_17_21_25, box_5_18_21_25, box_6_18_21_25]
  all_goals decide +kernel

private theorem box_4_5_22_25 : boxUpper ⟨4, 5, 22, 25⟩ = 34596621595573448 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_22_25 : boxUpper ⟨4, 6, 22, 25⟩ = 29908162567898806 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_22_25 : boxUpper ⟨5, 6, 22, 25⟩ = 24980922931397532 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_22_25 : boxUpper ⟨4, 7, 22, 25⟩ = 26517603032452410 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_22_25 : boxUpper ⟨5, 7, 22, 25⟩ = 22162686354125480 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_22_25 : boxUpper ⟨6, 7, 22, 25⟩ = 19194967419012591 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_22_25 : boxUpper ⟨4, 8, 22, 25⟩ = 23962857485798957 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_22_25 : boxUpper ⟨5, 8, 22, 25⟩ = 20040564300194034 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_22_25 : boxUpper ⟨6, 8, 22, 25⟩ = 17368922255670426 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_22_25 : boxUpper ⟨7, 8, 22, 25⟩ = 15441224094863155 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_22_25 : boxUpper ⟨4, 9, 22, 25⟩ = 21979074613396129 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_22_25 : boxUpper ⟨5, 9, 22, 25⟩ = 18394115084329134 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_22_25 : boxUpper ⟨6, 9, 22, 25⟩ = 15953498280771490 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_22_25 : boxUpper ⟨7, 9, 22, 25⟩ = 14193722296096387 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_22_25 : boxUpper ⟨8, 9, 22, 25⟩ = 12872941386099890 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_22_25 : boxUpper ⟨4, 10, 22, 25⟩ = 20403587612377988 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_22_25 : boxUpper ⟨5, 10, 22, 25⟩ = 17087966304742211 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_22_25 : boxUpper ⟨6, 10, 22, 25⟩ = 14831977351324658 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_22_25 : boxUpper ⟨7, 10, 22, 25⟩ = 13206568710711431 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_22_25 : boxUpper ⟨8, 10, 22, 25⟩ = 11987889442465796 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_22_25 : boxUpper ⟨9, 10, 22, 25⟩ = 11047726070095005 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_11_22_25 : boxUpper ⟨4, 11, 22, 25⟩ = 19131044692592860 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_22_25 : boxUpper ⟨5, 11, 22, 25⟩ = 16034463711365075 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_22_25 : boxUpper ⟨6, 11, 22, 25⟩ = 13928804006415543 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_22_25 : boxUpper ⟨7, 11, 22, 25⟩ = 12412981153944311 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_22_25 : boxUpper ⟨8, 11, 22, 25⟩ = 11277757077629703 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_22_25 : boxUpper ⟨9, 11, 22, 25⟩ = 10403310731154993 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_22_25 : boxUpper ⟨10, 11, 22, 25⟩ = 9716165338872279 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_12_22_25 : boxUpper ⟨4, 12, 22, 25⟩ = 18090299937825358 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_22_25 : boxUpper ⟨5, 12, 22, 25⟩ = 15174434834868970 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_22_25 : boxUpper ⟨6, 12, 22, 25⟩ = 13192995203245001 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_22_25 : boxUpper ⟨7, 12, 22, 25⟩ = 11767919133371459 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_22_25 : boxUpper ⟨8, 12, 22, 25⟩ = 10702002241387184 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_22_25 : boxUpper ⟨9, 12, 22, 25⟩ = 9882339711671246 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_22_25 : boxUpper ⟨10, 12, 22, 25⟩ = 9248324898690618 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_22_25 : boxUpper ⟨11, 12, 22, 25⟩ = 11085153685082553 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_13_22_25 : boxUpper ⟨4, 13, 22, 25⟩ = 17231670853369000 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_22_25 : boxUpper ⟨5, 13, 22, 25⟩ = 14466582662289509 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_22_25 : boxUpper ⟨6, 13, 22, 25⟩ = 12588993680272093 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_22_25 : boxUpper ⟨7, 13, 22, 25⟩ = 11239995012049698 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_22_25 : boxUpper ⟨8, 13, 22, 25⟩ = 10232398725290226 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_22_25 : boxUpper ⟨9, 13, 22, 25⟩ = 9467852491127661 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_22_25 : boxUpper ⟨10, 13, 22, 25⟩ = 11242542694023345 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_14_22_25 : boxUpper ⟨4, 14, 22, 25⟩ = 16519515353038584 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_22_25 : boxUpper ⟨5, 14, 22, 25⟩ = 13881307791138855 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_22_25 : boxUpper ⟨6, 14, 22, 25⟩ = 12091341163644094 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_22_25 : boxUpper ⟨7, 14, 22, 25⟩ = 10806764163903635 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_22_25 : boxUpper ⟨8, 14, 22, 25⟩ = 9857915386044881 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_22_25 : boxUpper ⟨9, 14, 22, 25⟩ = 11571155562525561 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_15_22_25 : boxUpper ⟨4, 15, 22, 25⟩ = 15927708215235793 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_15_22_25 : boxUpper ⟨5, 15, 22, 25⟩ = 13396944606879277 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_22_25 : boxUpper ⟨6, 15, 22, 25⟩ = 11681434030864192 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_22_25 : boxUpper ⟨7, 15, 22, 25⟩ = 10461490960076856 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_22_25 : boxUpper ⟨8, 15, 22, 25⟩ = 12101850958637499 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_16_22_25 : boxUpper ⟨4, 16, 22, 25⟩ = 15436779493615822 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_16_22_25 : boxUpper ⟨5, 16, 22, 25⟩ = 12997381394149738 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_22_25 : boxUpper ⟨6, 16, 22, 25⟩ = 11355853881346887 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_22_25 : boxUpper ⟨7, 16, 22, 25⟩ = 12890355948909452 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_17_22_25 : boxUpper ⟨4, 17, 22, 25⟩ = 15032047263165385 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_17_22_25 : boxUpper ⟨5, 17, 22, 25⟩ = 12681976882939425 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_17_22_25 : boxUpper ⟨6, 17, 22, 25⟩ = 14033885017722746 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_18_22_25 : boxUpper ⟨4, 18, 22, 25⟩ = 14715456325266954 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_18_22_25 : boxUpper ⟨5, 18, 22, 25⟩ = 15707258295766891 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_22 : pairUpper 25 22 = 947800054360808170 := by
  have members : atPair 25 22 = [
    ⟨4, 5, 22, 25⟩,
    ⟨4, 6, 22, 25⟩,
    ⟨5, 6, 22, 25⟩,
    ⟨4, 7, 22, 25⟩,
    ⟨5, 7, 22, 25⟩,
    ⟨6, 7, 22, 25⟩,
    ⟨4, 8, 22, 25⟩,
    ⟨5, 8, 22, 25⟩,
    ⟨6, 8, 22, 25⟩,
    ⟨7, 8, 22, 25⟩,
    ⟨4, 9, 22, 25⟩,
    ⟨5, 9, 22, 25⟩,
    ⟨6, 9, 22, 25⟩,
    ⟨7, 9, 22, 25⟩,
    ⟨8, 9, 22, 25⟩,
    ⟨4, 10, 22, 25⟩,
    ⟨5, 10, 22, 25⟩,
    ⟨6, 10, 22, 25⟩,
    ⟨7, 10, 22, 25⟩,
    ⟨8, 10, 22, 25⟩,
    ⟨9, 10, 22, 25⟩,
    ⟨4, 11, 22, 25⟩,
    ⟨5, 11, 22, 25⟩,
    ⟨6, 11, 22, 25⟩,
    ⟨7, 11, 22, 25⟩,
    ⟨8, 11, 22, 25⟩,
    ⟨9, 11, 22, 25⟩,
    ⟨10, 11, 22, 25⟩,
    ⟨4, 12, 22, 25⟩,
    ⟨5, 12, 22, 25⟩,
    ⟨6, 12, 22, 25⟩,
    ⟨7, 12, 22, 25⟩,
    ⟨8, 12, 22, 25⟩,
    ⟨9, 12, 22, 25⟩,
    ⟨10, 12, 22, 25⟩,
    ⟨11, 12, 22, 25⟩,
    ⟨4, 13, 22, 25⟩,
    ⟨5, 13, 22, 25⟩,
    ⟨6, 13, 22, 25⟩,
    ⟨7, 13, 22, 25⟩,
    ⟨8, 13, 22, 25⟩,
    ⟨9, 13, 22, 25⟩,
    ⟨10, 13, 22, 25⟩,
    ⟨4, 14, 22, 25⟩,
    ⟨5, 14, 22, 25⟩,
    ⟨6, 14, 22, 25⟩,
    ⟨7, 14, 22, 25⟩,
    ⟨8, 14, 22, 25⟩,
    ⟨9, 14, 22, 25⟩,
    ⟨4, 15, 22, 25⟩,
    ⟨5, 15, 22, 25⟩,
    ⟨6, 15, 22, 25⟩,
    ⟨7, 15, 22, 25⟩,
    ⟨8, 15, 22, 25⟩,
    ⟨4, 16, 22, 25⟩,
    ⟨5, 16, 22, 25⟩,
    ⟨6, 16, 22, 25⟩,
    ⟨7, 16, 22, 25⟩,
    ⟨4, 17, 22, 25⟩,
    ⟨5, 17, 22, 25⟩,
    ⟨6, 17, 22, 25⟩,
    ⟨4, 18, 22, 25⟩,
    ⟨5, 18, 22, 25⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_22_25, box_4_6_22_25, box_5_6_22_25, box_4_7_22_25, box_5_7_22_25, box_6_7_22_25, box_4_8_22_25, box_5_8_22_25, box_6_8_22_25, box_7_8_22_25, box_4_9_22_25, box_5_9_22_25, box_6_9_22_25, box_7_9_22_25, box_8_9_22_25, box_4_10_22_25, box_5_10_22_25, box_6_10_22_25, box_7_10_22_25, box_8_10_22_25, box_9_10_22_25, box_4_11_22_25, box_5_11_22_25, box_6_11_22_25, box_7_11_22_25, box_8_11_22_25, box_9_11_22_25, box_10_11_22_25, box_4_12_22_25, box_5_12_22_25, box_6_12_22_25, box_7_12_22_25, box_8_12_22_25, box_9_12_22_25, box_10_12_22_25, box_11_12_22_25, box_4_13_22_25, box_5_13_22_25, box_6_13_22_25, box_7_13_22_25, box_8_13_22_25, box_9_13_22_25, box_10_13_22_25, box_4_14_22_25, box_5_14_22_25, box_6_14_22_25, box_7_14_22_25, box_8_14_22_25, box_9_14_22_25, box_4_15_22_25, box_5_15_22_25, box_6_15_22_25, box_7_15_22_25, box_8_15_22_25, box_4_16_22_25, box_5_16_22_25, box_6_16_22_25, box_7_16_22_25, box_4_17_22_25, box_5_17_22_25, box_6_17_22_25, box_4_18_22_25, box_5_18_22_25]
  all_goals decide +kernel

theorem column_25 : columnUpper 25 = 2916168081283335055 := by
  unfold columnUpper
  have indices : List.range 25 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_14, pair_15, pair_16, pair_17, pair_18, pair_21, pair_22]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_25
