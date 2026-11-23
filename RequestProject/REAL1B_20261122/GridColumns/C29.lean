import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_10_11_12_29 : boxUpper ⟨10, 11, 12, 29⟩ = 25285856343788670 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_12 : pairUpper 29 12 = 25285856343788670 := by
  have members : atPair 29 12 = [
    ⟨10, 11, 12, 29⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_10_11_12_29]
  all_goals decide +kernel

private theorem box_9_10_13_29 : boxUpper ⟨9, 10, 13, 29⟩ = 17487701374787247 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_13_29 : boxUpper ⟨9, 11, 13, 29⟩ = 24685900670352348 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_13_29 : boxUpper ⟨10, 11, 13, 29⟩ = 24066454955304767 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_13_29 : boxUpper ⟨9, 12, 13, 29⟩ = 24478090073487501 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_13_29 : boxUpper ⟨10, 12, 13, 29⟩ = 22775718980451599 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_13_29 : boxUpper ⟨11, 12, 13, 29⟩ = 21407163433953251 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_13 : pairUpper 29 13 = 134901029488336713 := by
  have members : atPair 29 13 = [
    ⟨9, 10, 13, 29⟩,
    ⟨9, 11, 13, 29⟩,
    ⟨10, 11, 13, 29⟩,
    ⟨9, 12, 13, 29⟩,
    ⟨10, 12, 13, 29⟩,
    ⟨11, 12, 13, 29⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_9_10_13_29, box_9_11_13_29, box_10_11_13_29, box_9_12_13_29, box_10_12_13_29, box_11_12_13_29]
  all_goals decide +kernel

private theorem box_8_9_14_29 : boxUpper ⟨8, 9, 14, 29⟩ = 15482483099476053 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_14_29 : boxUpper ⟨8, 10, 14, 29⟩ = 14385811823058481 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_14_29 : boxUpper ⟨9, 10, 14, 29⟩ = 16726139492082689 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_14_29 : boxUpper ⟨8, 11, 14, 29⟩ = 17071329876471248 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_14_29 : boxUpper ⟨9, 11, 14, 29⟩ = 23627354119681480 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_14_29 : boxUpper ⟨10, 11, 14, 29⟩ = 23052301314229050 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_14_29 : boxUpper ⟨8, 12, 14, 29⟩ = 24303860925729863 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_14_29 : boxUpper ⟨9, 12, 14, 29⟩ = 23446585250566908 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_14_29 : boxUpper ⟨10, 12, 14, 29⟩ = 21834594352064614 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_14_29 : boxUpper ⟨11, 12, 14, 29⟩ = 20541197606753389 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_14_29 : boxUpper ⟨8, 13, 14, 29⟩ = 24277177046267572 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_14_29 : boxUpper ⟨9, 13, 14, 29⟩ = 22352951363843629 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_14_29 : boxUpper ⟨10, 13, 14, 29⟩ = 20835027618729157 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 29 14 = 267936813888954133 := by
  have members : atPair 29 14 = [
    ⟨8, 9, 14, 29⟩,
    ⟨8, 10, 14, 29⟩,
    ⟨9, 10, 14, 29⟩,
    ⟨8, 11, 14, 29⟩,
    ⟨9, 11, 14, 29⟩,
    ⟨10, 11, 14, 29⟩,
    ⟨8, 12, 14, 29⟩,
    ⟨9, 12, 14, 29⟩,
    ⟨10, 12, 14, 29⟩,
    ⟨11, 12, 14, 29⟩,
    ⟨8, 13, 14, 29⟩,
    ⟨9, 13, 14, 29⟩,
    ⟨10, 13, 14, 29⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_14_29, box_8_10_14_29, box_9_10_14_29, box_8_11_14_29, box_9_11_14_29, box_10_11_14_29, box_8_12_14_29, box_9_12_14_29, box_10_12_14_29, box_11_12_14_29, box_8_13_14_29, box_9_13_14_29, box_10_13_14_29]
  all_goals decide +kernel

private theorem box_7_8_15_29 : boxUpper ⟨7, 8, 15, 29⟩ = 17913554766393278 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_15_29 : boxUpper ⟨7, 9, 15, 29⟩ = 16430636713577637 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_15_29 : boxUpper ⟨8, 9, 15, 29⟩ = 14867596058910752 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_15_29 : boxUpper ⟨7, 10, 15, 29⟩ = 15252935851106588 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_15_29 : boxUpper ⟨8, 10, 15, 29⟩ = 13824467011615921 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_15_29 : boxUpper ⟨9, 10, 15, 29⟩ = 16087363725739059 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_15_29 : boxUpper ⟨7, 11, 15, 29⟩ = 14314663669449335 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_15_29 : boxUpper ⟨8, 11, 15, 29⟩ = 16419366354223782 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_15_29 : boxUpper ⟨9, 11, 15, 29⟩ = 22741801012673610 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_15_29 : boxUpper ⟨10, 11, 15, 29⟩ = 22206497159326974 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_15_29 : boxUpper ⟨7, 12, 15, 29⟩ = 17126416506626303 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_15_29 : boxUpper ⟨8, 12, 15, 29⟩ = 23392944495286635 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_15_29 : boxUpper ⟨9, 12, 15, 29⟩ = 22586309457719383 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_15_29 : boxUpper ⟨10, 12, 15, 29⟩ = 21052536626779210 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_15_29 : boxUpper ⟨7, 13, 15, 29⟩ = 24565503475020707 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_15_29 : boxUpper ⟨8, 13, 15, 29⟩ = 23386414988407203 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_15_29 : boxUpper ⟨9, 13, 15, 29⟩ = 21552320554662105 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_15_29 : boxUpper ⟨7, 14, 15, 29⟩ = 24699207696762555 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_15_29 : boxUpper ⟨8, 14, 15, 29⟩ = 22440357529104553 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 29 15 = 370860893653385590 := by
  have members : atPair 29 15 = [
    ⟨7, 8, 15, 29⟩,
    ⟨7, 9, 15, 29⟩,
    ⟨8, 9, 15, 29⟩,
    ⟨7, 10, 15, 29⟩,
    ⟨8, 10, 15, 29⟩,
    ⟨9, 10, 15, 29⟩,
    ⟨7, 11, 15, 29⟩,
    ⟨8, 11, 15, 29⟩,
    ⟨9, 11, 15, 29⟩,
    ⟨10, 11, 15, 29⟩,
    ⟨7, 12, 15, 29⟩,
    ⟨8, 12, 15, 29⟩,
    ⟨9, 12, 15, 29⟩,
    ⟨10, 12, 15, 29⟩,
    ⟨7, 13, 15, 29⟩,
    ⟨8, 13, 15, 29⟩,
    ⟨9, 13, 15, 29⟩,
    ⟨7, 14, 15, 29⟩,
    ⟨8, 14, 15, 29⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_15_29, box_7_9_15_29, box_8_9_15_29, box_7_10_15_29, box_8_10_15_29, box_9_10_15_29, box_7_11_15_29, box_8_11_15_29, box_9_11_15_29, box_10_11_15_29, box_7_12_15_29, box_8_12_15_29, box_9_12_15_29, box_10_12_15_29, box_7_13_15_29, box_8_13_15_29, box_9_13_15_29, box_7_14_15_29, box_8_14_15_29]
  all_goals decide +kernel

private theorem box_6_7_16_29 : boxUpper ⟨6, 7, 16, 29⟩ = 21518426410277769 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_16_29 : boxUpper ⟨6, 8, 16, 29⟩ = 19445369225458075 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_16_29 : boxUpper ⟨7, 8, 16, 29⟩ = 17262900689257163 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_16_29 : boxUpper ⟨6, 9, 16, 29⟩ = 17835628057683300 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_16_29 : boxUpper ⟨7, 9, 16, 29⟩ = 15844688128775425 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_16_29 : boxUpper ⟨8, 9, 16, 29⟩ = 14347745392089796 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_16_29 : boxUpper ⟨6, 10, 16, 29⟩ = 16557205206820919 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_16_29 : boxUpper ⟨7, 10, 16, 29⟩ = 14719606444835416 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_16_29 : boxUpper ⟨8, 10, 16, 29⟩ = 13351275475565059 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_16_29 : boxUpper ⟨9, 10, 16, 29⟩ = 15550918452074509 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_16_29 : boxUpper ⟨6, 11, 16, 29⟩ = 15524611936360587 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_16_29 : boxUpper ⟨7, 11, 16, 29⟩ = 13824686629293758 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_16_29 : boxUpper ⟨8, 11, 16, 29⟩ = 15871845248359397 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_16_29 : boxUpper ⟨9, 11, 16, 29⟩ = 22000656817488581 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_16_29 : boxUpper ⟨10, 11, 16, 29⟩ = 21501494497551402 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_16_29 : boxUpper ⟨6, 12, 16, 29⟩ = 14693359270731090 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_16_29 : boxUpper ⟨7, 12, 16, 29⟩ = 16555307053967708 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_16_29 : boxUpper ⟨8, 12, 16, 29⟩ = 22630571797607487 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_16_29 : boxUpper ⟨9, 12, 16, 29⟩ = 21869243428109402 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_16_29 : boxUpper ⟨6, 13, 16, 29⟩ = 17699005148934463 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_16_29 : boxUpper ⟨7, 13, 16, 29⟩ = 23764902018469211 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_16_29 : boxUpper ⟨8, 13, 16, 29⟩ = 22643935916328864 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_16_29 : boxUpper ⟨6, 14, 16, 29⟩ = 25559261293288390 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_16_29 : boxUpper ⟨7, 14, 16, 29⟩ = 23915029862361986 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_16_29 : boxUpper ⟨6, 15, 16, 29⟩ = 25850718529188518 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 29 16 = 470338392930878275 := by
  have members : atPair 29 16 = [
    ⟨6, 7, 16, 29⟩,
    ⟨6, 8, 16, 29⟩,
    ⟨7, 8, 16, 29⟩,
    ⟨6, 9, 16, 29⟩,
    ⟨7, 9, 16, 29⟩,
    ⟨8, 9, 16, 29⟩,
    ⟨6, 10, 16, 29⟩,
    ⟨7, 10, 16, 29⟩,
    ⟨8, 10, 16, 29⟩,
    ⟨9, 10, 16, 29⟩,
    ⟨6, 11, 16, 29⟩,
    ⟨7, 11, 16, 29⟩,
    ⟨8, 11, 16, 29⟩,
    ⟨9, 11, 16, 29⟩,
    ⟨10, 11, 16, 29⟩,
    ⟨6, 12, 16, 29⟩,
    ⟨7, 12, 16, 29⟩,
    ⟨8, 12, 16, 29⟩,
    ⟨9, 12, 16, 29⟩,
    ⟨6, 13, 16, 29⟩,
    ⟨7, 13, 16, 29⟩,
    ⟨8, 13, 16, 29⟩,
    ⟨6, 14, 16, 29⟩,
    ⟨7, 14, 16, 29⟩,
    ⟨6, 15, 16, 29⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_16_29, box_6_8_16_29, box_7_8_16_29, box_6_9_16_29, box_7_9_16_29, box_8_9_16_29, box_6_10_16_29, box_7_10_16_29, box_8_10_16_29, box_9_10_16_29, box_6_11_16_29, box_7_11_16_29, box_8_11_16_29, box_9_11_16_29, box_10_11_16_29, box_6_12_16_29, box_7_12_16_29, box_8_12_16_29, box_9_12_16_29, box_6_13_16_29, box_7_13_16_29, box_8_13_16_29, box_6_14_16_29, box_7_14_16_29, box_6_15_16_29]
  all_goals decide +kernel

private theorem box_5_6_17_29 : boxUpper ⟨5, 6, 17, 29⟩ = 27104730158958429 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_17_29 : boxUpper ⟨5, 7, 17, 29⟩ = 24032024497848452 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_17_29 : boxUpper ⟨6, 7, 17, 29⟩ = 20800443915522276 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_17_29 : boxUpper ⟨5, 8, 17, 29⟩ = 21716782060795296 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_17_29 : boxUpper ⟨6, 8, 17, 29⟩ = 18808781228105736 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_17_29 : boxUpper ⟨7, 8, 17, 29⟩ = 16709202240449456 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_17_29 : boxUpper ⟨5, 9, 17, 29⟩ = 19918979601125592 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_17_29 : boxUpper ⟨6, 9, 17, 29⟩ = 17263551347593054 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_17_29 : boxUpper ⟨7, 9, 17, 29⟩ = 15347552633616549 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_17_29 : boxUpper ⟨8, 9, 17, 29⟩ = 13908178556084644 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_17_29 : boxUpper ⟨5, 10, 17, 29⟩ = 18491199312053410 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_17_29 : boxUpper ⟨6, 10, 17, 29⟩ = 16037703586337740 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_17_29 : boxUpper ⟨7, 10, 17, 29⟩ = 14268641705989063 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_17_29 : boxUpper ⟨8, 10, 17, 29⟩ = 12952687735988898 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_17_29 : boxUpper ⟨9, 10, 17, 29⟩ = 15101273692810071 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_17_29 : boxUpper ⟨5, 11, 17, 29⟩ = 17337965532887945 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_17_29 : boxUpper ⟨6, 11, 17, 29⟩ = 15048972077682194 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_17_29 : boxUpper ⟨7, 11, 17, 29⟩ = 13411958754497273 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_17_29 : boxUpper ⟨8, 11, 17, 29⟩ = 15412915997647397 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_17_29 : boxUpper ⟨9, 11, 17, 29⟩ = 21382259244983192 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_17_29 : boxUpper ⟨5, 12, 17, 29⟩ = 16394801933787236 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_17_29 : boxUpper ⟨6, 12, 17, 29⟩ = 14254684111621420 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_17_29 : boxUpper ⟨7, 12, 17, 29⟩ = 16076604388969158 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_17_29 : boxUpper ⟨8, 12, 17, 29⟩ = 21994460171050214 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_17_29 : boxUpper ⟨5, 13, 17, 29⟩ = 15630650302408128 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_17_29 : boxUpper ⟨6, 13, 17, 29⟩ = 17187211731570708 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_17_29 : boxUpper ⟨7, 13, 17, 29⟩ = 23096890337982973 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_17_29 : boxUpper ⟨5, 14, 17, 29⟩ = 18932339935461737 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_17_29 : boxUpper ⟨6, 14, 17, 29⟩ = 24840784914333797 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_15_17_29 : boxUpper ⟨5, 15, 17, 29⟩ = 27513637123009798 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 29 17 = 550977868831171836 := by
  have members : atPair 29 17 = [
    ⟨5, 6, 17, 29⟩,
    ⟨5, 7, 17, 29⟩,
    ⟨6, 7, 17, 29⟩,
    ⟨5, 8, 17, 29⟩,
    ⟨6, 8, 17, 29⟩,
    ⟨7, 8, 17, 29⟩,
    ⟨5, 9, 17, 29⟩,
    ⟨6, 9, 17, 29⟩,
    ⟨7, 9, 17, 29⟩,
    ⟨8, 9, 17, 29⟩,
    ⟨5, 10, 17, 29⟩,
    ⟨6, 10, 17, 29⟩,
    ⟨7, 10, 17, 29⟩,
    ⟨8, 10, 17, 29⟩,
    ⟨9, 10, 17, 29⟩,
    ⟨5, 11, 17, 29⟩,
    ⟨6, 11, 17, 29⟩,
    ⟨7, 11, 17, 29⟩,
    ⟨8, 11, 17, 29⟩,
    ⟨9, 11, 17, 29⟩,
    ⟨5, 12, 17, 29⟩,
    ⟨6, 12, 17, 29⟩,
    ⟨7, 12, 17, 29⟩,
    ⟨8, 12, 17, 29⟩,
    ⟨5, 13, 17, 29⟩,
    ⟨6, 13, 17, 29⟩,
    ⟨7, 13, 17, 29⟩,
    ⟨5, 14, 17, 29⟩,
    ⟨6, 14, 17, 29⟩,
    ⟨5, 15, 17, 29⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_17_29, box_5_7_17_29, box_6_7_17_29, box_5_8_17_29, box_6_8_17_29, box_7_8_17_29, box_5_9_17_29, box_6_9_17_29, box_7_9_17_29, box_8_9_17_29, box_5_10_17_29, box_6_10_17_29, box_7_10_17_29, box_8_10_17_29, box_9_10_17_29, box_5_11_17_29, box_6_11_17_29, box_7_11_17_29, box_8_11_17_29, box_9_11_17_29, box_5_12_17_29, box_6_12_17_29, box_7_12_17_29, box_8_12_17_29, box_5_13_17_29, box_6_13_17_29, box_7_13_17_29, box_5_14_17_29, box_6_14_17_29, box_5_15_17_29]
  all_goals decide +kernel

private theorem box_4_5_18_29 : boxUpper ⟨4, 5, 18, 29⟩ = 36382796696248089 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_18_29 : boxUpper ⟨4, 6, 18, 29⟩ = 31452272677267832 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_18_29 : boxUpper ⟨5, 6, 18, 29⟩ = 26270641983384889 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_18_29 : boxUpper ⟨4, 7, 18, 29⟩ = 27886658058902802 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_18_29 : boxUpper ⟨5, 7, 18, 29⟩ = 23306899794175084 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_18_29 : boxUpper ⟨6, 7, 18, 29⟩ = 20185958912193656 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_18_29 : boxUpper ⟨4, 8, 18, 29⟩ = 25200010032720424 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_18_29 : boxUpper ⟨5, 8, 18, 29⟩ = 21075211997642431 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_18_29 : boxUpper ⟨6, 8, 18, 29⟩ = 18265634728534855 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_18_29 : boxUpper ⟨7, 8, 18, 29⟩ = 16238410225799976 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_18_29 : boxUpper ⟨4, 9, 18, 29⟩ = 23113803100546990 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_18_29 : boxUpper ⟨5, 9, 18, 29⟩ = 19343755614378783 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_18_29 : boxUpper ⟨6, 9, 18, 29⟩ = 16777131662384881 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_18_29 : boxUpper ⟨7, 9, 18, 29⟩ = 14926499332237863 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_18_29 : boxUpper ⟨8, 9, 18, 29⟩ = 13537526688517179 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_18_29 : boxUpper ⟨4, 10, 18, 29⟩ = 21456972019739127 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_18_29 : boxUpper ⟨5, 10, 18, 29⟩ = 17970169025594889 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_18_29 : boxUpper ⟨6, 10, 18, 29⟩ = 15597705483308447 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_18_29 : boxUpper ⟨7, 10, 18, 29⟩ = 13888378036418185 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_18_29 : boxUpper ⟨8, 10, 18, 29⟩ = 12618284022914229 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_18_29 : boxUpper ⟨9, 10, 18, 29⟩ = 14726520412329648 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_11_18_29 : boxUpper ⟨4, 11, 18, 29⟩ = 20118725709400758 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_18_29 : boxUpper ⟨5, 11, 18, 29⟩ = 16862272423143976 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_18_29 : boxUpper ⟨6, 11, 18, 29⟩ = 14647899839405877 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_18_29 : boxUpper ⟨7, 11, 18, 29⟩ = 13065690702432154 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_18_29 : boxUpper ⟨8, 11, 18, 29⟩ = 15030423717655108 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_12_18_29 : boxUpper ⟨4, 12, 18, 29⟩ = 19024244995500694 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_18_29 : boxUpper ⟨5, 12, 18, 29⟩ = 15957838275139678 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_18_29 : boxUpper ⟨6, 12, 18, 29⟩ = 13886644675663312 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_18_29 : boxUpper ⟨7, 12, 18, 29⟩ = 15677630044297309 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_13_18_29 : boxUpper ⟨4, 13, 18, 29⟩ = 18121282270168600 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_18_29 : boxUpper ⟨5, 13, 18, 29⟩ = 15227059925857998 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_18_29 : boxUpper ⟨6, 13, 18, 29⟩ = 16760654322764401 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_14_18_29 : boxUpper ⟨4, 14, 18, 29⟩ = 17387668461690364 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_18_29 : boxUpper ⟨5, 14, 18, 29⟩ = 18462434924403407 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_15_18_29 : boxUpper ⟨4, 15, 18, 29⟩ = 21150200214007278 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 29 18 = 681601911006771173 := by
  have members : atPair 29 18 = [
    ⟨4, 5, 18, 29⟩,
    ⟨4, 6, 18, 29⟩,
    ⟨5, 6, 18, 29⟩,
    ⟨4, 7, 18, 29⟩,
    ⟨5, 7, 18, 29⟩,
    ⟨6, 7, 18, 29⟩,
    ⟨4, 8, 18, 29⟩,
    ⟨5, 8, 18, 29⟩,
    ⟨6, 8, 18, 29⟩,
    ⟨7, 8, 18, 29⟩,
    ⟨4, 9, 18, 29⟩,
    ⟨5, 9, 18, 29⟩,
    ⟨6, 9, 18, 29⟩,
    ⟨7, 9, 18, 29⟩,
    ⟨8, 9, 18, 29⟩,
    ⟨4, 10, 18, 29⟩,
    ⟨5, 10, 18, 29⟩,
    ⟨6, 10, 18, 29⟩,
    ⟨7, 10, 18, 29⟩,
    ⟨8, 10, 18, 29⟩,
    ⟨9, 10, 18, 29⟩,
    ⟨4, 11, 18, 29⟩,
    ⟨5, 11, 18, 29⟩,
    ⟨6, 11, 18, 29⟩,
    ⟨7, 11, 18, 29⟩,
    ⟨8, 11, 18, 29⟩,
    ⟨4, 12, 18, 29⟩,
    ⟨5, 12, 18, 29⟩,
    ⟨6, 12, 18, 29⟩,
    ⟨7, 12, 18, 29⟩,
    ⟨4, 13, 18, 29⟩,
    ⟨5, 13, 18, 29⟩,
    ⟨6, 13, 18, 29⟩,
    ⟨4, 14, 18, 29⟩,
    ⟨5, 14, 18, 29⟩,
    ⟨4, 15, 18, 29⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_18_29, box_4_6_18_29, box_5_6_18_29, box_4_7_18_29, box_5_7_18_29, box_6_7_18_29, box_4_8_18_29, box_5_8_18_29, box_6_8_18_29, box_7_8_18_29, box_4_9_18_29, box_5_9_18_29, box_6_9_18_29, box_7_9_18_29, box_8_9_18_29, box_4_10_18_29, box_5_10_18_29, box_6_10_18_29, box_7_10_18_29, box_8_10_18_29, box_9_10_18_29, box_4_11_18_29, box_5_11_18_29, box_6_11_18_29, box_7_11_18_29, box_8_11_18_29, box_4_12_18_29, box_5_12_18_29, box_6_12_18_29, box_7_12_18_29, box_4_13_18_29, box_5_13_18_29, box_6_13_18_29, box_4_14_18_29, box_5_14_18_29, box_4_15_18_29]
  all_goals decide +kernel

theorem column_29 : columnUpper 29 = 2501902766143286390 := by
  unfold columnUpper
  have indices : List.range 29 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_12, pair_13, pair_14, pair_15, pair_16, pair_17, pair_18]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_29
