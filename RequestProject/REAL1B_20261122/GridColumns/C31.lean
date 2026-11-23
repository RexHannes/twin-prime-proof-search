import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_9_10_11_31 : boxUpper ⟨9, 10, 11, 31⟩ = 30376174795791690 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_11 : pairUpper 31 11 = 30376174795791690 := by
  have members : atPair 31 11 = [
    ⟨9, 10, 11, 31⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_9_10_11_31]
  all_goals decide +kernel

private theorem box_8_9_12_31 : boxUpper ⟨8, 9, 12, 31⟩ = 21301149593758231 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_12_31 : boxUpper ⟨8, 10, 12, 31⟩ = 29790612455341033 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_12_31 : boxUpper ⟨9, 10, 12, 31⟩ = 28701953543377900 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_12_31 : boxUpper ⟨8, 11, 12, 31⟩ = 29299607848711132 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_12_31 : boxUpper ⟨9, 11, 12, 31⟩ = 26932514970345670 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_12_31 : boxUpper ⟨10, 11, 12, 31⟩ = 25059428131716261 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_12 : pairUpper 31 12 = 161085266543250227 := by
  have members : atPair 31 12 = [
    ⟨8, 9, 12, 31⟩,
    ⟨8, 10, 12, 31⟩,
    ⟨9, 10, 12, 31⟩,
    ⟨8, 11, 12, 31⟩,
    ⟨9, 11, 12, 31⟩,
    ⟨10, 11, 12, 31⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_12_31, box_8_10_12_31, box_9_10_12_31, box_8_11_12_31, box_9_11_12_31, box_10_11_12_31]
  all_goals decide +kernel

private theorem box_7_8_13_31 : boxUpper ⟨7, 8, 13, 31⟩ = 19272106614991075 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_13_31 : boxUpper ⟨7, 9, 13, 31⟩ = 17692598095419821 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_13_31 : boxUpper ⟨8, 9, 13, 31⟩ = 20245669797957575 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_13_31 : boxUpper ⟨7, 10, 13, 31⟩ = 20765194453649079 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_13_31 : boxUpper ⟨8, 10, 13, 31⟩ = 28333205526527793 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_13_31 : boxUpper ⟨9, 10, 13, 31⟩ = 27317783309425607 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_13_31 : boxUpper ⟨7, 11, 13, 31⟩ = 29334791235115481 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_13_31 : boxUpper ⟨8, 11, 13, 31⟩ = 27886607829368815 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_13_31 : boxUpper ⟨9, 11, 13, 31⟩ = 25654350989621704 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_13_31 : boxUpper ⟨7, 12, 13, 31⟩ = 29098692195986736 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_13_31 : boxUpper ⟨8, 12, 13, 31⟩ = 26390951837926250 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_13 : pairUpper 31 13 = 271991951885989936 := by
  have members : atPair 31 13 = [
    ⟨7, 8, 13, 31⟩,
    ⟨7, 9, 13, 31⟩,
    ⟨8, 9, 13, 31⟩,
    ⟨7, 10, 13, 31⟩,
    ⟨8, 10, 13, 31⟩,
    ⟨9, 10, 13, 31⟩,
    ⟨7, 11, 13, 31⟩,
    ⟨8, 11, 13, 31⟩,
    ⟨9, 11, 13, 31⟩,
    ⟨7, 12, 13, 31⟩,
    ⟨8, 12, 13, 31⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_13_31, box_7_9_13_31, box_8_9_13_31, box_7_10_13_31, box_8_10_13_31, box_9_10_13_31, box_7_11_13_31, box_8_11_13_31, box_9_11_13_31, box_7_12_13_31, box_8_12_13_31]
  all_goals decide +kernel

private theorem box_6_7_14_31 : boxUpper ⟨6, 7, 14, 31⟩ = 22942232672322381 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_14_31 : boxUpper ⟨6, 8, 14, 31⟩ = 20732001086957248 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_14_31 : boxUpper ⟨7, 8, 14, 31⟩ = 18405119947169885 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_14_31 : boxUpper ⟨6, 9, 14, 31⟩ = 19015742471276525 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_14_31 : boxUpper ⟨7, 9, 14, 31⟩ = 16908254505175531 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_14_31 : boxUpper ⟨8, 9, 14, 31⟩ = 19363976226437558 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_14_31 : boxUpper ⟨6, 10, 14, 31⟩ = 17668525348042504 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_14_31 : boxUpper ⟨7, 10, 14, 31⟩ = 19860868040205918 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_14_31 : boxUpper ⟨8, 10, 14, 31⟩ = 27118231171069002 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_14_31 : boxUpper ⟨9, 10, 14, 31⟩ = 26166590430799236 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_14_31 : boxUpper ⟨6, 11, 14, 31⟩ = 20935690316295393 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_14_31 : boxUpper ⟨7, 11, 14, 31⟩ = 28076855060990231 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_14_31 : boxUpper ⟨8, 11, 14, 31⟩ = 26711436613460420 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_14_31 : boxUpper ⟨6, 12, 14, 31⟩ = 29835320888187710 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_14_31 : boxUpper ⟨7, 12, 14, 31⟩ = 27872425509735964 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_14_31 : boxUpper ⟨6, 13, 14, 31⟩ = 29817214590005302 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 31 14 = 371430484878130808 := by
  have members : atPair 31 14 = [
    ⟨6, 7, 14, 31⟩,
    ⟨6, 8, 14, 31⟩,
    ⟨7, 8, 14, 31⟩,
    ⟨6, 9, 14, 31⟩,
    ⟨7, 9, 14, 31⟩,
    ⟨8, 9, 14, 31⟩,
    ⟨6, 10, 14, 31⟩,
    ⟨7, 10, 14, 31⟩,
    ⟨8, 10, 14, 31⟩,
    ⟨9, 10, 14, 31⟩,
    ⟨6, 11, 14, 31⟩,
    ⟨7, 11, 14, 31⟩,
    ⟨8, 11, 14, 31⟩,
    ⟨6, 12, 14, 31⟩,
    ⟨7, 12, 14, 31⟩,
    ⟨6, 13, 14, 31⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_14_31, box_6_8_14_31, box_7_8_14_31, box_6_9_14_31, box_7_9_14_31, box_8_9_14_31, box_6_10_14_31, box_7_10_14_31, box_8_10_14_31, box_9_10_14_31, box_6_11_14_31, box_7_11_14_31, box_8_11_14_31, box_6_12_14_31, box_7_12_14_31, box_6_13_14_31]
  all_goals decide +kernel

private theorem box_5_6_15_31 : boxUpper ⟨5, 6, 15, 31⟩ = 28670019760374144 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_15_31 : boxUpper ⟨5, 7, 15, 31⟩ = 25419859687822127 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_15_31 : boxUpper ⟨6, 7, 15, 31⟩ = 22001651203815435 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_15_31 : boxUpper ⟨5, 8, 15, 31⟩ = 22970907075426667 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_15_31 : boxUpper ⟨6, 8, 15, 31⟩ = 19894966015083163 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_15_31 : boxUpper ⟨7, 8, 15, 31⟩ = 17674133459562087 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_15_31 : boxUpper ⟨5, 9, 15, 31⟩ = 21069277034411514 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_15_31 : boxUpper ⟨6, 9, 15, 31⟩ = 18260495395173880 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_15_31 : boxUpper ⟨7, 9, 15, 31⟩ = 16248458325096879 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_15_31 : boxUpper ⟨8, 9, 15, 31⟩ = 18624433828630616 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_15_31 : boxUpper ⟨5, 10, 15, 31⟩ = 19559038186906229 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_15_31 : boxUpper ⟨6, 10, 15, 31⟩ = 16979050572794909 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_15_31 : boxUpper ⟨7, 10, 15, 31⟩ = 19102340712926344 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_15_31 : boxUpper ⟨8, 10, 15, 31⟩ = 26101810324055125 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_15_31 : boxUpper ⟨5, 11, 15, 31⟩ = 18355489561381702 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_15_31 : boxUpper ⟨6, 11, 15, 31⟩ = 20136095502868864 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_15_31 : boxUpper ⟨7, 11, 15, 31⟩ = 27024491536928652 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_15_31 : boxUpper ⟨5, 12, 15, 31⟩ = 21916382597166238 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_15_31 : boxUpper ⟨6, 12, 15, 31⟩ = 28717023184845285 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_15_31 : boxUpper ⟨5, 13, 15, 31⟩ = 31479081317394387 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 31 15 = 440205005282664247 := by
  have members : atPair 31 15 = [
    ⟨5, 6, 15, 31⟩,
    ⟨5, 7, 15, 31⟩,
    ⟨6, 7, 15, 31⟩,
    ⟨5, 8, 15, 31⟩,
    ⟨6, 8, 15, 31⟩,
    ⟨7, 8, 15, 31⟩,
    ⟨5, 9, 15, 31⟩,
    ⟨6, 9, 15, 31⟩,
    ⟨7, 9, 15, 31⟩,
    ⟨8, 9, 15, 31⟩,
    ⟨5, 10, 15, 31⟩,
    ⟨6, 10, 15, 31⟩,
    ⟨7, 10, 15, 31⟩,
    ⟨8, 10, 15, 31⟩,
    ⟨5, 11, 15, 31⟩,
    ⟨6, 11, 15, 31⟩,
    ⟨7, 11, 15, 31⟩,
    ⟨5, 12, 15, 31⟩,
    ⟨6, 12, 15, 31⟩,
    ⟨5, 13, 15, 31⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_15_31, box_5_7_15_31, box_6_7_15_31, box_5_8_15_31, box_6_8_15_31, box_7_8_15_31, box_5_9_15_31, box_6_9_15_31, box_7_9_15_31, box_8_9_15_31, box_5_10_15_31, box_6_10_15_31, box_7_10_15_31, box_8_10_15_31, box_5_11_15_31, box_6_11_15_31, box_7_11_15_31, box_5_12_15_31, box_6_12_15_31, box_5_13_15_31]
  all_goals decide +kernel

private theorem box_4_5_16_31 : boxUpper ⟨4, 5, 16, 31⟩ = 38214970894376379 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_16_31 : boxUpper ⟨4, 6, 16, 31⟩ = 33036147366254437 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_16_31 : boxUpper ⟨5, 6, 16, 31⟩ = 27593573853687389 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_16_31 : boxUpper ⟨4, 7, 16, 31⟩ = 29290968963103342 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_16_31 : boxUpper ⟨5, 7, 16, 31⟩ = 24480578460025496 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_16_31 : boxUpper ⟨6, 7, 16, 31⟩ = 21202469446453038 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_16_31 : boxUpper ⟨4, 8, 16, 31⟩ = 26469021129194854 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_16_31 : boxUpper ⟨5, 8, 16, 31⟩ = 22136502928473655 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_16_31 : boxUpper ⟨6, 8, 16, 31⟩ = 19185437996788084 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_16_31 : boxUpper ⟨7, 8, 16, 31⟩ = 17056123862711604 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_16_31 : boxUpper ⟨4, 9, 16, 31⟩ = 24277752004851526 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_16_31 : boxUpper ⟨5, 9, 16, 31⟩ = 20317849864472525 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_16_31 : boxUpper ⟨6, 9, 16, 31⟩ = 17621973565771873 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_16_31 : boxUpper ⟨7, 9, 16, 31⟩ = 15692272751771069 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_16_31 : boxUpper ⟨8, 9, 16, 31⟩ = 18003360479733745 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_16_31 : boxUpper ⟨4, 10, 16, 31⟩ = 22537481605481088 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_16_31 : boxUpper ⟨5, 10, 16, 31⟩ = 18875088426772187 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_16_31 : boxUpper ⟨6, 10, 16, 31⟩ = 16397845354035818 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_16_31 : boxUpper ⟨7, 10, 16, 31⟩ = 18465322504766886 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_11_16_31 : boxUpper ⟨4, 11, 16, 31⟩ = 21131839469421679 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_16_31 : boxUpper ⟨5, 11, 16, 31⟩ = 17727144559502161 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_16_31 : boxUpper ⟨6, 11, 16, 31⟩ = 19464585771357662 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_12_16_31 : boxUpper ⟨4, 12, 16, 31⟩ = 19999742720851257 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_16_31 : boxUpper ⟨5, 12, 16, 31⟩ = 21185468631051047 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_13_16_31 : boxUpper ⟨4, 13, 16, 31⟩ = 24020616939781222 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 31 16 = 554384139550690023 := by
  have members : atPair 31 16 = [
    ⟨4, 5, 16, 31⟩,
    ⟨4, 6, 16, 31⟩,
    ⟨5, 6, 16, 31⟩,
    ⟨4, 7, 16, 31⟩,
    ⟨5, 7, 16, 31⟩,
    ⟨6, 7, 16, 31⟩,
    ⟨4, 8, 16, 31⟩,
    ⟨5, 8, 16, 31⟩,
    ⟨6, 8, 16, 31⟩,
    ⟨7, 8, 16, 31⟩,
    ⟨4, 9, 16, 31⟩,
    ⟨5, 9, 16, 31⟩,
    ⟨6, 9, 16, 31⟩,
    ⟨7, 9, 16, 31⟩,
    ⟨8, 9, 16, 31⟩,
    ⟨4, 10, 16, 31⟩,
    ⟨5, 10, 16, 31⟩,
    ⟨6, 10, 16, 31⟩,
    ⟨7, 10, 16, 31⟩,
    ⟨4, 11, 16, 31⟩,
    ⟨5, 11, 16, 31⟩,
    ⟨6, 11, 16, 31⟩,
    ⟨4, 12, 16, 31⟩,
    ⟨5, 12, 16, 31⟩,
    ⟨4, 13, 16, 31⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_16_31, box_4_6_16_31, box_5_6_16_31, box_4_7_16_31, box_5_7_16_31, box_6_7_16_31, box_4_8_16_31, box_5_8_16_31, box_6_8_16_31, box_7_8_16_31, box_4_9_16_31, box_5_9_16_31, box_6_9_16_31, box_7_9_16_31, box_8_9_16_31, box_4_10_16_31, box_5_10_16_31, box_6_10_16_31, box_7_10_16_31, box_4_11_16_31, box_5_11_16_31, box_6_11_16_31, box_4_12_16_31, box_5_12_16_31, box_4_13_16_31]
  all_goals decide +kernel

theorem column_31 : columnUpper 31 = 1829473022936516931 := by
  unfold columnUpper
  have indices : List.range 31 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_11, pair_12, pair_13, pair_14, pair_15, pair_16]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_31
