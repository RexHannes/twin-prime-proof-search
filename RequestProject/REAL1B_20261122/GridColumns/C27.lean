import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_11_12_13_27 : boxUpper ⟨11, 12, 13, 27⟩ = 21664782531688848 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_13 : pairUpper 27 13 = 21664782531688848 := by
  have members : atPair 27 13 = [
    ⟨11, 12, 13, 27⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_11_12_13_27]
  all_goals decide +kernel

private theorem box_10_11_14_27 : boxUpper ⟨10, 11, 14, 27⟩ = 14814033207366200 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_14_27 : boxUpper ⟨10, 12, 14, 27⟩ = 21077844401288878 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_14_27 : boxUpper ⟨11, 12, 14, 27⟩ = 20751852965819756 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_14_27 : boxUpper ⟨10, 13, 14, 27⟩ = 21048703788306904 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_14_27 : boxUpper ⟨11, 13, 14, 27⟩ = 19783934120283814 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_14_27 : boxUpper ⟨12, 13, 14, 27⟩ = 18755882822429491 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 27 14 = 116232251305495043 := by
  have members : atPair 27 14 = [
    ⟨10, 11, 14, 27⟩,
    ⟨10, 12, 14, 27⟩,
    ⟨11, 12, 14, 27⟩,
    ⟨10, 13, 14, 27⟩,
    ⟨11, 13, 14, 27⟩,
    ⟨12, 13, 14, 27⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_10_11_14_27, box_10_12_14_27, box_11_12_14_27, box_10_13_14_27, box_11_13_14_27, box_12_13_14_27]
  all_goals decide +kernel

private theorem box_9_10_15_27 : boxUpper ⟨9, 10, 15, 27⟩ = 12890394934162603 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_15_27 : boxUpper ⟨9, 11, 15, 27⟩ = 12097595912497314 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_15_27 : boxUpper ⟨10, 11, 15, 27⟩ = 14248297375910278 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_15_27 : boxUpper ⟨9, 12, 15, 27⟩ = 14490040317058179 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_15_27 : boxUpper ⟨10, 12, 15, 27⟩ = 20287864978330377 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_15_27 : boxUpper ⟨11, 12, 15, 27⟩ = 19990472443340104 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_15_27 : boxUpper ⟨9, 13, 15, 27⟩ = 20768287892981272 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_15_27 : boxUpper ⟨10, 13, 15, 27⟩ = 20276428372343355 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_15_27 : boxUpper ⟨11, 13, 15, 27⟩ = 19075343033064353 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_15_27 : boxUpper ⟨12, 13, 15, 27⟩ = 18101543481581055 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_15_27 : boxUpper ⟨9, 14, 15, 27⟩ = 20873669671380105 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_15_27 : boxUpper ⟨10, 14, 15, 27⟩ = 19456210321852776 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_15_27 : boxUpper ⟨11, 14, 15, 27⟩ = 18321355931608104 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_15_27 : boxUpper ⟨12, 14, 15, 27⟩ = 17403898920615310 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 27 15 = 248281403586725185 := by
  have members : atPair 27 15 = [
    ⟨9, 10, 15, 27⟩,
    ⟨9, 11, 15, 27⟩,
    ⟨10, 11, 15, 27⟩,
    ⟨9, 12, 15, 27⟩,
    ⟨10, 12, 15, 27⟩,
    ⟨11, 12, 15, 27⟩,
    ⟨9, 13, 15, 27⟩,
    ⟨10, 13, 15, 27⟩,
    ⟨11, 13, 15, 27⟩,
    ⟨12, 13, 15, 27⟩,
    ⟨9, 14, 15, 27⟩,
    ⟨10, 14, 15, 27⟩,
    ⟨11, 14, 15, 27⟩,
    ⟨12, 14, 15, 27⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_9_10_15_27, box_9_11_15_27, box_10_11_15_27, box_9_12_15_27, box_10_12_15_27, box_11_12_15_27, box_9_13_15_27, box_10_13_15_27, box_11_13_15_27, box_12_13_15_27, box_9_14_15_27, box_10_14_15_27, box_11_14_15_27, box_12_14_15_27]
  all_goals decide +kernel

private theorem box_8_9_16_27 : boxUpper ⟨8, 9, 16, 27⟩ = 14589012563369965 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_16_27 : boxUpper ⟨8, 10, 16, 27⟩ = 13543327650236818 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_16_27 : boxUpper ⟨9, 10, 16, 27⟩ = 12439693126341474 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_16_27 : boxUpper ⟨8, 11, 16, 27⟩ = 12698722046641998 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_16_27 : boxUpper ⟨9, 11, 16, 27⟩ = 11683526641684912 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_16_27 : boxUpper ⟨10, 11, 16, 27⟩ = 13773193609688351 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_16_27 : boxUpper ⟨8, 12, 16, 27⟩ = 12018968227946735 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_16_27 : boxUpper ⟨9, 12, 16, 27⟩ = 14006872469536601 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_16_27 : boxUpper ⟨10, 12, 16, 27⟩ = 19626711899698962 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_16_27 : boxUpper ⟨11, 12, 16, 27⟩ = 19355842407682649 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_16_27 : boxUpper ⟨8, 13, 16, 27⟩ = 14498929783047092 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_16_27 : boxUpper ⟨9, 13, 16, 27⟩ = 20091473116050148 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_16_27 : boxUpper ⟨10, 13, 16, 27⟩ = 19632716593794431 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_16_27 : boxUpper ⟨11, 13, 16, 27⟩ = 18487565000052080 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_16_27 : boxUpper ⟨12, 13, 16, 27⟩ = 17561783077759934 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_16_27 : boxUpper ⟨8, 14, 16, 27⟩ = 20917143840307547 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_16_27 : boxUpper ⟨9, 14, 16, 27⟩ = 20210989635667335 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_16_27 : boxUpper ⟨10, 14, 16, 27⟩ = 18856691472925660 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_16_27 : boxUpper ⟨11, 14, 16, 27⟩ = 17775038154008957 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_16_27 : boxUpper ⟨8, 15, 16, 27⟩ = 21145408946498794 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_16_27 : boxUpper ⟨9, 15, 16, 27⟩ = 19505866681155869 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_16_27 : boxUpper ⟨10, 15, 16, 27⟩ = 18217506263494042 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 27 16 = 370636983207590354 := by
  have members : atPair 27 16 = [
    ⟨8, 9, 16, 27⟩,
    ⟨8, 10, 16, 27⟩,
    ⟨9, 10, 16, 27⟩,
    ⟨8, 11, 16, 27⟩,
    ⟨9, 11, 16, 27⟩,
    ⟨10, 11, 16, 27⟩,
    ⟨8, 12, 16, 27⟩,
    ⟨9, 12, 16, 27⟩,
    ⟨10, 12, 16, 27⟩,
    ⟨11, 12, 16, 27⟩,
    ⟨8, 13, 16, 27⟩,
    ⟨9, 13, 16, 27⟩,
    ⟨10, 13, 16, 27⟩,
    ⟨11, 13, 16, 27⟩,
    ⟨12, 13, 16, 27⟩,
    ⟨8, 14, 16, 27⟩,
    ⟨9, 14, 16, 27⟩,
    ⟨10, 14, 16, 27⟩,
    ⟨11, 14, 16, 27⟩,
    ⟨8, 15, 16, 27⟩,
    ⟨9, 15, 16, 27⟩,
    ⟨10, 15, 16, 27⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_16_27, box_8_10_16_27, box_9_10_16_27, box_8_11_16_27, box_9_11_16_27, box_10_11_16_27, box_8_12_16_27, box_9_12_16_27, box_10_12_16_27, box_11_12_16_27, box_8_13_16_27, box_9_13_16_27, box_10_13_16_27, box_11_13_16_27, box_12_13_16_27, box_8_14_16_27, box_9_14_16_27, box_10_14_16_27, box_11_14_16_27, box_8_15_16_27, box_9_15_16_27, box_10_15_16_27]
  all_goals decide +kernel

private theorem box_7_8_17_27 : boxUpper ⟨7, 8, 17, 27⟩ = 17014111522857731 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_17_27 : boxUpper ⟨7, 9, 17, 27⟩ = 15605655319596327 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_17_27 : boxUpper ⟨8, 9, 17, 27⟩ = 14121098888698394 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_17_27 : boxUpper ⟨7, 10, 17, 27⟩ = 14487090893033535 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_17_27 : boxUpper ⟨8, 10, 17, 27⟩ = 13118417437294327 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_17_27 : boxUpper ⟨9, 10, 17, 27⟩ = 12058598325335278 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_17_27 : boxUpper ⟨7, 11, 17, 27⟩ = 13583618851878491 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_17_27 : boxUpper ⟨8, 11, 17, 27⟩ = 12309688475320288 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_17_27 : boxUpper ⟨9, 11, 17, 27⟩ = 11334742057760248 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_17_27 : boxUpper ⟨10, 11, 17, 27⟩ = 13374967554712822 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_17_27 : boxUpper ⟨7, 12, 17, 27⟩ = 12844725968377006 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_17_27 : boxUpper ⟨8, 12, 17, 27⟩ = 11660165389717394 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_17_27 : boxUpper ⟨9, 12, 17, 27⟩ = 13601886672649275 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_17_27 : boxUpper ⟨10, 12, 17, 27⟩ = 19075060645161360 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_17_27 : boxUpper ⟨11, 12, 17, 27⟩ = 18829211633551501 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_17_27 : boxUpper ⟨7, 13, 17, 27⟩ = 12246305271304404 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_17_27 : boxUpper ⟨8, 13, 17, 27⟩ = 14079709635042879 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_17_27 : boxUpper ⟨9, 13, 17, 27⟩ = 19526753177403728 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_17_27 : boxUpper ⟨10, 13, 17, 27⟩ = 19098548935707263 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_17_27 : boxUpper ⟨11, 13, 17, 27⟩ = 18003019633194267 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_17_27 : boxUpper ⟨7, 14, 17, 27⟩ = 14863120530679877 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_17_27 : boxUpper ⟨8, 14, 17, 27⟩ = 20329206119107585 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_17_27 : boxUpper ⟨9, 14, 17, 27⟩ = 19661080276421905 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_17_27 : boxUpper ⟨10, 14, 17, 27⟩ = 18362466422544995 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_17_27 : boxUpper ⟨7, 15, 17, 27⟩ = 21570584234597358 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_17_27 : boxUpper ⟨8, 15, 17, 27⟩ = 20570061932632945 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_17_27 : boxUpper ⟨9, 15, 17, 27⟩ = 18994617680004488 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_17_27 : boxUpper ⟨7, 16, 17, 27⟩ = 21921805926980426 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_17_27 : boxUpper ⟨8, 16, 17, 27⟩ = 19956657492922924 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 27 17 = 472202976904489021 := by
  have members : atPair 27 17 = [
    ⟨7, 8, 17, 27⟩,
    ⟨7, 9, 17, 27⟩,
    ⟨8, 9, 17, 27⟩,
    ⟨7, 10, 17, 27⟩,
    ⟨8, 10, 17, 27⟩,
    ⟨9, 10, 17, 27⟩,
    ⟨7, 11, 17, 27⟩,
    ⟨8, 11, 17, 27⟩,
    ⟨9, 11, 17, 27⟩,
    ⟨10, 11, 17, 27⟩,
    ⟨7, 12, 17, 27⟩,
    ⟨8, 12, 17, 27⟩,
    ⟨9, 12, 17, 27⟩,
    ⟨10, 12, 17, 27⟩,
    ⟨11, 12, 17, 27⟩,
    ⟨7, 13, 17, 27⟩,
    ⟨8, 13, 17, 27⟩,
    ⟨9, 13, 17, 27⟩,
    ⟨10, 13, 17, 27⟩,
    ⟨11, 13, 17, 27⟩,
    ⟨7, 14, 17, 27⟩,
    ⟨8, 14, 17, 27⟩,
    ⟨9, 14, 17, 27⟩,
    ⟨10, 14, 17, 27⟩,
    ⟨7, 15, 17, 27⟩,
    ⟨8, 15, 17, 27⟩,
    ⟨9, 15, 17, 27⟩,
    ⟨7, 16, 17, 27⟩,
    ⟨8, 16, 17, 27⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_17_27, box_7_9_17_27, box_8_9_17_27, box_7_10_17_27, box_8_10_17_27, box_9_10_17_27, box_7_11_17_27, box_8_11_17_27, box_9_11_17_27, box_10_11_17_27, box_7_12_17_27, box_8_12_17_27, box_9_12_17_27, box_10_12_17_27, box_11_12_17_27, box_7_13_17_27, box_8_13_17_27, box_9_13_17_27, box_10_13_17_27, box_11_13_17_27, box_7_14_17_27, box_8_14_17_27, box_9_14_17_27, box_10_14_17_27, box_7_15_17_27, box_8_15_17_27, box_9_15_17_27, box_7_16_17_27, box_8_16_17_27]
  all_goals decide +kernel

private theorem box_6_7_18_27 : boxUpper ⟨6, 7, 18, 27⟩ = 20581803170062566 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_18_27 : boxUpper ⟨6, 8, 18, 27⟩ = 18598983037794004 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_18_27 : boxUpper ⟨7, 8, 18, 27⟩ = 16511513146349705 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_18_27 : boxUpper ⟨6, 9, 18, 27⟩ = 17059311896769748 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_18_27 : boxUpper ⟨7, 9, 18, 27⟩ = 15155033517078752 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_18_27 : boxUpper ⟨8, 9, 18, 27⟩ = 13723250033177295 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_18_27 : boxUpper ⟨6, 10, 18, 27⟩ = 15836537631093993 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_18_27 : boxUpper ⟨7, 10, 18, 27⟩ = 14078925579415399 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_18_27 : boxUpper ⟨8, 10, 18, 27⟩ = 12758538872222384 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_18_27 : boxUpper ⟨9, 10, 18, 27⟩ = 11737253808419205 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_18_27 : boxUpper ⟨6, 11, 18, 27⟩ = 14848892656359786 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_18_27 : boxUpper ⟨7, 11, 18, 27⟩ = 13210971937119837 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_18_27 : boxUpper ⟨8, 11, 18, 27⟩ = 11981649342901219 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_18_27 : boxUpper ⟨9, 11, 18, 27⟩ = 11042124176922747 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_18_27 : boxUpper ⟨10, 11, 18, 27⟩ = 13043071839466110 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_18_27 : boxUpper ⟨6, 12, 18, 27⟩ = 14041157984468712 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_18_27 : boxUpper ⟨7, 12, 18, 27⟩ = 12502421095811582 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_18_27 : boxUpper ⟨8, 12, 18, 27⟩ = 11359141805818577 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_18_27 : boxUpper ⟨9, 12, 18, 27⟩ = 13264356553253252 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_18_27 : boxUpper ⟨10, 12, 18, 27⟩ = 18618132539587428 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_18_27 : boxUpper ⟨11, 12, 18, 27⟩ = 18396288290304710 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_18_27 : boxUpper ⟨6, 13, 18, 27⟩ = 13374773295027464 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_18_27 : boxUpper ⟨7, 13, 18, 27⟩ = 11930141019440475 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_18_27 : boxUpper ⟨8, 13, 18, 27⟩ = 13730314782974378 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_18_27 : boxUpper ⟨9, 13, 18, 27⟩ = 19058999353027350 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_18_27 : boxUpper ⟨10, 13, 18, 27⟩ = 18659429069643194 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_18_27 : boxUpper ⟨6, 14, 18, 27⟩ = 12833713196560490 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_18_27 : boxUpper ⟨7, 14, 18, 27⟩ = 14494271823048696 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_18_27 : boxUpper ⟨8, 14, 18, 27⟩ = 19842219238903941 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_18_27 : boxUpper ⟨9, 14, 18, 27⟩ = 19209018150247869 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_18_27 : boxUpper ⟨6, 15, 18, 27⟩ = 15656297528709780 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_18_27 : boxUpper ⟨7, 15, 18, 27⟩ = 21053842552635037 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_18_27 : boxUpper ⟨8, 15, 18, 27⟩ = 20097085691991592 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_18_27 : boxUpper ⟨6, 16, 18, 27⟩ = 22848487936489991 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_18_27 : boxUpper ⟨7, 16, 18, 27⟩ = 21417726061805625 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_17_18_27 : boxUpper ⟨6, 17, 18, 27⟩ = 23335436741750231 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 27 18 = 575891115356653124 := by
  have members : atPair 27 18 = [
    ⟨6, 7, 18, 27⟩,
    ⟨6, 8, 18, 27⟩,
    ⟨7, 8, 18, 27⟩,
    ⟨6, 9, 18, 27⟩,
    ⟨7, 9, 18, 27⟩,
    ⟨8, 9, 18, 27⟩,
    ⟨6, 10, 18, 27⟩,
    ⟨7, 10, 18, 27⟩,
    ⟨8, 10, 18, 27⟩,
    ⟨9, 10, 18, 27⟩,
    ⟨6, 11, 18, 27⟩,
    ⟨7, 11, 18, 27⟩,
    ⟨8, 11, 18, 27⟩,
    ⟨9, 11, 18, 27⟩,
    ⟨10, 11, 18, 27⟩,
    ⟨6, 12, 18, 27⟩,
    ⟨7, 12, 18, 27⟩,
    ⟨8, 12, 18, 27⟩,
    ⟨9, 12, 18, 27⟩,
    ⟨10, 12, 18, 27⟩,
    ⟨11, 12, 18, 27⟩,
    ⟨6, 13, 18, 27⟩,
    ⟨7, 13, 18, 27⟩,
    ⟨8, 13, 18, 27⟩,
    ⟨9, 13, 18, 27⟩,
    ⟨10, 13, 18, 27⟩,
    ⟨6, 14, 18, 27⟩,
    ⟨7, 14, 18, 27⟩,
    ⟨8, 14, 18, 27⟩,
    ⟨9, 14, 18, 27⟩,
    ⟨6, 15, 18, 27⟩,
    ⟨7, 15, 18, 27⟩,
    ⟨8, 15, 18, 27⟩,
    ⟨6, 16, 18, 27⟩,
    ⟨7, 16, 18, 27⟩,
    ⟨6, 17, 18, 27⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_18_27, box_6_8_18_27, box_7_8_18_27, box_6_9_18_27, box_7_9_18_27, box_8_9_18_27, box_6_10_18_27, box_7_10_18_27, box_8_10_18_27, box_9_10_18_27, box_6_11_18_27, box_7_11_18_27, box_8_11_18_27, box_9_11_18_27, box_10_11_18_27, box_6_12_18_27, box_7_12_18_27, box_8_12_18_27, box_9_12_18_27, box_10_12_18_27, box_11_12_18_27, box_6_13_18_27, box_7_13_18_27, box_8_13_18_27, box_9_13_18_27, box_10_13_18_27, box_6_14_18_27, box_7_14_18_27, box_8_14_18_27, box_9_14_18_27, box_6_15_18_27, box_7_15_18_27, box_8_15_18_27, box_6_16_18_27, box_7_16_18_27, box_6_17_18_27]
  all_goals decide +kernel

theorem column_27 : columnUpper 27 = 1804909512892641575 := by
  unfold columnUpper
  have indices : List.range 27 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_13, pair_14, pair_15, pair_16, pair_17, pair_18]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_27
