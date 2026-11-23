import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_9_10_12_30 : boxUpper ⟨9, 10, 12, 30⟩ = 27508011212879561 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_12_30 : boxUpper ⟨9, 11, 12, 30⟩ = 27050214196517926 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_12_30 : boxUpper ⟨10, 11, 12, 30⟩ = 25148663636634670 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_12 : pairUpper 30 12 = 79706889046032157 := by
  have members : atPair 30 12 = [
    ⟨9, 10, 12, 30⟩,
    ⟨9, 11, 12, 30⟩,
    ⟨10, 11, 12, 30⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_9_10_12_30, box_9_11_12_30, box_10_11_12_30]
  all_goals decide +kernel

private theorem box_8_9_13_30 : boxUpper ⟨8, 9, 13, 30⟩ = 16103436919676482 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_13_30 : boxUpper ⟨8, 10, 13, 30⟩ = 18912120444515867 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_13_30 : boxUpper ⟨9, 10, 13, 30⟩ = 26162289297214988 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_13_30 : boxUpper ⟨8, 11, 13, 30⟩ = 26705475706813715 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_13_30 : boxUpper ⟨9, 11, 13, 30⟩ = 25745712305035519 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_13_30 : boxUpper ⟨10, 11, 13, 30⟩ = 23955172582326396 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_13_30 : boxUpper ⟨8, 12, 13, 30⟩ = 26484946355482188 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_13_30 : boxUpper ⟨9, 12, 13, 30⟩ = 24364899127779711 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_13_30 : boxUpper ⟨10, 12, 13, 30⟩ = 22689766040067642 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_13 : pairUpper 30 13 = 211123818778912508 := by
  have members : atPair 30 13 = [
    ⟨8, 9, 13, 30⟩,
    ⟨8, 10, 13, 30⟩,
    ⟨9, 10, 13, 30⟩,
    ⟨8, 11, 13, 30⟩,
    ⟨9, 11, 13, 30⟩,
    ⟨10, 11, 13, 30⟩,
    ⟨8, 12, 13, 30⟩,
    ⟨9, 12, 13, 30⟩,
    ⟨10, 12, 13, 30⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_13_30, box_8_10_13_30, box_9_10_13_30, box_8_11_13_30, box_9_11_13_30, box_10_11_13_30, box_8_12_13_30, box_9_12_13_30, box_10_12_13_30]
  all_goals decide +kernel

private theorem box_7_8_14_30 : boxUpper ⟨7, 8, 14, 30⟩ = 18525691230976818 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_14_30 : boxUpper ⟨7, 9, 14, 30⟩ = 16992096224783097 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_14_30 : boxUpper ⟨8, 9, 14, 30⟩ = 15389556918095535 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_14_30 : boxUpper ⟨7, 10, 14, 30⟩ = 15788389254082509 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_14_30 : boxUpper ⟨8, 10, 14, 30⟩ = 18088513564542165 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_14_30 : boxUpper ⟨9, 10, 14, 30⟩ = 25040423897410300 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_14_30 : boxUpper ⟨7, 11, 14, 30⟩ = 18723827979608474 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_14_30 : boxUpper ⟨8, 11, 14, 30⟩ = 25560311793701646 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_14_30 : boxUpper ⟨9, 11, 14, 30⟩ = 24660780049196304 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_14_30 : boxUpper ⟨10, 11, 14, 30⟩ = 22965301473533482 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_14_30 : boxUpper ⟨7, 12, 14, 30⟩ = 26667909210447923 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_14_30 : boxUpper ⟨8, 12, 14, 30⟩ = 25368852977105677 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_14_30 : boxUpper ⟨9, 12, 14, 30⟩ = 23358092101732730 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_14_30 : boxUpper ⟨7, 13, 14, 30⟩ = 26644213885285413 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_14_30 : boxUpper ⟨8, 13, 14, 30⟩ = 24185537541012640 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 30 14 = 327959498101514713 := by
  have members : atPair 30 14 = [
    ⟨7, 8, 14, 30⟩,
    ⟨7, 9, 14, 30⟩,
    ⟨8, 9, 14, 30⟩,
    ⟨7, 10, 14, 30⟩,
    ⟨8, 10, 14, 30⟩,
    ⟨9, 10, 14, 30⟩,
    ⟨7, 11, 14, 30⟩,
    ⟨8, 11, 14, 30⟩,
    ⟨9, 11, 14, 30⟩,
    ⟨10, 11, 14, 30⟩,
    ⟨7, 12, 14, 30⟩,
    ⟨8, 12, 14, 30⟩,
    ⟨9, 12, 14, 30⟩,
    ⟨7, 13, 14, 30⟩,
    ⟨8, 13, 14, 30⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_14_30, box_7_9_14_30, box_8_9_14_30, box_7_10_14_30, box_8_10_14_30, box_9_10_14_30, box_7_11_14_30, box_8_11_14_30, box_9_11_14_30, box_10_11_14_30, box_7_12_14_30, box_8_12_14_30, box_9_12_14_30, box_7_13_14_30, box_8_13_14_30]
  all_goals decide +kernel

private theorem box_6_7_15_30 : boxUpper ⟨6, 7, 15, 30⟩ = 22160203338566406 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_15_30 : boxUpper ⟨6, 8, 15, 30⟩ = 20025315257236995 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_15_30 : boxUpper ⟨7, 8, 15, 30⟩ = 17777753205107925 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_15_30 : boxUpper ⟨6, 9, 15, 30⟩ = 18367561721505305 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_15_30 : boxUpper ⟨7, 9, 15, 30⟩ = 16317240905352772 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_15_30 : boxUpper ⟨8, 9, 15, 30⟩ = 14789037060640527 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_15_30 : boxUpper ⟨6, 10, 15, 30⟩ = 17051008131135659 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_15_30 : boxUpper ⟨7, 10, 15, 30⟩ = 15172301067886314 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_15_30 : boxUpper ⟨8, 10, 15, 30⟩ = 17397694352321130 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_15_30 : boxUpper ⟨9, 10, 15, 30⟩ = 24101898346546964 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_15_30 : boxUpper ⟨6, 11, 15, 30⟩ = 16001986126891383 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_15_30 : boxUpper ⟨7, 11, 15, 30⟩ = 18008735835033465 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_15_30 : boxUpper ⟨8, 11, 15, 30⟩ = 24602294380377666 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_15_30 : boxUpper ⟨9, 11, 15, 30⟩ = 23755944242136108 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_15_30 : boxUpper ⟨6, 12, 15, 30⟩ = 19128920564628378 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_15_30 : boxUpper ⟨7, 12, 15, 30⟩ = 25668364427490111 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_15_30 : boxUpper ⟨8, 12, 15, 30⟩ = 24438027286339005 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_15_30 : boxUpper ⟨6, 13, 15, 30⟩ = 27453536302717767 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_15_30 : boxUpper ⟨7, 13, 15, 30⟩ = 25666574578717076 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_15_30 : boxUpper ⟨6, 14, 15, 30⟩ = 27610695988942437 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 30 15 = 415495093119573393 := by
  have members : atPair 30 15 = [
    ⟨6, 7, 15, 30⟩,
    ⟨6, 8, 15, 30⟩,
    ⟨7, 8, 15, 30⟩,
    ⟨6, 9, 15, 30⟩,
    ⟨7, 9, 15, 30⟩,
    ⟨8, 9, 15, 30⟩,
    ⟨6, 10, 15, 30⟩,
    ⟨7, 10, 15, 30⟩,
    ⟨8, 10, 15, 30⟩,
    ⟨9, 10, 15, 30⟩,
    ⟨6, 11, 15, 30⟩,
    ⟨7, 11, 15, 30⟩,
    ⟨8, 11, 15, 30⟩,
    ⟨9, 11, 15, 30⟩,
    ⟨6, 12, 15, 30⟩,
    ⟨7, 12, 15, 30⟩,
    ⟨8, 12, 15, 30⟩,
    ⟨6, 13, 15, 30⟩,
    ⟨7, 13, 15, 30⟩,
    ⟨6, 14, 15, 30⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_15_30, box_6_8_15_30, box_7_8_15_30, box_6_9_15_30, box_7_9_15_30, box_8_9_15_30, box_6_10_15_30, box_7_10_15_30, box_8_10_15_30, box_9_10_15_30, box_6_11_15_30, box_7_11_15_30, box_8_11_15_30, box_9_11_15_30, box_6_12_15_30, box_7_12_15_30, box_8_12_15_30, box_6_13_15_30, box_7_13_15_30, box_6_14_15_30]
  all_goals decide +kernel

private theorem box_5_6_16_30 : boxUpper ⟨5, 6, 16, 30⟩ = 27809647310210591 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_16_30 : boxUpper ⟨5, 7, 16, 30⟩ = 24657026393877813 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_16_30 : boxUpper ⟨6, 7, 16, 30⟩ = 21341399319510730 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_16_30 : boxUpper ⟨5, 8, 16, 30⟩ = 22281568597177860 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_16_30 : boxUpper ⟨6, 8, 16, 30⟩ = 19297937120744310 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_16_30 : boxUpper ⟨7, 8, 16, 30⟩ = 17143752490393116 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_16_30 : boxUpper ⟨5, 9, 16, 30⟩ = 20437008185583737 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_16_30 : boxUpper ⟨6, 9, 16, 30⟩ = 17712518358323103 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_16_30 : boxUpper ⟨7, 9, 16, 30⟩ = 15746688675139369 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_16_30 : boxUpper ⟨8, 9, 16, 30⟩ = 14282821332276274 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_16_30 : boxUpper ⟨5, 10, 16, 30⟩ = 18972093328746141 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_16_30 : boxUpper ⟨6, 10, 16, 30⟩ = 16454788036904124 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_16_30 : boxUpper ⟨7, 10, 16, 30⟩ = 14652961049136599 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_16_30 : boxUpper ⟨8, 10, 16, 30⟩ = 16817540778381545 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_16_30 : boxUpper ⟨9, 10, 16, 30⟩ = 23316418374075246 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_16_30 : boxUpper ⟨5, 11, 16, 30⟩ = 17788865243051717 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_16_30 : boxUpper ⟨6, 11, 16, 30⟩ = 15454233862327071 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_16_30 : boxUpper ⟨7, 11, 16, 30⟩ = 17408196284607480 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_16_30 : boxUpper ⟨8, 11, 16, 30⟩ = 23800500111948825 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_16_30 : boxUpper ⟨5, 12, 16, 30⟩ = 16836165866439357 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_16_30 : boxUpper ⟨6, 12, 16, 30⟩ = 18491006903507652 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_16_30 : boxUpper ⟨7, 12, 16, 30⟩ = 24831812455528600 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_16_30 : boxUpper ⟨5, 13, 16, 30⟩ = 20256213651384552 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_16_30 : boxUpper ⟨6, 13, 16, 30⟩ = 26558778683386124 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_16_30 : boxUpper ⟨5, 14, 16, 30⟩ = 29275391781957846 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 30 16 = 501625334194619782 := by
  have members : atPair 30 16 = [
    ⟨5, 6, 16, 30⟩,
    ⟨5, 7, 16, 30⟩,
    ⟨6, 7, 16, 30⟩,
    ⟨5, 8, 16, 30⟩,
    ⟨6, 8, 16, 30⟩,
    ⟨7, 8, 16, 30⟩,
    ⟨5, 9, 16, 30⟩,
    ⟨6, 9, 16, 30⟩,
    ⟨7, 9, 16, 30⟩,
    ⟨8, 9, 16, 30⟩,
    ⟨5, 10, 16, 30⟩,
    ⟨6, 10, 16, 30⟩,
    ⟨7, 10, 16, 30⟩,
    ⟨8, 10, 16, 30⟩,
    ⟨9, 10, 16, 30⟩,
    ⟨5, 11, 16, 30⟩,
    ⟨6, 11, 16, 30⟩,
    ⟨7, 11, 16, 30⟩,
    ⟨8, 11, 16, 30⟩,
    ⟨5, 12, 16, 30⟩,
    ⟨6, 12, 16, 30⟩,
    ⟨7, 12, 16, 30⟩,
    ⟨5, 13, 16, 30⟩,
    ⟨6, 13, 16, 30⟩,
    ⟨5, 14, 16, 30⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_16_30, box_5_7_16_30, box_6_7_16_30, box_5_8_16_30, box_6_8_16_30, box_7_8_16_30, box_5_9_16_30, box_6_9_16_30, box_7_9_16_30, box_8_9_16_30, box_5_10_16_30, box_6_10_16_30, box_7_10_16_30, box_8_10_16_30, box_9_10_16_30, box_5_11_16_30, box_6_11_16_30, box_7_11_16_30, box_8_11_16_30, box_5_12_16_30, box_6_12_16_30, box_7_12_16_30, box_5_13_16_30, box_6_13_16_30, box_5_14_16_30]
  all_goals decide +kernel

private theorem box_4_5_17_30 : boxUpper ⟨4, 5, 17, 30⟩ = 37206076214380803 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_17_30 : boxUpper ⟨4, 6, 17, 30⟩ = 32163979971445569 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_17_30 : boxUpper ⟨5, 6, 17, 30⟩ = 26865095813844357 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_17_30 : boxUpper ⟨4, 7, 17, 30⟩ = 28517679213295914 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_17_30 : boxUpper ⟨5, 7, 17, 30⟩ = 23834287396650703 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_17_30 : boxUpper ⟨6, 7, 17, 30⟩ = 20642723732842308 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_17_30 : boxUpper ⟨4, 8, 17, 30⟩ = 25770234864246540 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_17_30 : boxUpper ⟨5, 8, 17, 30⟩ = 21552098704931598 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_17_30 : boxUpper ⟨6, 8, 17, 30⟩ = 18678944595862273 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_17_30 : boxUpper ⟨7, 8, 17, 30⟩ = 16605846586075102 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_17_30 : boxUpper ⟨4, 9, 17, 30⟩ = 23636818745097703 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_17_30 : boxUpper ⟨5, 9, 17, 30⟩ = 19781460914076322 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_17_30 : boxUpper ⟨6, 9, 17, 30⟩ = 17156758000925896 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_17_30 : boxUpper ⟨7, 9, 17, 30⟩ = 15264248331117001 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_17_30 : boxUpper ⟨8, 9, 17, 30⟩ = 13856414732125069 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_17_30 : boxUpper ⟨4, 10, 17, 30⟩ = 21942494618636122 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_17_30 : boxUpper ⟨5, 10, 17, 30⟩ = 18376790947976662 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_17_30 : boxUpper ⟨6, 10, 17, 30⟩ = 15950642184830340 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_17_30 : boxUpper ⟨7, 10, 17, 30⟩ = 14215498461767394 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_17_30 : boxUpper ⟨8, 10, 17, 30⟩ = 16331257692154958 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_11_17_30 : boxUpper ⟨4, 11, 17, 30⟩ = 20573964335054072 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_17_30 : boxUpper ⟨5, 11, 17, 30⟩ = 17243823086135642 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_17_30 : boxUpper ⟨6, 11, 17, 30⟩ = 14992836468483518 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_17_30 : boxUpper ⟨7, 11, 17, 30⟩ = 16904824133358510 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_12_17_30 : boxUpper ⟨4, 12, 17, 30⟩ = 19454715648088871 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_17_30 : boxUpper ⟨5, 12, 17, 30⟩ = 16333485677159867 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_17_30 : boxUpper ⟨6, 12, 17, 30⟩ = 17956304665342964 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_13_17_30 : boxUpper ⟨4, 13, 17, 30⟩ = 18547605173393183 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_17_30 : boxUpper ⟨5, 13, 17, 30⟩ = 19670431824868749 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_14_17_30 : boxUpper ⟨4, 14, 17, 30⟩ = 22426455100132823 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 30 17 = 612453797834300833 := by
  have members : atPair 30 17 = [
    ⟨4, 5, 17, 30⟩,
    ⟨4, 6, 17, 30⟩,
    ⟨5, 6, 17, 30⟩,
    ⟨4, 7, 17, 30⟩,
    ⟨5, 7, 17, 30⟩,
    ⟨6, 7, 17, 30⟩,
    ⟨4, 8, 17, 30⟩,
    ⟨5, 8, 17, 30⟩,
    ⟨6, 8, 17, 30⟩,
    ⟨7, 8, 17, 30⟩,
    ⟨4, 9, 17, 30⟩,
    ⟨5, 9, 17, 30⟩,
    ⟨6, 9, 17, 30⟩,
    ⟨7, 9, 17, 30⟩,
    ⟨8, 9, 17, 30⟩,
    ⟨4, 10, 17, 30⟩,
    ⟨5, 10, 17, 30⟩,
    ⟨6, 10, 17, 30⟩,
    ⟨7, 10, 17, 30⟩,
    ⟨8, 10, 17, 30⟩,
    ⟨4, 11, 17, 30⟩,
    ⟨5, 11, 17, 30⟩,
    ⟨6, 11, 17, 30⟩,
    ⟨7, 11, 17, 30⟩,
    ⟨4, 12, 17, 30⟩,
    ⟨5, 12, 17, 30⟩,
    ⟨6, 12, 17, 30⟩,
    ⟨4, 13, 17, 30⟩,
    ⟨5, 13, 17, 30⟩,
    ⟨4, 14, 17, 30⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_17_30, box_4_6_17_30, box_5_6_17_30, box_4_7_17_30, box_5_7_17_30, box_6_7_17_30, box_4_8_17_30, box_5_8_17_30, box_6_8_17_30, box_7_8_17_30, box_4_9_17_30, box_5_9_17_30, box_6_9_17_30, box_7_9_17_30, box_8_9_17_30, box_4_10_17_30, box_5_10_17_30, box_6_10_17_30, box_7_10_17_30, box_8_10_17_30, box_4_11_17_30, box_5_11_17_30, box_6_11_17_30, box_7_11_17_30, box_4_12_17_30, box_5_12_17_30, box_6_12_17_30, box_4_13_17_30, box_5_13_17_30, box_4_14_17_30]
  all_goals decide +kernel

theorem column_30 : columnUpper 30 = 2148364431074953386 := by
  unfold columnUpper
  have indices : List.range 30 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_12, pair_13, pair_14, pair_15, pair_16, pair_17]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_30
