import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_13_14_16_22 : boxUpper ⟨13, 14, 16, 22⟩ = 16060017342089311 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_16_22 : boxUpper ⟨13, 15, 16, 22⟩ = 16227103578744724 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_16_22 : boxUpper ⟨14, 15, 16, 22⟩ = 15585721734369870 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 22 16 = 47872842655203905 := by
  have members : atPair 22 16 = [
    ⟨13, 14, 16, 22⟩,
    ⟨13, 15, 16, 22⟩,
    ⟨14, 15, 16, 22⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_13_14_16_22, box_13_15_16_22, box_14_15_16_22]
  all_goals decide +kernel

private theorem box_12_13_17_22 : boxUpper ⟨12, 13, 17, 22⟩ = 8948156016247485 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_17_22 : boxUpper ⟨12, 14, 17, 22⟩ = 10881680205696525 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_17_22 : boxUpper ⟨13, 14, 17, 22⟩ = 15608641757454992 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_17_22 : boxUpper ⟨12, 15, 17, 22⟩ = 15771259086137512 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_17_22 : boxUpper ⟨13, 15, 17, 22⟩ = 15785625468338500 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_17_22 : boxUpper ⟨14, 15, 17, 22⟩ = 15177257516646847 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_17_22 : boxUpper ⟨12, 16, 17, 22⟩ = 16017747483021490 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_17_22 : boxUpper ⟨13, 16, 17, 22⟩ = 15314942094456819 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_16_17_22 : boxUpper ⟨14, 16, 17, 22⟩ = 14747794318777507 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_15_16_17_22 : boxUpper ⟨15, 16, 17, 22⟩ = 16208900955020445 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 22 17 = 144462004901798122 := by
  have members : atPair 22 17 = [
    ⟨12, 13, 17, 22⟩,
    ⟨12, 14, 17, 22⟩,
    ⟨13, 14, 17, 22⟩,
    ⟨12, 15, 17, 22⟩,
    ⟨13, 15, 17, 22⟩,
    ⟨14, 15, 17, 22⟩,
    ⟨12, 16, 17, 22⟩,
    ⟨13, 16, 17, 22⟩,
    ⟨14, 16, 17, 22⟩,
    ⟨15, 16, 17, 22⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_12_13_17_22, box_12_14_17_22, box_13_14_17_22, box_12_15_17_22, box_13_15_17_22, box_14_15_17_22, box_12_16_17_22, box_13_16_17_22, box_14_16_17_22, box_15_16_17_22]
  all_goals decide +kernel

private theorem box_11_12_18_22 : boxUpper ⟨11, 12, 18, 22⟩ = 9652813645721018 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_18_22 : boxUpper ⟨11, 13, 18, 22⟩ = 9194734568584166 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_18_22 : boxUpper ⟨12, 13, 18, 22⟩ = 8717169555352750 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_18_22 : boxUpper ⟨11, 14, 18, 22⟩ = 8823020702379968 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_18_22 : boxUpper ⟨12, 14, 18, 22⟩ = 10611677256836824 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_18_22 : boxUpper ⟨13, 14, 18, 22⟩ = 15234775994914386 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_18_22 : boxUpper ⟨11, 15, 18, 22⟩ = 10791230714707814 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_18_22 : boxUpper ⟨12, 15, 18, 22⟩ = 15393496559930562 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_18_22 : boxUpper ⟨13, 15, 18, 22⟩ = 15422708120407209 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_18_22 : boxUpper ⟨14, 15, 18, 22⟩ = 14851565859246887 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_18_22 : boxUpper ⟨11, 16, 18, 22⟩ = 15721088423280040 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_18_22 : boxUpper ⟨12, 16, 18, 22⟩ = 15649490782596636 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_18_22 : boxUpper ⟨13, 16, 18, 22⟩ = 14986290442478219 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_16_18_22 : boxUpper ⟨14, 16, 18, 22⟩ = 16391305737115661 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_15_16_18_22 : boxUpper ⟨15, 16, 18, 22⟩ = 20356895324798967 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_17_18_22 : boxUpper ⟨11, 17, 18, 22⟩ = 16042681342338899 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_17_18_22 : boxUpper ⟨12, 17, 18, 22⟩ = 15263219592480272 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_17_18_22 : boxUpper ⟨13, 17, 18, 22⟩ = 16600862653167367 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_17_18_22 : boxUpper ⟨14, 17, 18, 22⟩ = 20518685820367788 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_15_17_18_22 : boxUpper ⟨15, 17, 18, 22⟩ = 20541568059020904 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_16_17_18_22 : boxUpper ⟨16, 17, 18, 22⟩ = 20055591737394951 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 22 18 = 310820872893121288 := by
  have members : atPair 22 18 = [
    ⟨11, 12, 18, 22⟩,
    ⟨11, 13, 18, 22⟩,
    ⟨12, 13, 18, 22⟩,
    ⟨11, 14, 18, 22⟩,
    ⟨12, 14, 18, 22⟩,
    ⟨13, 14, 18, 22⟩,
    ⟨11, 15, 18, 22⟩,
    ⟨12, 15, 18, 22⟩,
    ⟨13, 15, 18, 22⟩,
    ⟨14, 15, 18, 22⟩,
    ⟨11, 16, 18, 22⟩,
    ⟨12, 16, 18, 22⟩,
    ⟨13, 16, 18, 22⟩,
    ⟨14, 16, 18, 22⟩,
    ⟨15, 16, 18, 22⟩,
    ⟨11, 17, 18, 22⟩,
    ⟨12, 17, 18, 22⟩,
    ⟨13, 17, 18, 22⟩,
    ⟨14, 17, 18, 22⟩,
    ⟨15, 17, 18, 22⟩,
    ⟨16, 17, 18, 22⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_11_12_18_22, box_11_13_18_22, box_12_13_18_22, box_11_14_18_22, box_12_14_18_22, box_13_14_18_22, box_11_15_18_22, box_12_15_18_22, box_13_15_18_22, box_14_15_18_22, box_11_16_18_22, box_12_16_18_22, box_13_16_18_22, box_14_16_18_22, box_15_16_18_22, box_11_17_18_22, box_12_17_18_22, box_13_17_18_22, box_14_17_18_22, box_15_17_18_22, box_16_17_18_22]
  all_goals decide +kernel

private theorem box_8_9_21_22 : boxUpper ⟨8, 9, 21, 22⟩ = 13678306652637112 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_21_22 : boxUpper ⟨8, 10, 21, 22⟩ = 12697902117206950 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_21_22 : boxUpper ⟨9, 10, 21, 22⟩ = 11663164925289427 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_21_22 : boxUpper ⟨8, 11, 21, 22⟩ = 11906024372694083 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_21_22 : boxUpper ⟨9, 11, 21, 22⟩ = 10944160565718426 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_21_22 : boxUpper ⟨10, 11, 21, 22⟩ = 10183037028763207 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_21_22 : boxUpper ⟨8, 12, 21, 22⟩ = 11258399142916954 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_21_22 : boxUpper ⟨9, 12, 21, 22⟩ = 10357206532155527 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_21_22 : boxUpper ⟨10, 12, 21, 22⟩ = 9645140092745760 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_21_22 : boxUpper ⟨11, 12, 21, 22⟩ = 9073807734815363 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_21_22 : boxUpper ⟨8, 13, 21, 22⟩ = 10724109028426581 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_21_22 : boxUpper ⟨9, 13, 21, 22⟩ = 9874117368440478 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_21_22 : boxUpper ⟨10, 13, 21, 22⟩ = 9203603331503559 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_21_22 : boxUpper ⟨11, 13, 21, 22⟩ = 8666773047748529 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_21_22 : boxUpper ⟨12, 13, 21, 22⟩ = 8240486485284429 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_21_22 : boxUpper ⟨8, 14, 21, 22⟩ = 10280974123948614 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_21_22 : boxUpper ⟨9, 14, 21, 22⟩ = 9474691422274300 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_21_22 : boxUpper ⟨10, 14, 21, 22⟩ = 8839815595222943 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_21_22 : boxUpper ⟨11, 14, 21, 22⟩ = 8340545487800965 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_21_22 : boxUpper ⟨12, 14, 21, 22⟩ = 10073985055479679 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_21_22 : boxUpper ⟨13, 14, 21, 22⟩ = 16551976216543265 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_21_22 : boxUpper ⟨8, 15, 21, 22⟩ = 9912736996734969 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_21_22 : boxUpper ⟨9, 15, 21, 22⟩ = 9144141998238832 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_21_22 : boxUpper ⟨10, 15, 21, 22⟩ = 8548150480983390 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_21_22 : boxUpper ⟨11, 15, 21, 22⟩ = 10244425642409207 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_21_22 : boxUpper ⟨12, 15, 21, 22⟩ = 16723823547450017 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_21_22 : boxUpper ⟨13, 15, 21, 22⟩ = 21417230045705376 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_21_22 : boxUpper ⟨14, 15, 21, 22⟩ = 21339013277800316 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_21_22 : boxUpper ⟨8, 16, 21, 22⟩ = 9607281912742076 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_21_22 : boxUpper ⟨9, 16, 21, 22⟩ = 8879733739802227 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_21_22 : boxUpper ⟨10, 16, 21, 22⟩ = 10541708294208319 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_21_22 : boxUpper ⟨11, 16, 21, 22⟩ = 17078469746237920 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_21_22 : boxUpper ⟨12, 16, 21, 22⟩ = 21731739603700563 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_21_22 : boxUpper ⟨13, 16, 21, 22⟩ = 21532585050483068 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_16_21_22 : boxUpper ⟨14, 16, 21, 22⟩ = 20834159657502479 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_17_21_22 : boxUpper ⟨8, 17, 21, 22⟩ = 9364150095689095 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_17_21_22 : boxUpper ⟨9, 17, 21, 22⟩ = 10988184505094440 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_17_21_22 : boxUpper ⟨10, 17, 21, 22⟩ = 17639623568707862 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_17_21_22 : boxUpper ⟨11, 17, 21, 22⟩ = 22276999884122383 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_17_21_22 : boxUpper ⟨12, 17, 21, 22⟩ = 21930475624096931 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_17_21_22 : boxUpper ⟨13, 17, 21, 22⟩ = 21101358294013105 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_18_21_22 : boxUpper ⟨8, 18, 21, 22⟩ = 11621142844662193 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_18_21_22 : boxUpper ⟨9, 18, 21, 22⟩ = 18447944873905243 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_18_21_22 : boxUpper ⟨10, 18, 21, 22⟩ = 23088092646981416 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_18_21_22 : boxUpper ⟨11, 18, 21, 22⟩ = 22555715843863425 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_18_21_22 : boxUpper ⟨12, 18, 21, 22⟩ = 21562275525667420 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_21 : pairUpper 22 21 = 629789390028418423 := by
  have members : atPair 22 21 = [
    ⟨8, 9, 21, 22⟩,
    ⟨8, 10, 21, 22⟩,
    ⟨9, 10, 21, 22⟩,
    ⟨8, 11, 21, 22⟩,
    ⟨9, 11, 21, 22⟩,
    ⟨10, 11, 21, 22⟩,
    ⟨8, 12, 21, 22⟩,
    ⟨9, 12, 21, 22⟩,
    ⟨10, 12, 21, 22⟩,
    ⟨11, 12, 21, 22⟩,
    ⟨8, 13, 21, 22⟩,
    ⟨9, 13, 21, 22⟩,
    ⟨10, 13, 21, 22⟩,
    ⟨11, 13, 21, 22⟩,
    ⟨12, 13, 21, 22⟩,
    ⟨8, 14, 21, 22⟩,
    ⟨9, 14, 21, 22⟩,
    ⟨10, 14, 21, 22⟩,
    ⟨11, 14, 21, 22⟩,
    ⟨12, 14, 21, 22⟩,
    ⟨13, 14, 21, 22⟩,
    ⟨8, 15, 21, 22⟩,
    ⟨9, 15, 21, 22⟩,
    ⟨10, 15, 21, 22⟩,
    ⟨11, 15, 21, 22⟩,
    ⟨12, 15, 21, 22⟩,
    ⟨13, 15, 21, 22⟩,
    ⟨14, 15, 21, 22⟩,
    ⟨8, 16, 21, 22⟩,
    ⟨9, 16, 21, 22⟩,
    ⟨10, 16, 21, 22⟩,
    ⟨11, 16, 21, 22⟩,
    ⟨12, 16, 21, 22⟩,
    ⟨13, 16, 21, 22⟩,
    ⟨14, 16, 21, 22⟩,
    ⟨8, 17, 21, 22⟩,
    ⟨9, 17, 21, 22⟩,
    ⟨10, 17, 21, 22⟩,
    ⟨11, 17, 21, 22⟩,
    ⟨12, 17, 21, 22⟩,
    ⟨13, 17, 21, 22⟩,
    ⟨8, 18, 21, 22⟩,
    ⟨9, 18, 21, 22⟩,
    ⟨10, 18, 21, 22⟩,
    ⟨11, 18, 21, 22⟩,
    ⟨12, 18, 21, 22⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_21_22, box_8_10_21_22, box_9_10_21_22, box_8_11_21_22, box_9_11_21_22, box_10_11_21_22, box_8_12_21_22, box_9_12_21_22, box_10_12_21_22, box_11_12_21_22, box_8_13_21_22, box_9_13_21_22, box_10_13_21_22, box_11_13_21_22, box_12_13_21_22, box_8_14_21_22, box_9_14_21_22, box_10_14_21_22, box_11_14_21_22, box_12_14_21_22, box_13_14_21_22, box_8_15_21_22, box_9_15_21_22, box_10_15_21_22, box_11_15_21_22, box_12_15_21_22, box_13_15_21_22, box_14_15_21_22, box_8_16_21_22, box_9_16_21_22, box_10_16_21_22, box_11_16_21_22, box_12_16_21_22, box_13_16_21_22, box_14_16_21_22, box_8_17_21_22, box_9_17_21_22, box_10_17_21_22, box_11_17_21_22, box_12_17_21_22, box_13_17_21_22, box_8_18_21_22, box_9_18_21_22, box_10_18_21_22, box_11_18_21_22, box_12_18_21_22]
  all_goals decide +kernel

theorem column_22 : columnUpper 22 = 1132945110478541738 := by
  unfold columnUpper
  have indices : List.range 22 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_16, pair_17, pair_18, pair_21]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_22
