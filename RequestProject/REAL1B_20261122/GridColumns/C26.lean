import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_11_12_14_26 : boxUpper ⟨11, 12, 14, 26⟩ = 19962482569852942 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_14_26 : boxUpper ⟨11, 13, 14, 26⟩ = 19932925918615645 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_14_26 : boxUpper ⟨12, 13, 14, 26⟩ = 18880019694299887 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_14 : pairUpper 26 14 = 58775428182768474 := by
  have members : atPair 26 14 = [
    ⟨11, 12, 14, 26⟩,
    ⟨11, 13, 14, 26⟩,
    ⟨12, 13, 14, 26⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_11_12_14_26, box_11_13_14_26, box_12_13_14_26]
  all_goals decide +kernel

private theorem box_10_11_15_26 : boxUpper ⟨10, 11, 15, 26⟩ = 11350745299256869 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_15_26 : boxUpper ⟨10, 12, 15, 26⟩ = 13600612974619800 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_15_26 : boxUpper ⟨11, 12, 15, 26⟩ = 19214314093372013 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_15_26 : boxUpper ⟨10, 13, 15, 26⟩ = 19488514359189458 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_15_26 : boxUpper ⟨11, 13, 15, 26⟩ = 19201598016205029 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_15_26 : boxUpper ⟨12, 13, 15, 26⟩ = 18203811538101958 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_15_26 : boxUpper ⟨10, 14, 15, 26⟩ = 19584991014413852 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_15_26 : boxUpper ⟨11, 14, 15, 26⟩ = 18424868680339244 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_15_26 : boxUpper ⟨12, 14, 15, 26⟩ = 17484281342990754 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_15_26 : boxUpper ⟨13, 14, 15, 26⟩ = 16717116084393281 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 26 15 = 173270853402882258 := by
  have members : atPair 26 15 = [
    ⟨10, 11, 15, 26⟩,
    ⟨10, 12, 15, 26⟩,
    ⟨11, 12, 15, 26⟩,
    ⟨10, 13, 15, 26⟩,
    ⟨11, 13, 15, 26⟩,
    ⟨12, 13, 15, 26⟩,
    ⟨10, 14, 15, 26⟩,
    ⟨11, 14, 15, 26⟩,
    ⟨12, 14, 15, 26⟩,
    ⟨13, 14, 15, 26⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_10_11_15_26, box_10_12_15_26, box_11_12_15_26, box_10_13_15_26, box_11_13_15_26, box_12_13_15_26, box_10_14_15_26, box_11_14_15_26, box_12_14_15_26, box_13_14_15_26]
  all_goals decide +kernel

private theorem box_9_10_16_26 : boxUpper ⟨9, 10, 16, 26⟩ = 12563771591732815 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_16_26 : boxUpper ⟨9, 11, 16, 26⟩ = 11780262292466178 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_16_26 : boxUpper ⟨10, 11, 16, 26⟩ = 10962245010269032 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_16_26 : boxUpper ⟨9, 12, 16, 26⟩ = 11149730514507532 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_16_26 : boxUpper ⟨10, 12, 16, 26⟩ = 13147111509154065 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_16_26 : boxUpper ⟨11, 12, 16, 26⟩ = 18588154890322120 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_16_26 : boxUpper ⟨9, 13, 16, 26⟩ = 13456797768399829 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_16_26 : boxUpper ⟨10, 13, 16, 26⟩ = 18853416570443899 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_16_26 : boxUpper ⟨11, 13, 16, 26⟩ = 18592018644696484 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_16_26 : boxUpper ⟨12, 13, 16, 26⟩ = 17642896573759936 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_16_26 : boxUpper ⟨9, 14, 16, 26⟩ = 19407377724875425 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_16_26 : boxUpper ⟨10, 14, 16, 26⟩ = 18963235649949490 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_16_26 : boxUpper ⟨11, 14, 16, 26⟩ = 17857139536778778 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_16_26 : boxUpper ⟨12, 14, 16, 26⟩ = 16962932324499587 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_16_26 : boxUpper ⟨13, 14, 16, 26⟩ = 16236414925799892 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_16_26 : boxUpper ⟨9, 15, 16, 26⟩ = 19616087908017491 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_16_26 : boxUpper ⟨10, 15, 16, 26⟩ = 18301657566522742 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_16_26 : boxUpper ⟨11, 15, 16, 26⟩ = 17251846642619472 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_16_26 : boxUpper ⟨12, 15, 16, 26⟩ = 16405909905077239 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 26 16 = 307739007549892006 := by
  have members : atPair 26 16 = [
    ⟨9, 10, 16, 26⟩,
    ⟨9, 11, 16, 26⟩,
    ⟨10, 11, 16, 26⟩,
    ⟨9, 12, 16, 26⟩,
    ⟨10, 12, 16, 26⟩,
    ⟨11, 12, 16, 26⟩,
    ⟨9, 13, 16, 26⟩,
    ⟨10, 13, 16, 26⟩,
    ⟨11, 13, 16, 26⟩,
    ⟨12, 13, 16, 26⟩,
    ⟨9, 14, 16, 26⟩,
    ⟨10, 14, 16, 26⟩,
    ⟨11, 14, 16, 26⟩,
    ⟨12, 14, 16, 26⟩,
    ⟨13, 14, 16, 26⟩,
    ⟨9, 15, 16, 26⟩,
    ⟨10, 15, 16, 26⟩,
    ⟨11, 15, 16, 26⟩,
    ⟨12, 15, 16, 26⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_9_10_16_26, box_9_11_16_26, box_10_11_16_26, box_9_12_16_26, box_10_12_16_26, box_11_12_16_26, box_9_13_16_26, box_10_13_16_26, box_11_13_16_26, box_12_13_16_26, box_9_14_16_26, box_10_14_16_26, box_11_14_16_26, box_12_14_16_26, box_13_14_16_26, box_9_15_16_26, box_10_15_16_26, box_11_15_16_26, box_12_15_16_26]
  all_goals decide +kernel

private theorem box_8_9_17_26 : boxUpper ⟨8, 9, 17, 26⟩ = 14272252218258391 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_17_26 : boxUpper ⟨8, 10, 17, 26⟩ = 13249273093907780 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_17_26 : boxUpper ⟨9, 10, 17, 26⟩ = 12169602394816666 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_17_26 : boxUpper ⟨8, 11, 17, 26⟩ = 12423007276254055 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_17_26 : boxUpper ⟨9, 11, 17, 26⟩ = 11419374551629996 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_17_26 : boxUpper ⟨10, 11, 17, 26⟩ = 10634999009398849 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_17_26 : boxUpper ⟨8, 12, 17, 26⟩ = 11747257901418034 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_17_26 : boxUpper ⟨9, 12, 17, 26⟩ = 10816885361455207 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_17_26 : boxUpper ⟨10, 12, 17, 26⟩ = 12766993130642826 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_17_26 : boxUpper ⟨11, 12, 17, 26⟩ = 18065703157879442 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_17_26 : boxUpper ⟨8, 13, 17, 26⟩ = 11200042631178920 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_17_26 : boxUpper ⟨9, 13, 17, 26⟩ = 13067721223692370 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_17_26 : boxUpper ⟨10, 13, 17, 26⟩ = 18323506210384054 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_17_26 : boxUpper ⟨11, 13, 17, 26⟩ = 18086176663445462 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_17_26 : boxUpper ⟨12, 13, 17, 26⟩ = 17180497786128055 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_17_26 : boxUpper ⟨8, 14, 17, 26⟩ = 13601800262781412 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_17_26 : boxUpper ⟨9, 14, 17, 26⟩ = 18861890813796951 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_17_26 : boxUpper ⟨10, 14, 17, 26⟩ = 18447288934503572 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_17_26 : boxUpper ⟨11, 14, 17, 26⟩ = 17389122863674785 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_17_26 : boxUpper ⟨12, 14, 17, 26⟩ = 16536453312562722 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_17_26 : boxUpper ⟨8, 15, 17, 26⟩ = 19731692365255035 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_17_26 : boxUpper ⟨9, 15, 17, 26⟩ = 19082369729178933 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_17_26 : boxUpper ⟨10, 15, 17, 26⟩ = 17821984511184655 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_17_26 : boxUpper ⟨11, 15, 17, 26⟩ = 16818099820584993 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_17_26 : boxUpper ⟨8, 16, 17, 26⟩ = 20048869060648702 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_17_26 : boxUpper ⟨9, 16, 17, 26⟩ = 18513346671466163 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_17_26 : boxUpper ⟨10, 16, 17, 26⟩ = 17309497576584702 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 26 17 = 419585708532712732 := by
  have members : atPair 26 17 = [
    ⟨8, 9, 17, 26⟩,
    ⟨8, 10, 17, 26⟩,
    ⟨9, 10, 17, 26⟩,
    ⟨8, 11, 17, 26⟩,
    ⟨9, 11, 17, 26⟩,
    ⟨10, 11, 17, 26⟩,
    ⟨8, 12, 17, 26⟩,
    ⟨9, 12, 17, 26⟩,
    ⟨10, 12, 17, 26⟩,
    ⟨11, 12, 17, 26⟩,
    ⟨8, 13, 17, 26⟩,
    ⟨9, 13, 17, 26⟩,
    ⟨10, 13, 17, 26⟩,
    ⟨11, 13, 17, 26⟩,
    ⟨12, 13, 17, 26⟩,
    ⟨8, 14, 17, 26⟩,
    ⟨9, 14, 17, 26⟩,
    ⟨10, 14, 17, 26⟩,
    ⟨11, 14, 17, 26⟩,
    ⟨12, 14, 17, 26⟩,
    ⟨8, 15, 17, 26⟩,
    ⟨9, 15, 17, 26⟩,
    ⟨10, 15, 17, 26⟩,
    ⟨11, 15, 17, 26⟩,
    ⟨8, 16, 17, 26⟩,
    ⟨9, 16, 17, 26⟩,
    ⟨10, 16, 17, 26⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_8_9_17_26, box_8_10_17_26, box_9_10_17_26, box_8_11_17_26, box_9_11_17_26, box_10_11_17_26, box_8_12_17_26, box_9_12_17_26, box_10_12_17_26, box_11_12_17_26, box_8_13_17_26, box_9_13_17_26, box_10_13_17_26, box_11_13_17_26, box_12_13_17_26, box_8_14_17_26, box_9_14_17_26, box_10_14_17_26, box_11_14_17_26, box_12_14_17_26, box_8_15_17_26, box_9_15_17_26, box_10_15_17_26, box_11_15_17_26, box_8_16_17_26, box_9_16_17_26, box_10_16_17_26]
  all_goals decide +kernel

private theorem box_7_8_18_26 : boxUpper ⟨7, 8, 18, 26⟩ = 16699692108873522 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_18_26 : boxUpper ⟨7, 9, 18, 26⟩ = 15317265514927110 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_18_26 : boxUpper ⟨8, 9, 18, 26⟩ = 13860144814253832 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_18_26 : boxUpper ⟨7, 10, 18, 26⟩ = 14219373384998730 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_18_26 : boxUpper ⟨8, 10, 18, 26⟩ = 12875994000794853 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_18_26 : boxUpper ⟨9, 10, 18, 26⟩ = 11835761267139612 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_18_26 : boxUpper ⟨7, 11, 18, 26⟩ = 13332598666730315 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_18_26 : boxUpper ⟨8, 11, 18, 26⟩ = 12082211392256268 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_18_26 : boxUpper ⟨9, 11, 18, 26⟩ = 11115069737709105 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_18_26 : boxUpper ⟨10, 11, 18, 26⟩ = 10360452309302249 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_18_26 : boxUpper ⟨7, 12, 18, 26⟩ = 12607361650430780 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_18_26 : boxUpper ⟨8, 12, 18, 26⟩ = 11434211300426332 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_18_26 : boxUpper ⟨9, 12, 18, 26⟩ = 10537640800541910 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_18_26 : boxUpper ⟨10, 12, 18, 26⟩ = 12450190004227825 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_18_26 : boxUpper ⟨11, 12, 18, 26⟩ = 17632962380255935 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_18_26 : boxUpper ⟨7, 13, 18, 26⟩ = 12009040045965610 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_18_26 : boxUpper ⟨8, 13, 18, 26⟩ = 10910901410695209 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_18_26 : boxUpper ⟨9, 13, 18, 26⟩ = 12743451304113802 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_18_26 : boxUpper ⟨10, 13, 18, 26⟩ = 17884586978257752 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_18_26 : boxUpper ⟨11, 13, 18, 26⟩ = 17670344340311671 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_18_26 : boxUpper ⟨12, 13, 18, 26⟩ = 16803881998765495 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_18_26 : boxUpper ⟨7, 14, 18, 26⟩ = 11523333868233983 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_18_26 : boxUpper ⟨8, 14, 18, 26⟩ = 13264269156476279 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_18_26 : boxUpper ⟨9, 14, 18, 26⟩ = 18410068485454899 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_18_26 : boxUpper ⟨10, 14, 18, 26⟩ = 18023148961752345 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_18_26 : boxUpper ⟨11, 14, 18, 26⟩ = 17007930813828053 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_18_26 : boxUpper ⟨7, 15, 18, 26⟩ = 14069524432267432 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_18_26 : boxUpper ⟨8, 15, 18, 26⟩ = 19259023289967863 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_18_26 : boxUpper ⟨9, 15, 18, 26⟩ = 18643618782775953 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_18_26 : boxUpper ⟨10, 15, 18, 26⟩ = 17431297266190249 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_18_26 : boxUpper ⟨7, 16, 18, 26⟩ = 20521137852948297 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_18_26 : boxUpper ⟨8, 16, 18, 26⟩ = 19587881193688813 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_18_26 : boxUpper ⟨9, 16, 18, 26⟩ = 18107493164078184 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_17_18_26 : boxUpper ⟨7, 17, 18, 26⟩ = 20952724069371529 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_17_18_26 : boxUpper ⟨8, 17, 18, 26⟩ = 19095365158177794 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 26 18 = 530279951906189590 := by
  have members : atPair 26 18 = [
    ⟨7, 8, 18, 26⟩,
    ⟨7, 9, 18, 26⟩,
    ⟨8, 9, 18, 26⟩,
    ⟨7, 10, 18, 26⟩,
    ⟨8, 10, 18, 26⟩,
    ⟨9, 10, 18, 26⟩,
    ⟨7, 11, 18, 26⟩,
    ⟨8, 11, 18, 26⟩,
    ⟨9, 11, 18, 26⟩,
    ⟨10, 11, 18, 26⟩,
    ⟨7, 12, 18, 26⟩,
    ⟨8, 12, 18, 26⟩,
    ⟨9, 12, 18, 26⟩,
    ⟨10, 12, 18, 26⟩,
    ⟨11, 12, 18, 26⟩,
    ⟨7, 13, 18, 26⟩,
    ⟨8, 13, 18, 26⟩,
    ⟨9, 13, 18, 26⟩,
    ⟨10, 13, 18, 26⟩,
    ⟨11, 13, 18, 26⟩,
    ⟨12, 13, 18, 26⟩,
    ⟨7, 14, 18, 26⟩,
    ⟨8, 14, 18, 26⟩,
    ⟨9, 14, 18, 26⟩,
    ⟨10, 14, 18, 26⟩,
    ⟨11, 14, 18, 26⟩,
    ⟨7, 15, 18, 26⟩,
    ⟨8, 15, 18, 26⟩,
    ⟨9, 15, 18, 26⟩,
    ⟨10, 15, 18, 26⟩,
    ⟨7, 16, 18, 26⟩,
    ⟨8, 16, 18, 26⟩,
    ⟨9, 16, 18, 26⟩,
    ⟨7, 17, 18, 26⟩,
    ⟨8, 17, 18, 26⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_7_8_18_26, box_7_9_18_26, box_8_9_18_26, box_7_10_18_26, box_8_10_18_26, box_9_10_18_26, box_7_11_18_26, box_8_11_18_26, box_9_11_18_26, box_10_11_18_26, box_7_12_18_26, box_8_12_18_26, box_9_12_18_26, box_10_12_18_26, box_11_12_18_26, box_7_13_18_26, box_8_13_18_26, box_9_13_18_26, box_10_13_18_26, box_11_13_18_26, box_12_13_18_26, box_7_14_18_26, box_8_14_18_26, box_9_14_18_26, box_10_14_18_26, box_11_14_18_26, box_7_15_18_26, box_8_15_18_26, box_9_15_18_26, box_10_15_18_26, box_7_16_18_26, box_8_16_18_26, box_9_16_18_26, box_7_17_18_26, box_8_17_18_26]
  all_goals decide +kernel

private theorem box_4_5_21_26 : boxUpper ⟨4, 5, 21, 26⟩ = 34840969699016396 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_21_26 : boxUpper ⟨4, 6, 21, 26⟩ = 30119396305872059 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_21_26 : boxUpper ⟨5, 6, 21, 26⟩ = 25157356091873831 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_21_26 : boxUpper ⟨4, 7, 21, 26⟩ = 26704889329210180 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_21_26 : boxUpper ⟨5, 7, 21, 26⟩ = 22319214423080382 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_21_26 : boxUpper ⟨6, 7, 21, 26⟩ = 19330534797510419 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_21_26 : boxUpper ⟨4, 8, 21, 26⟩ = 24132099597727321 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_21_26 : boxUpper ⟨5, 8, 21, 26⟩ = 20182103836049129 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_21_26 : boxUpper ⟨6, 8, 21, 26⟩ = 17491592315128441 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_21_26 : boxUpper ⟨7, 8, 21, 26⟩ = 15550278998494505 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_21_26 : boxUpper ⟨4, 9, 21, 26⟩ = 22134305175169402 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_21_26 : boxUpper ⟨5, 9, 21, 26⟩ = 18524025689764044 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_21_26 : boxUpper ⟨6, 9, 21, 26⟩ = 16066171162999708 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_21_26 : boxUpper ⟨7, 9, 21, 26⟩ = 14293966072481656 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_21_26 : boxUpper ⟨8, 9, 21, 26⟩ = 12963856567792472 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_21_26 : boxUpper ⟨4, 10, 21, 26⟩ = 20547690356213558 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_21_26 : boxUpper ⟨5, 10, 21, 26⟩ = 17208651460846578 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_21_26 : boxUpper ⟨6, 10, 21, 26⟩ = 14936728832105146 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_21_26 : boxUpper ⟨7, 10, 21, 26⟩ = 13299840136505986 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_21_26 : boxUpper ⟨8, 10, 21, 26⟩ = 12072553426868927 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_21_26 : boxUpper ⟨9, 10, 21, 26⟩ = 11125749683858409 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_11_21_26 : boxUpper ⟨4, 11, 21, 26⟩ = 19266159258441689 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_21_26 : boxUpper ⟨5, 11, 21, 26⟩ = 16147707805063839 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_21_26 : boxUpper ⟨6, 11, 21, 26⟩ = 14027176221460162 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_21_26 : boxUpper ⟨7, 11, 21, 26⟩ = 12500647331711596 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_21_26 : boxUpper ⟨8, 11, 21, 26⟩ = 11357405265752715 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_21_26 : boxUpper ⟨9, 11, 21, 26⟩ = 10476782711392067 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_21_26 : boxUpper ⟨10, 11, 21, 26⟩ = 9793856844977888 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_12_21_26 : boxUpper ⟨4, 12, 21, 26⟩ = 18218063465850141 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_21_26 : boxUpper ⟨5, 12, 21, 26⟩ = 15281604322052238 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_21_26 : boxUpper ⟨6, 12, 21, 26⟩ = 13286170199381031 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_21_26 : boxUpper ⟨7, 12, 21, 26⟩ = 11851029049206965 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_21_26 : boxUpper ⟨8, 12, 21, 26⟩ = 10777583690412106 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_21_26 : boxUpper ⟨9, 12, 21, 26⟩ = 9961347515716282 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_21_26 : boxUpper ⟨10, 12, 21, 26⟩ = 11810546817664381 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_13_21_26 : boxUpper ⟨4, 13, 21, 26⟩ = 17353369577623696 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_21_26 : boxUpper ⟨5, 13, 21, 26⟩ = 14568752319645854 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_21_26 : boxUpper ⟨6, 13, 21, 26⟩ = 12677902365140706 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_21_26 : boxUpper ⟨7, 13, 21, 26⟩ = 11319375962999354 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_21_26 : boxUpper ⟨8, 13, 21, 26⟩ = 10314178108932653 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_21_26 : boxUpper ⟨9, 13, 21, 26⟩ = 12088727053696934 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_14_21_26 : boxUpper ⟨4, 14, 21, 26⟩ = 16636183767030313 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_21_26 : boxUpper ⟨5, 14, 21, 26⟩ = 13979343334503926 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_21_26 : boxUpper ⟨6, 14, 21, 26⟩ = 12176734632914622 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_21_26 : boxUpper ⟨7, 14, 21, 26⟩ = 10893087258563760 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_21_26 : boxUpper ⟨8, 14, 21, 26⟩ = 12582760014414575 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_15_21_26 : boxUpper ⟨4, 15, 21, 26⟩ = 16040196288028297 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_15_21_26 : boxUpper ⟨5, 15, 21, 26⟩ = 13491558726046550 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_21_26 : boxUpper ⟨6, 15, 21, 26⟩ = 11774667489854365 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_21_26 : boxUpper ⟨7, 15, 21, 26⟩ = 13346598033704943 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_16_21_26 : boxUpper ⟨4, 16, 21, 26⟩ = 15545799674679127 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_16_21_26 : boxUpper ⟨5, 16, 21, 26⟩ = 13100991344167313 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_21_26 : boxUpper ⟨6, 16, 21, 26⟩ = 14477054232559726 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_17_21_26 : boxUpper ⟨4, 17, 21, 26⟩ = 15151654153064394 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_17_21_26 : boxUpper ⟨5, 17, 21, 26⟩ = 16150223049774015 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_18_21_26 : boxUpper ⟨4, 18, 21, 26⟩ = 18708881808509017 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_21 : pairUpper 26 21 = 886136093653505789 := by
  have members : atPair 26 21 = [
    ⟨4, 5, 21, 26⟩,
    ⟨4, 6, 21, 26⟩,
    ⟨5, 6, 21, 26⟩,
    ⟨4, 7, 21, 26⟩,
    ⟨5, 7, 21, 26⟩,
    ⟨6, 7, 21, 26⟩,
    ⟨4, 8, 21, 26⟩,
    ⟨5, 8, 21, 26⟩,
    ⟨6, 8, 21, 26⟩,
    ⟨7, 8, 21, 26⟩,
    ⟨4, 9, 21, 26⟩,
    ⟨5, 9, 21, 26⟩,
    ⟨6, 9, 21, 26⟩,
    ⟨7, 9, 21, 26⟩,
    ⟨8, 9, 21, 26⟩,
    ⟨4, 10, 21, 26⟩,
    ⟨5, 10, 21, 26⟩,
    ⟨6, 10, 21, 26⟩,
    ⟨7, 10, 21, 26⟩,
    ⟨8, 10, 21, 26⟩,
    ⟨9, 10, 21, 26⟩,
    ⟨4, 11, 21, 26⟩,
    ⟨5, 11, 21, 26⟩,
    ⟨6, 11, 21, 26⟩,
    ⟨7, 11, 21, 26⟩,
    ⟨8, 11, 21, 26⟩,
    ⟨9, 11, 21, 26⟩,
    ⟨10, 11, 21, 26⟩,
    ⟨4, 12, 21, 26⟩,
    ⟨5, 12, 21, 26⟩,
    ⟨6, 12, 21, 26⟩,
    ⟨7, 12, 21, 26⟩,
    ⟨8, 12, 21, 26⟩,
    ⟨9, 12, 21, 26⟩,
    ⟨10, 12, 21, 26⟩,
    ⟨4, 13, 21, 26⟩,
    ⟨5, 13, 21, 26⟩,
    ⟨6, 13, 21, 26⟩,
    ⟨7, 13, 21, 26⟩,
    ⟨8, 13, 21, 26⟩,
    ⟨9, 13, 21, 26⟩,
    ⟨4, 14, 21, 26⟩,
    ⟨5, 14, 21, 26⟩,
    ⟨6, 14, 21, 26⟩,
    ⟨7, 14, 21, 26⟩,
    ⟨8, 14, 21, 26⟩,
    ⟨4, 15, 21, 26⟩,
    ⟨5, 15, 21, 26⟩,
    ⟨6, 15, 21, 26⟩,
    ⟨7, 15, 21, 26⟩,
    ⟨4, 16, 21, 26⟩,
    ⟨5, 16, 21, 26⟩,
    ⟨6, 16, 21, 26⟩,
    ⟨4, 17, 21, 26⟩,
    ⟨5, 17, 21, 26⟩,
    ⟨4, 18, 21, 26⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_21_26, box_4_6_21_26, box_5_6_21_26, box_4_7_21_26, box_5_7_21_26, box_6_7_21_26, box_4_8_21_26, box_5_8_21_26, box_6_8_21_26, box_7_8_21_26, box_4_9_21_26, box_5_9_21_26, box_6_9_21_26, box_7_9_21_26, box_8_9_21_26, box_4_10_21_26, box_5_10_21_26, box_6_10_21_26, box_7_10_21_26, box_8_10_21_26, box_9_10_21_26, box_4_11_21_26, box_5_11_21_26, box_6_11_21_26, box_7_11_21_26, box_8_11_21_26, box_9_11_21_26, box_10_11_21_26, box_4_12_21_26, box_5_12_21_26, box_6_12_21_26, box_7_12_21_26, box_8_12_21_26, box_9_12_21_26, box_10_12_21_26, box_4_13_21_26, box_5_13_21_26, box_6_13_21_26, box_7_13_21_26, box_8_13_21_26, box_9_13_21_26, box_4_14_21_26, box_5_14_21_26, box_6_14_21_26, box_7_14_21_26, box_8_14_21_26, box_4_15_21_26, box_5_15_21_26, box_6_15_21_26, box_7_15_21_26, box_4_16_21_26, box_5_16_21_26, box_6_16_21_26, box_4_17_21_26, box_5_17_21_26, box_4_18_21_26]
  all_goals decide +kernel

theorem column_26 : columnUpper 26 = 2375787043227950849 := by
  unfold columnUpper
  have indices : List.range 26 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_14, pair_15, pair_16, pair_17, pair_18, pair_21]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_26
