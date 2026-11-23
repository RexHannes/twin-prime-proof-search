import RequestProject.REAL1B_20261122.FMGridData

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem box_12_13_15_24 : boxUpper ⟨12, 13, 15, 24⟩ = 17693168032599137 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_15_24 : boxUpper ⟨12, 14, 15, 24⟩ = 17777693299593756 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_15_24 : boxUpper ⟨13, 14, 15, 24⟩ = 16963878921769210 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_15 : pairUpper 24 15 = 52434740253962103 := by
  have members : atPair 24 15 = [
    ⟨12, 13, 15, 24⟩,
    ⟨12, 14, 15, 24⟩,
    ⟨13, 14, 15, 24⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_12_13_15_24, box_12_14_15_24, box_13_14_15_24]
  all_goals decide +kernel

private theorem box_11_12_16_24 : boxUpper ⟨11, 12, 16, 24⟩ = 9950683765839826 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_16_24 : boxUpper ⟨11, 13, 16, 24⟩ = 12017613062314176 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_16_24 : boxUpper ⟨12, 13, 16, 24⟩ = 17116591089204296 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_16_24 : boxUpper ⟨11, 14, 16, 24⟩ = 17323992332122704 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_16_24 : boxUpper ⟨12, 14, 16, 24⟩ = 17213329605867672 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_16_24 : boxUpper ⟨13, 14, 16, 24⟩ = 16441180850358795 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_16_24 : boxUpper ⟨11, 15, 16, 24⟩ = 17506516223863255 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_16_24 : boxUpper ⟨12, 15, 16, 24⟩ = 16612817895085647 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_16_24 : boxUpper ⟨13, 15, 16, 24⟩ = 15883897574978292 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_16_24 : boxUpper ⟨14, 15, 16, 24⟩ = 15288471536045794 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_16 : pairUpper 24 16 = 155355093935680457 := by
  have members : atPair 24 16 = [
    ⟨11, 12, 16, 24⟩,
    ⟨11, 13, 16, 24⟩,
    ⟨12, 13, 16, 24⟩,
    ⟨11, 14, 16, 24⟩,
    ⟨12, 14, 16, 24⟩,
    ⟨13, 14, 16, 24⟩,
    ⟨11, 15, 16, 24⟩,
    ⟨12, 15, 16, 24⟩,
    ⟨13, 15, 16, 24⟩,
    ⟨14, 15, 16, 24⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_11_12_16_24, box_11_13_16_24, box_12_13_16_24, box_11_14_16_24, box_12_14_16_24, box_13_14_16_24, box_11_15_16_24, box_12_15_16_24, box_13_15_16_24, box_14_15_16_24]
  all_goals decide +kernel

private theorem box_10_11_17_24 : boxUpper ⟨10, 11, 17, 24⟩ = 10860800439586247 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_17_24 : boxUpper ⟨10, 12, 17, 24⟩ = 10270040266595708 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_17_24 : boxUpper ⟨11, 12, 17, 24⟩ = 9653643129507045 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_17_24 : boxUpper ⟨10, 13, 17, 24⟩ = 9791727038852784 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_17_24 : boxUpper ⟨11, 13, 17, 24⟩ = 11670161885332598 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_17_24 : boxUpper ⟨12, 13, 17, 24⟩ = 16635511418497428 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_17_24 : boxUpper ⟨10, 14, 17, 24⟩ = 11901513577204973 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_17_24 : boxUpper ⟨11, 14, 17, 24⟩ = 16837081276096057 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_17_24 : boxUpper ⟨12, 14, 17, 24⟩ = 16745010695723673 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_17_24 : boxUpper ⟨13, 14, 17, 24⟩ = 16010288764264746 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_17_24 : boxUpper ⟨10, 15, 17, 24⟩ = 17255270594104400 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_17_24 : boxUpper ⟨11, 15, 17, 24⟩ = 17030217120179501 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_17_24 : boxUpper ⟨12, 15, 17, 24⟩ = 16177425421082475 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_17_24 : boxUpper ⟨13, 15, 17, 24⟩ = 15484558073486390 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_17_24 : boxUpper ⟨14, 15, 17, 24⟩ = 14921571830008210 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_17_24 : boxUpper ⟨10, 16, 17, 24⟩ = 17527826601785841 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_17_24 : boxUpper ⟨11, 16, 17, 24⟩ = 16522410027558204 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_17_24 : boxUpper ⟨12, 16, 17, 24⟩ = 15712247222503959 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_17_24 : boxUpper ⟨13, 16, 17, 24⟩ = 15056933368099347 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_16_17_24 : boxUpper ⟨14, 16, 17, 24⟩ = 14534600785314437 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_17 : pairUpper 24 17 = 290598839535784023 := by
  have members : atPair 24 17 = [
    ⟨10, 11, 17, 24⟩,
    ⟨10, 12, 17, 24⟩,
    ⟨11, 12, 17, 24⟩,
    ⟨10, 13, 17, 24⟩,
    ⟨11, 13, 17, 24⟩,
    ⟨12, 13, 17, 24⟩,
    ⟨10, 14, 17, 24⟩,
    ⟨11, 14, 17, 24⟩,
    ⟨12, 14, 17, 24⟩,
    ⟨13, 14, 17, 24⟩,
    ⟨10, 15, 17, 24⟩,
    ⟨11, 15, 17, 24⟩,
    ⟨12, 15, 17, 24⟩,
    ⟨13, 15, 17, 24⟩,
    ⟨14, 15, 17, 24⟩,
    ⟨10, 16, 17, 24⟩,
    ⟨11, 16, 17, 24⟩,
    ⟨12, 16, 17, 24⟩,
    ⟨13, 16, 17, 24⟩,
    ⟨14, 16, 17, 24⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_10_11_17_24, box_10_12_17_24, box_11_12_17_24, box_10_13_17_24, box_11_13_17_24, box_12_13_17_24, box_10_14_17_24, box_11_14_17_24, box_12_14_17_24, box_13_14_17_24, box_10_15_17_24, box_11_15_17_24, box_12_15_17_24, box_13_15_17_24, box_14_15_17_24, box_10_16_17_24, box_11_16_17_24, box_12_16_17_24, box_13_16_17_24, box_14_16_17_24]
  all_goals decide +kernel

private theorem box_9_10_18_24 : boxUpper ⟨9, 10, 18, 24⟩ = 12117201855970393 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_18_24 : boxUpper ⟨9, 11, 18, 24⟩ = 11361544222965734 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_18_24 : boxUpper ⟨10, 11, 18, 24⟩ = 10562873352862753 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_18_24 : boxUpper ⟨9, 12, 18, 24⟩ = 10743541821522702 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_18_24 : boxUpper ⟨10, 12, 18, 24⟩ = 9996372637064134 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_18_24 : boxUpper ⟨11, 12, 18, 24⟩ = 9404438926524571 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_18_24 : boxUpper ⟨9, 13, 18, 24⟩ = 10233691318013856 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_18_24 : boxUpper ⟨10, 13, 18, 24⟩ = 9538956605907482 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_18_24 : boxUpper ⟨11, 13, 18, 24⟩ = 11380586515020954 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_18_24 : boxUpper ⟨12, 13, 18, 24⟩ = 16237040744126001 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_18_24 : boxUpper ⟨9, 14, 18, 24⟩ = 9819906492886150 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_18_24 : boxUpper ⟨10, 14, 18, 24⟩ = 11606194470906672 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_18_24 : boxUpper ⟨11, 14, 18, 24⟩ = 16433780155391292 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_18_24 : boxUpper ⟨12, 14, 18, 24⟩ = 16360027019570051 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_14_18_24 : boxUpper ⟨13, 14, 18, 24⟩ = 15659336974908036 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_18_24 : boxUpper ⟨9, 15, 18, 24⟩ = 12002814141453508 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_18_24 : boxUpper ⟨10, 15, 18, 24⟩ = 16841947758989589 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_18_24 : boxUpper ⟨11, 15, 18, 24⟩ = 16638672594627509 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_15_18_24 : boxUpper ⟨12, 15, 18, 24⟩ = 15822807728615293 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_15_18_24 : boxUpper ⟨13, 15, 18, 24⟩ = 15162881451493828 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_14_15_18_24 : boxUpper ⟨14, 15, 18, 24⟩ = 14636869692982296 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_18_24 : boxUpper ⟨9, 16, 18, 24⟩ = 17493775537603402 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_18_24 : boxUpper ⟨10, 16, 18, 24⟩ = 17124834841104435 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_16_18_24 : boxUpper ⟨11, 16, 18, 24⟩ = 16160225448283158 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_16_18_24 : boxUpper ⟨12, 16, 18, 24⟩ = 15385837450602481 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_13_16_18_24 : boxUpper ⟨13, 16, 18, 24⟩ = 14769642968807800 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_17_18_24 : boxUpper ⟨9, 17, 18, 24⟩ = 17855335732462424 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_17_18_24 : boxUpper ⟨10, 17, 18, 24⟩ = 16694279900198723 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_17_18_24 : boxUpper ⟨11, 17, 18, 24⟩ = 15772393014832929 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_17_18_24 : boxUpper ⟨12, 17, 18, 24⟩ = 15042560957009877 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_18 : pairUpper 24 18 = 418860372332708033 := by
  have members : atPair 24 18 = [
    ⟨9, 10, 18, 24⟩,
    ⟨9, 11, 18, 24⟩,
    ⟨10, 11, 18, 24⟩,
    ⟨9, 12, 18, 24⟩,
    ⟨10, 12, 18, 24⟩,
    ⟨11, 12, 18, 24⟩,
    ⟨9, 13, 18, 24⟩,
    ⟨10, 13, 18, 24⟩,
    ⟨11, 13, 18, 24⟩,
    ⟨12, 13, 18, 24⟩,
    ⟨9, 14, 18, 24⟩,
    ⟨10, 14, 18, 24⟩,
    ⟨11, 14, 18, 24⟩,
    ⟨12, 14, 18, 24⟩,
    ⟨13, 14, 18, 24⟩,
    ⟨9, 15, 18, 24⟩,
    ⟨10, 15, 18, 24⟩,
    ⟨11, 15, 18, 24⟩,
    ⟨12, 15, 18, 24⟩,
    ⟨13, 15, 18, 24⟩,
    ⟨14, 15, 18, 24⟩,
    ⟨9, 16, 18, 24⟩,
    ⟨10, 16, 18, 24⟩,
    ⟨11, 16, 18, 24⟩,
    ⟨12, 16, 18, 24⟩,
    ⟨13, 16, 18, 24⟩,
    ⟨9, 17, 18, 24⟩,
    ⟨10, 17, 18, 24⟩,
    ⟨11, 17, 18, 24⟩,
    ⟨12, 17, 18, 24⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_9_10_18_24, box_9_11_18_24, box_10_11_18_24, box_9_12_18_24, box_10_12_18_24, box_11_12_18_24, box_9_13_18_24, box_10_13_18_24, box_11_13_18_24, box_12_13_18_24, box_9_14_18_24, box_10_14_18_24, box_11_14_18_24, box_12_14_18_24, box_13_14_18_24, box_9_15_18_24, box_10_15_18_24, box_11_15_18_24, box_12_15_18_24, box_13_15_18_24, box_14_15_18_24, box_9_16_18_24, box_10_16_18_24, box_11_16_18_24, box_12_16_18_24, box_13_16_18_24, box_9_17_18_24, box_10_17_18_24, box_11_17_18_24, box_12_17_18_24]
  all_goals decide +kernel

private theorem box_6_7_21_24 : boxUpper ⟨6, 7, 21, 24⟩ = 19874072994111455 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_21_24 : boxUpper ⟨6, 8, 21, 24⟩ = 17959437439038359 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_21_24 : boxUpper ⟨7, 8, 21, 24⟩ = 15943750116364211 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_21_24 : boxUpper ⟨6, 9, 21, 24⟩ = 16472712318716613 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_21_24 : boxUpper ⟨7, 9, 21, 24⟩ = 14633916872187286 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_21_24 : boxUpper ⟨8, 9, 21, 24⟩ = 13251368798697285 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_21_24 : boxUpper ⟨6, 10, 21, 24⟩ = 15291986978299065 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_21_24 : boxUpper ⟨7, 10, 21, 24⟩ = 13594814251280981 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_21_24 : boxUpper ⟨8, 10, 21, 24⟩ = 12319832211210341 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_21_24 : boxUpper ⟨9, 10, 21, 24⟩ = 11333666782683506 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_21_24 : boxUpper ⟨6, 11, 21, 24⟩ = 14338305598760988 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_21_24 : boxUpper ⟨7, 11, 21, 24⟩ = 12756708210985097 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_21_24 : boxUpper ⟨8, 11, 21, 24⟩ = 11569658743495372 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_21_24 : boxUpper ⟨9, 11, 21, 24⟩ = 10652641701885243 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_21_24 : boxUpper ⟨10, 11, 21, 24⟩ = 9929253882195031 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_21_24 : boxUpper ⟨6, 12, 21, 24⟩ = 13558348027883293 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_21_24 : boxUpper ⟨7, 12, 21, 24⟩ = 12072523688783277 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_21_24 : boxUpper ⟨8, 12, 21, 24⟩ = 10958501410856417 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_21_24 : boxUpper ⟨9, 12, 21, 24⟩ = 10099078006045426 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_21_24 : boxUpper ⟨10, 12, 21, 24⟩ = 9422357805469178 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_21_24 : boxUpper ⟨11, 12, 21, 24⟩ = 8890153202808447 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_21_24 : boxUpper ⟨6, 13, 21, 24⟩ = 12914879938506298 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_21_24 : boxUpper ⟨7, 13, 21, 24⟩ = 11509406641737639 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_21_24 : boxUpper ⟨8, 13, 21, 24⟩ = 10456826083805570 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_21_24 : boxUpper ⟨9, 13, 21, 24⟩ = 9646039818814356 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_21_24 : boxUpper ⟨10, 13, 21, 24⟩ = 9017309396456389 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_21_24 : boxUpper ⟨11, 13, 21, 24⟩ = 10795930189072684 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_21_24 : boxUpper ⟨12, 13, 21, 24⟩ = 15449394731246173 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_21_24 : boxUpper ⟨6, 14, 21, 24⟩ = 12381189648639928 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_21_24 : boxUpper ⟨7, 14, 21, 24⟩ = 11043809205999392 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_21_24 : boxUpper ⟨8, 14, 21, 24⟩ = 10043486994790448 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_21_24 : boxUpper ⟨9, 14, 21, 24⟩ = 9282883805014628 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_21_24 : boxUpper ⟨10, 14, 21, 24⟩ = 11009937817976816 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_21_24 : boxUpper ⟨11, 14, 21, 24⟩ = 15636583165396618 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_14_21_24 : boxUpper ⟨12, 14, 21, 24⟩ = 15626522948041028 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_21_24 : boxUpper ⟨6, 15, 21, 24⟩ = 11937697953832747 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_21_24 : boxUpper ⟨7, 15, 21, 24⟩ = 10658495357240539 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_21_24 : boxUpper ⟨8, 15, 21, 24⟩ = 9712016840836891 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_21_24 : boxUpper ⟨9, 15, 21, 24⟩ = 11386163103033810 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_21_24 : boxUpper ⟨10, 15, 21, 24⟩ = 16024935170488740 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_15_21_24 : boxUpper ⟨11, 15, 21, 24⟩ = 15892655083992428 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_21_24 : boxUpper ⟨6, 16, 21, 24⟩ = 11569813515394869 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_21_24 : boxUpper ⟨7, 16, 21, 24⟩ = 10350173344869663 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_21_24 : boxUpper ⟨8, 16, 21, 24⟩ = 11958366686313746 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_21_24 : boxUpper ⟨9, 16, 21, 24⟩ = 16645116648507549 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_16_21_24 : boxUpper ⟨10, 16, 21, 24⟩ = 16356983112520277 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_17_21_24 : boxUpper ⟨6, 17, 21, 24⟩ = 11276834369454299 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_17_21_24 : boxUpper ⟨7, 17, 21, 24⟩ = 12784677018838751 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_17_21_24 : boxUpper ⟨8, 17, 21, 24⟩ = 17550956977689260 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_17_21_24 : boxUpper ⟨9, 17, 21, 24⟩ = 17054672374991933 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_18_21_24 : boxUpper ⟨6, 18, 21, 24⟩ = 13964614795550207 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_18_21_24 : boxUpper ⟨7, 18, 21, 24⟩ = 18832452765526495 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_18_21_24 : boxUpper ⟨8, 18, 21, 24⟩ = 18044458353410241 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_21 : pairUpper 24 21 = 691738372899747283 := by
  have members : atPair 24 21 = [
    ⟨6, 7, 21, 24⟩,
    ⟨6, 8, 21, 24⟩,
    ⟨7, 8, 21, 24⟩,
    ⟨6, 9, 21, 24⟩,
    ⟨7, 9, 21, 24⟩,
    ⟨8, 9, 21, 24⟩,
    ⟨6, 10, 21, 24⟩,
    ⟨7, 10, 21, 24⟩,
    ⟨8, 10, 21, 24⟩,
    ⟨9, 10, 21, 24⟩,
    ⟨6, 11, 21, 24⟩,
    ⟨7, 11, 21, 24⟩,
    ⟨8, 11, 21, 24⟩,
    ⟨9, 11, 21, 24⟩,
    ⟨10, 11, 21, 24⟩,
    ⟨6, 12, 21, 24⟩,
    ⟨7, 12, 21, 24⟩,
    ⟨8, 12, 21, 24⟩,
    ⟨9, 12, 21, 24⟩,
    ⟨10, 12, 21, 24⟩,
    ⟨11, 12, 21, 24⟩,
    ⟨6, 13, 21, 24⟩,
    ⟨7, 13, 21, 24⟩,
    ⟨8, 13, 21, 24⟩,
    ⟨9, 13, 21, 24⟩,
    ⟨10, 13, 21, 24⟩,
    ⟨11, 13, 21, 24⟩,
    ⟨12, 13, 21, 24⟩,
    ⟨6, 14, 21, 24⟩,
    ⟨7, 14, 21, 24⟩,
    ⟨8, 14, 21, 24⟩,
    ⟨9, 14, 21, 24⟩,
    ⟨10, 14, 21, 24⟩,
    ⟨11, 14, 21, 24⟩,
    ⟨12, 14, 21, 24⟩,
    ⟨6, 15, 21, 24⟩,
    ⟨7, 15, 21, 24⟩,
    ⟨8, 15, 21, 24⟩,
    ⟨9, 15, 21, 24⟩,
    ⟨10, 15, 21, 24⟩,
    ⟨11, 15, 21, 24⟩,
    ⟨6, 16, 21, 24⟩,
    ⟨7, 16, 21, 24⟩,
    ⟨8, 16, 21, 24⟩,
    ⟨9, 16, 21, 24⟩,
    ⟨10, 16, 21, 24⟩,
    ⟨6, 17, 21, 24⟩,
    ⟨7, 17, 21, 24⟩,
    ⟨8, 17, 21, 24⟩,
    ⟨9, 17, 21, 24⟩,
    ⟨6, 18, 21, 24⟩,
    ⟨7, 18, 21, 24⟩,
    ⟨8, 18, 21, 24⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_6_7_21_24, box_6_8_21_24, box_7_8_21_24, box_6_9_21_24, box_7_9_21_24, box_8_9_21_24, box_6_10_21_24, box_7_10_21_24, box_8_10_21_24, box_9_10_21_24, box_6_11_21_24, box_7_11_21_24, box_8_11_21_24, box_9_11_21_24, box_10_11_21_24, box_6_12_21_24, box_7_12_21_24, box_8_12_21_24, box_9_12_21_24, box_10_12_21_24, box_11_12_21_24, box_6_13_21_24, box_7_13_21_24, box_8_13_21_24, box_9_13_21_24, box_10_13_21_24, box_11_13_21_24, box_12_13_21_24, box_6_14_21_24, box_7_14_21_24, box_8_14_21_24, box_9_14_21_24, box_10_14_21_24, box_11_14_21_24, box_12_14_21_24, box_6_15_21_24, box_7_15_21_24, box_8_15_21_24, box_9_15_21_24, box_10_15_21_24, box_11_15_21_24, box_6_16_21_24, box_7_16_21_24, box_8_16_21_24, box_9_16_21_24, box_10_16_21_24, box_6_17_21_24, box_7_17_21_24, box_8_17_21_24, box_9_17_21_24, box_6_18_21_24, box_7_18_21_24, box_8_18_21_24]
  all_goals decide +kernel

private theorem box_5_6_22_24 : boxUpper ⟨5, 6, 22, 24⟩ = 25373253149130889 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_22_24 : boxUpper ⟨5, 7, 22, 24⟩ = 22496841460607151 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_22_24 : boxUpper ⟨6, 7, 22, 24⟩ = 19471702483122738 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_22_24 : boxUpper ⟨5, 8, 22, 24⟩ = 20329504541285848 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_22_24 : boxUpper ⟨6, 8, 22, 24⟩ = 17607273694724766 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_22_24 : boxUpper ⟨7, 8, 22, 24⟩ = 15641821362905511 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_22_24 : boxUpper ⟨5, 9, 22, 24⟩ = 18646552434815058 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_22_24 : boxUpper ⟨6, 9, 22, 24⟩ = 16160758743507302 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_22_24 : boxUpper ⟨7, 9, 22, 24⟩ = 14367158787667039 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_22_24 : boxUpper ⟨8, 9, 22, 24⟩ = 13019736075131020 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_22_24 : boxUpper ⟨5, 10, 22, 24⟩ = 17309984764231807 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_22_24 : boxUpper ⟨6, 10, 22, 24⟩ = 15013223244169576 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_22_24 : boxUpper ⟨7, 10, 22, 24⟩ = 13357173146673235 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_22_24 : boxUpper ⟨8, 10, 22, 24⟩ = 12114243437496548 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_22_24 : boxUpper ⟨9, 10, 22, 24⟩ = 11154057259200296 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_22_24 : boxUpper ⟨5, 11, 22, 24⟩ = 16230425109527261 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_22_24 : boxUpper ⟨6, 11, 22, 24⟩ = 14087656679808006 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_22_24 : boxUpper ⟨7, 11, 22, 24⟩ = 12543822538306854 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_22_24 : boxUpper ⟨8, 11, 22, 24⟩ = 11386305908052783 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_22_24 : boxUpper ⟨9, 11, 22, 24⟩ = 10493327834590309 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_22_24 : boxUpper ⟨10, 11, 22, 24⟩ = 9790185738260768 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_22_24 : boxUpper ⟨5, 12, 22, 24⟩ = 15347516071276114 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_22_24 : boxUpper ⟨6, 12, 22, 24⟩ = 13332071857428402 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_22_24 : boxUpper ⟨7, 12, 22, 24⟩ = 11881193926058670 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_22_24 : boxUpper ⟨8, 12, 22, 24⟩ = 10794608722625474 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_22_24 : boxUpper ⟨9, 12, 22, 24⟩ = 9957628781592874 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_22_24 : boxUpper ⟨10, 12, 22, 24⟩ = 9299925358022575 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_22_24 : boxUpper ⟨11, 12, 22, 24⟩ = 8784263934771149 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_22_24 : boxUpper ⟨5, 13, 22, 24⟩ = 14619109048565955 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_22_24 : boxUpper ⟨6, 13, 22, 24⟩ = 12710186485600916 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_22_24 : boxUpper ⟨7, 13, 22, 24⟩ = 11337266075995478 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_22_24 : boxUpper ⟨8, 13, 22, 24⟩ = 10310360644098589 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_22_24 : boxUpper ⟨9, 13, 22, 24⟩ = 9520697429568241 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_22_24 : boxUpper ⟨10, 13, 22, 24⟩ = 8909903594534925 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_22_24 : boxUpper ⟨11, 13, 22, 24⟩ = 10681526863803709 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_12_13_22_24 : boxUpper ⟨12, 13, 22, 24⟩ = 15310811042209841 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_22_24 : boxUpper ⟨5, 14, 22, 24⟩ = 14014966833596164 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_22_24 : boxUpper ⟨6, 14, 22, 24⟩ = 12195995492141922 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_22_24 : boxUpper ⟨7, 14, 22, 24⟩ = 10889112479934686 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_22_24 : boxUpper ⟨8, 14, 22, 24⟩ = 9912973709407549 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_22_24 : boxUpper ⟨9, 14, 22, 24⟩ = 9172310437138443 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_22_24 : boxUpper ⟨10, 14, 22, 24⟩ = 10893262858096748 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_14_22_24 : boxUpper ⟨11, 14, 22, 24⟩ = 15496311610794832 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_15_22_24 : boxUpper ⟨5, 15, 22, 24⟩ = 13512926009690459 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_22_24 : boxUpper ⟨6, 15, 22, 24⟩ = 11770464237086954 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_22_24 : boxUpper ⟨7, 15, 22, 24⟩ = 10519979649905194 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_22_24 : boxUpper ⟨8, 15, 22, 24⟩ = 9596324588503227 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_22_24 : boxUpper ⟨9, 15, 22, 24⟩ = 11265494247399903 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_15_22_24 : boxUpper ⟨10, 15, 22, 24⟩ = 15881161220843610 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_16_22_24 : boxUpper ⟨5, 16, 22, 24⟩ = 13096469291447242 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_22_24 : boxUpper ⟨6, 16, 22, 24⟩ = 11419437612742982 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_22_24 : boxUpper ⟨7, 16, 22, 24⟩ = 10226867703172028 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_22_24 : boxUpper ⟨8, 16, 22, 24⟩ = 11831622598505138 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_16_22_24 : boxUpper ⟨9, 16, 22, 24⟩ = 16495747706083182 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_17_22_24 : boxUpper ⟨5, 17, 22, 24⟩ = 12753141423916351 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_17_22_24 : boxUpper ⟨6, 17, 22, 24⟩ = 11142470880843506 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_17_22_24 : boxUpper ⟨7, 17, 22, 24⟩ = 12649157886424206 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_17_22_24 : boxUpper ⟨8, 17, 22, 24⟩ = 17393411953584600 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_18_22_24 : boxUpper ⟨5, 18, 22, 24⟩ = 12484786191416901 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_18_22_24 : boxUpper ⟨6, 18, 22, 24⟩ = 13816561362188939 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_18_22_24 : boxUpper ⟨7, 18, 22, 24⟩ = 18663332922091254 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_22 : pairUpper 24 22 = 816486369136323697 := by
  have members : atPair 24 22 = [
    ⟨5, 6, 22, 24⟩,
    ⟨5, 7, 22, 24⟩,
    ⟨6, 7, 22, 24⟩,
    ⟨5, 8, 22, 24⟩,
    ⟨6, 8, 22, 24⟩,
    ⟨7, 8, 22, 24⟩,
    ⟨5, 9, 22, 24⟩,
    ⟨6, 9, 22, 24⟩,
    ⟨7, 9, 22, 24⟩,
    ⟨8, 9, 22, 24⟩,
    ⟨5, 10, 22, 24⟩,
    ⟨6, 10, 22, 24⟩,
    ⟨7, 10, 22, 24⟩,
    ⟨8, 10, 22, 24⟩,
    ⟨9, 10, 22, 24⟩,
    ⟨5, 11, 22, 24⟩,
    ⟨6, 11, 22, 24⟩,
    ⟨7, 11, 22, 24⟩,
    ⟨8, 11, 22, 24⟩,
    ⟨9, 11, 22, 24⟩,
    ⟨10, 11, 22, 24⟩,
    ⟨5, 12, 22, 24⟩,
    ⟨6, 12, 22, 24⟩,
    ⟨7, 12, 22, 24⟩,
    ⟨8, 12, 22, 24⟩,
    ⟨9, 12, 22, 24⟩,
    ⟨10, 12, 22, 24⟩,
    ⟨11, 12, 22, 24⟩,
    ⟨5, 13, 22, 24⟩,
    ⟨6, 13, 22, 24⟩,
    ⟨7, 13, 22, 24⟩,
    ⟨8, 13, 22, 24⟩,
    ⟨9, 13, 22, 24⟩,
    ⟨10, 13, 22, 24⟩,
    ⟨11, 13, 22, 24⟩,
    ⟨12, 13, 22, 24⟩,
    ⟨5, 14, 22, 24⟩,
    ⟨6, 14, 22, 24⟩,
    ⟨7, 14, 22, 24⟩,
    ⟨8, 14, 22, 24⟩,
    ⟨9, 14, 22, 24⟩,
    ⟨10, 14, 22, 24⟩,
    ⟨11, 14, 22, 24⟩,
    ⟨5, 15, 22, 24⟩,
    ⟨6, 15, 22, 24⟩,
    ⟨7, 15, 22, 24⟩,
    ⟨8, 15, 22, 24⟩,
    ⟨9, 15, 22, 24⟩,
    ⟨10, 15, 22, 24⟩,
    ⟨5, 16, 22, 24⟩,
    ⟨6, 16, 22, 24⟩,
    ⟨7, 16, 22, 24⟩,
    ⟨8, 16, 22, 24⟩,
    ⟨9, 16, 22, 24⟩,
    ⟨5, 17, 22, 24⟩,
    ⟨6, 17, 22, 24⟩,
    ⟨7, 17, 22, 24⟩,
    ⟨8, 17, 22, 24⟩,
    ⟨5, 18, 22, 24⟩,
    ⟨6, 18, 22, 24⟩,
    ⟨7, 18, 22, 24⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_5_6_22_24, box_5_7_22_24, box_6_7_22_24, box_5_8_22_24, box_6_8_22_24, box_7_8_22_24, box_5_9_22_24, box_6_9_22_24, box_7_9_22_24, box_8_9_22_24, box_5_10_22_24, box_6_10_22_24, box_7_10_22_24, box_8_10_22_24, box_9_10_22_24, box_5_11_22_24, box_6_11_22_24, box_7_11_22_24, box_8_11_22_24, box_9_11_22_24, box_10_11_22_24, box_5_12_22_24, box_6_12_22_24, box_7_12_22_24, box_8_12_22_24, box_9_12_22_24, box_10_12_22_24, box_11_12_22_24, box_5_13_22_24, box_6_13_22_24, box_7_13_22_24, box_8_13_22_24, box_9_13_22_24, box_10_13_22_24, box_11_13_22_24, box_12_13_22_24, box_5_14_22_24, box_6_14_22_24, box_7_14_22_24, box_8_14_22_24, box_9_14_22_24, box_10_14_22_24, box_11_14_22_24, box_5_15_22_24, box_6_15_22_24, box_7_15_22_24, box_8_15_22_24, box_9_15_22_24, box_10_15_22_24, box_5_16_22_24, box_6_16_22_24, box_7_16_22_24, box_8_16_22_24, box_9_16_22_24, box_5_17_22_24, box_6_17_22_24, box_7_17_22_24, box_8_17_22_24, box_5_18_22_24, box_6_18_22_24, box_7_18_22_24]
  all_goals decide +kernel

private theorem box_4_5_23_24 : boxUpper ⟨4, 5, 23, 24⟩ = 34475729040913513 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_6_23_24 : boxUpper ⟨4, 6, 23, 24⟩ = 29803653521502668 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_6_23_24 : boxUpper ⟨5, 6, 23, 24⟩ = 24893631657098420 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_7_23_24 : boxUpper ⟨4, 7, 23, 24⟩ = 26424942109430000 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_7_23_24 : boxUpper ⟨5, 7, 23, 24⟩ = 22085243229519418 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_7_23_24 : boxUpper ⟨6, 7, 23, 24⟩ = 19127894708256084 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_8_23_24 : boxUpper ⟨4, 8, 23, 24⟩ = 23879124018384051 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_8_23_24 : boxUpper ⟨5, 8, 23, 24⟩ = 19970536831538114 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_8_23_24 : boxUpper ⟨6, 8, 23, 24⟩ = 17308230561787892 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_8_23_24 : boxUpper ⟨7, 8, 23, 24⟩ = 15387268572111355 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_9_23_24 : boxUpper ⟨4, 9, 23, 24⟩ = 21902273433909004 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_9_23_24 : boxUpper ⟨5, 9, 23, 24⟩ = 18329841090076218 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_9_23_24 : boxUpper ⟨6, 9, 23, 24⟩ = 15897752742901005 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_9_23_24 : boxUpper ⟨7, 9, 23, 24⟩ = 14144126124947473 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_9_23_24 : boxUpper ⟨8, 9, 23, 24⟩ = 12827960586838368 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_10_23_24 : boxUpper ⟨4, 10, 23, 24⟩ = 20332291978762464 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_10_23_24 : boxUpper ⟨5, 10, 23, 24⟩ = 17028256649620168 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_10_23_24 : boxUpper ⟨6, 10, 23, 24⟩ = 14780150968122116 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_10_23_24 : boxUpper ⟨7, 10, 23, 24⟩ = 13160422146383285 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_10_23_24 : boxUpper ⟨8, 10, 23, 24⟩ = 11946001455671138 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_10_23_24 : boxUpper ⟨9, 10, 23, 24⟩ = 11009123441744438 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_11_23_24 : boxUpper ⟨4, 11, 23, 24⟩ = 19064196006408155 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_11_23_24 : boxUpper ⟨5, 11, 23, 24⟩ = 15978435560248153 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_11_23_24 : boxUpper ⟨6, 11, 23, 24⟩ = 13880133797820599 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_11_23_24 : boxUpper ⟨7, 11, 23, 24⟩ = 12369607814945550 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_11_23_24 : boxUpper ⟨8, 11, 23, 24⟩ = 11238350681840868 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_11_23_24 : boxUpper ⟨9, 11, 23, 24⟩ = 10366960046855386 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_11_23_24 : boxUpper ⟨10, 11, 23, 24⟩ = 9682215887323154 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_12_23_24 : boxUpper ⟨4, 12, 23, 24⟩ = 18027088215073135 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_12_23_24 : boxUpper ⟨5, 12, 23, 24⟩ = 15121412126238457 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_12_23_24 : boxUpper ⟨6, 12, 23, 24⟩ = 13146896345096423 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_12_23_24 : boxUpper ⟨7, 12, 23, 24⟩ = 11726800028035871 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_12_23_24 : boxUpper ⟨8, 12, 23, 24⟩ = 10664607885287741 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_12_23_24 : boxUpper ⟨9, 12, 23, 24⟩ = 9847809626789148 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_12_23_24 : boxUpper ⟨10, 12, 23, 24⟩ = 9207439010948884 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_12_23_24 : boxUpper ⟨11, 12, 23, 24⟩ = 8707113754629370 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_13_23_24 : boxUpper ⟨4, 13, 23, 24⟩ = 17171459722707797 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_13_23_24 : boxUpper ⟨5, 13, 23, 24⟩ = 14416033644459612 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_13_23_24 : boxUpper ⟨6, 13, 23, 24⟩ = 12545005600855878 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_13_23_24 : boxUpper ⟨7, 13, 23, 24⟩ = 11200720830548256 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_13_23_24 : boxUpper ⟨8, 13, 23, 24⟩ = 10196645491918967 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_13_23_24 : boxUpper ⟨9, 13, 23, 24⟩ = 9426011880407844 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_13_23_24 : boxUpper ⟨10, 13, 23, 24⟩ = 8831647831535798 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_11_13_23_24 : boxUpper ⟨11, 13, 23, 24⟩ = 10610647723100878 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_14_23_24 : boxUpper ⟨4, 14, 23, 24⟩ = 16461792993088596 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_14_23_24 : boxUpper ⟨5, 14, 23, 24⟩ = 13832804146383040 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_14_23_24 : boxUpper ⟨6, 14, 23, 24⟩ = 12049092254167338 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_14_23_24 : boxUpper ⟨7, 14, 23, 24⟩ = 10769004028271238 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_14_23_24 : boxUpper ⟨8, 14, 23, 24⟩ = 9814380116051971 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_14_23_24 : boxUpper ⟨9, 14, 23, 24⟩ = 9091745397966708 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_10_14_23_24 : boxUpper ⟨10, 14, 23, 24⟩ = 10820964630765687 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_15_23_24 : boxUpper ⟨4, 15, 23, 24⟩ = 15872054099049443 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_15_23_24 : boxUpper ⟨5, 15, 23, 24⟩ = 13350133727903735 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_15_23_24 : boxUpper ⟨6, 15, 23, 24⟩ = 11640617692951477 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_15_23_24 : boxUpper ⟨7, 15, 23, 24⟩ = 10415337719607295 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_15_23_24 : boxUpper ⟨8, 15, 23, 24⟩ = 9512027520089275 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_9_15_23_24 : boxUpper ⟨9, 15, 23, 24⟩ = 11190699969600775 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_16_23_24 : boxUpper ⟨4, 16, 23, 24⟩ = 15382841132773009 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_16_23_24 : boxUpper ⟨5, 16, 23, 24⟩ = 12951966976908984 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_16_23_24 : boxUpper ⟨6, 16, 23, 24⟩ = 11305830940017448 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_16_23_24 : boxUpper ⟨7, 16, 23, 24⟩ = 10137019552099042 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_8_16_23_24 : boxUpper ⟨8, 16, 23, 24⟩ = 11753028897649514 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_17_23_24 : boxUpper ⟨4, 17, 23, 24⟩ = 14979523476891782 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_17_23_24 : boxUpper ⟨5, 17, 23, 24⟩ = 12626236792115887 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_17_23_24 : boxUpper ⟨6, 17, 23, 24⟩ = 11044559406358142 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_7_17_23_24 : boxUpper ⟨7, 17, 23, 24⟩ = 12565070784364430 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_4_18_23_24 : boxUpper ⟨4, 18, 23, 24⟩ = 14650996502976740 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_5_18_23_24 : boxUpper ⟨5, 18, 23, 24⟩ = 12375047810265458 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem box_6_18_23_24 : boxUpper ⟨6, 18, 23, 24⟩ = 13724616218765112 := by
  exact (boxUpper_eq_fast _).trans (by decide +kernel)

private theorem pair_23 : pairUpper 24 23 = 996459087169675242 := by
  have members : atPair 24 23 = [
    ⟨4, 5, 23, 24⟩,
    ⟨4, 6, 23, 24⟩,
    ⟨5, 6, 23, 24⟩,
    ⟨4, 7, 23, 24⟩,
    ⟨5, 7, 23, 24⟩,
    ⟨6, 7, 23, 24⟩,
    ⟨4, 8, 23, 24⟩,
    ⟨5, 8, 23, 24⟩,
    ⟨6, 8, 23, 24⟩,
    ⟨7, 8, 23, 24⟩,
    ⟨4, 9, 23, 24⟩,
    ⟨5, 9, 23, 24⟩,
    ⟨6, 9, 23, 24⟩,
    ⟨7, 9, 23, 24⟩,
    ⟨8, 9, 23, 24⟩,
    ⟨4, 10, 23, 24⟩,
    ⟨5, 10, 23, 24⟩,
    ⟨6, 10, 23, 24⟩,
    ⟨7, 10, 23, 24⟩,
    ⟨8, 10, 23, 24⟩,
    ⟨9, 10, 23, 24⟩,
    ⟨4, 11, 23, 24⟩,
    ⟨5, 11, 23, 24⟩,
    ⟨6, 11, 23, 24⟩,
    ⟨7, 11, 23, 24⟩,
    ⟨8, 11, 23, 24⟩,
    ⟨9, 11, 23, 24⟩,
    ⟨10, 11, 23, 24⟩,
    ⟨4, 12, 23, 24⟩,
    ⟨5, 12, 23, 24⟩,
    ⟨6, 12, 23, 24⟩,
    ⟨7, 12, 23, 24⟩,
    ⟨8, 12, 23, 24⟩,
    ⟨9, 12, 23, 24⟩,
    ⟨10, 12, 23, 24⟩,
    ⟨11, 12, 23, 24⟩,
    ⟨4, 13, 23, 24⟩,
    ⟨5, 13, 23, 24⟩,
    ⟨6, 13, 23, 24⟩,
    ⟨7, 13, 23, 24⟩,
    ⟨8, 13, 23, 24⟩,
    ⟨9, 13, 23, 24⟩,
    ⟨10, 13, 23, 24⟩,
    ⟨11, 13, 23, 24⟩,
    ⟨4, 14, 23, 24⟩,
    ⟨5, 14, 23, 24⟩,
    ⟨6, 14, 23, 24⟩,
    ⟨7, 14, 23, 24⟩,
    ⟨8, 14, 23, 24⟩,
    ⟨9, 14, 23, 24⟩,
    ⟨10, 14, 23, 24⟩,
    ⟨4, 15, 23, 24⟩,
    ⟨5, 15, 23, 24⟩,
    ⟨6, 15, 23, 24⟩,
    ⟨7, 15, 23, 24⟩,
    ⟨8, 15, 23, 24⟩,
    ⟨9, 15, 23, 24⟩,
    ⟨4, 16, 23, 24⟩,
    ⟨5, 16, 23, 24⟩,
    ⟨6, 16, 23, 24⟩,
    ⟨7, 16, 23, 24⟩,
    ⟨8, 16, 23, 24⟩,
    ⟨4, 17, 23, 24⟩,
    ⟨5, 17, 23, 24⟩,
    ⟨6, 17, 23, 24⟩,
    ⟨7, 17, 23, 24⟩,
    ⟨4, 18, 23, 24⟩,
    ⟨5, 18, 23, 24⟩,
    ⟨6, 18, 23, 24⟩] := by decide +kernel
  simp only [pairUpper, members, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    box_4_5_23_24, box_4_6_23_24, box_5_6_23_24, box_4_7_23_24, box_5_7_23_24, box_6_7_23_24, box_4_8_23_24, box_5_8_23_24, box_6_8_23_24, box_7_8_23_24, box_4_9_23_24, box_5_9_23_24, box_6_9_23_24, box_7_9_23_24, box_8_9_23_24, box_4_10_23_24, box_5_10_23_24, box_6_10_23_24, box_7_10_23_24, box_8_10_23_24, box_9_10_23_24, box_4_11_23_24, box_5_11_23_24, box_6_11_23_24, box_7_11_23_24, box_8_11_23_24, box_9_11_23_24, box_10_11_23_24, box_4_12_23_24, box_5_12_23_24, box_6_12_23_24, box_7_12_23_24, box_8_12_23_24, box_9_12_23_24, box_10_12_23_24, box_11_12_23_24, box_4_13_23_24, box_5_13_23_24, box_6_13_23_24, box_7_13_23_24, box_8_13_23_24, box_9_13_23_24, box_10_13_23_24, box_11_13_23_24, box_4_14_23_24, box_5_14_23_24, box_6_14_23_24, box_7_14_23_24, box_8_14_23_24, box_9_14_23_24, box_10_14_23_24, box_4_15_23_24, box_5_15_23_24, box_6_15_23_24, box_7_15_23_24, box_8_15_23_24, box_9_15_23_24, box_4_16_23_24, box_5_16_23_24, box_6_16_23_24, box_7_16_23_24, box_8_16_23_24, box_4_17_23_24, box_5_17_23_24, box_6_17_23_24, box_7_17_23_24, box_4_18_23_24, box_5_18_23_24, box_6_18_23_24]
  all_goals decide +kernel

theorem column_24 : columnUpper 24 = 3421932875263880838 := by
  unfold columnUpper
  have indices : List.range 24 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pair_15, pair_16, pair_17, pair_18, pair_21, pair_22, pair_23]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.column_24
