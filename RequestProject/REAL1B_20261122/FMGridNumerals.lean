import RequestProject.REAL1B_20261122.GridColumns.C21
import RequestProject.REAL1B_20261122.GridColumns.C22
import RequestProject.REAL1B_20261122.GridColumns.C23
import RequestProject.REAL1B_20261122.GridColumns.C24
import RequestProject.REAL1B_20261122.GridColumns.C25
import RequestProject.REAL1B_20261122.GridColumns.C26
import RequestProject.REAL1B_20261122.GridColumns.C27
import RequestProject.REAL1B_20261122.GridColumns.C28
import RequestProject.REAL1B_20261122.GridColumns.C29
import RequestProject.REAL1B_20261122.GridColumns.C30
import RequestProject.REAL1B_20261122.GridColumns.C31
import RequestProject.REAL1B_20261122.GridColumns.C32
import RequestProject.REAL1B_20261122.GridColumns.C33
import RequestProject.REAL1B_20261122.GridColumns.C34
import RequestProject.REAL1B_20261122.GridColumns.C35
import RequestProject.REAL1B_20261122.GridColumns.C36
import RequestProject.REAL1B_20261122.GridColumns.C37
import RequestProject.REAL1B_20261122.GridColumns.C38
import RequestProject.REAL1B_20261122.GridColumns.C39

namespace REAL1B.FM.Grid
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private theorem zero_0 : columnUpper 0 = 0 := by decide +kernel
private theorem zero_1 : columnUpper 1 = 0 := by decide +kernel
private theorem zero_2 : columnUpper 2 = 0 := by decide +kernel
private theorem zero_3 : columnUpper 3 = 0 := by decide +kernel
private theorem zero_4 : columnUpper 4 = 0 := by decide +kernel
private theorem zero_5 : columnUpper 5 = 0 := by decide +kernel
private theorem zero_6 : columnUpper 6 = 0 := by decide +kernel
private theorem zero_7 : columnUpper 7 = 0 := by decide +kernel
private theorem zero_8 : columnUpper 8 = 0 := by decide +kernel
private theorem zero_9 : columnUpper 9 = 0 := by decide +kernel
private theorem zero_10 : columnUpper 10 = 0 := by decide +kernel
private theorem zero_11 : columnUpper 11 = 0 := by decide +kernel
private theorem zero_12 : columnUpper 12 = 0 := by decide +kernel
private theorem zero_13 : columnUpper 13 = 0 := by decide +kernel
private theorem zero_14 : columnUpper 14 = 0 := by decide +kernel
private theorem zero_15 : columnUpper 15 = 0 := by decide +kernel
private theorem zero_16 : columnUpper 16 = 0 := by decide +kernel
private theorem zero_17 : columnUpper 17 = 0 := by decide +kernel
private theorem zero_18 : columnUpper 18 = 0 := by decide +kernel
private theorem zero_19 : columnUpper 19 = 0 := by decide +kernel
private theorem zero_20 : columnUpper 20 = 0 := by decide +kernel
private theorem zero_40 : columnUpper 40 = 0 := by decide +kernel
private theorem zero_41 : columnUpper 41 = 0 := by decide +kernel
private theorem zero_42 : columnUpper 42 = 0 := by decide +kernel
private theorem zero_43 : columnUpper 43 = 0 := by decide +kernel
private theorem zero_44 : columnUpper 44 = 0 := by decide +kernel
private theorem zero_45 : columnUpper 45 = 0 := by decide +kernel
private theorem zero_46 : columnUpper 46 = 0 := by decide +kernel
private theorem zero_47 : columnUpper 47 = 0 := by decide +kernel
private theorem zero_48 : columnUpper 48 = 0 := by decide +kernel

theorem total_upper_exact : totalUpper = 28449989344325252602 := by
  unfold totalUpper
  have indices : List.range 49 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48] := by decide +kernel
  simp only [indices, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_0, zero_1, zero_2, zero_3, zero_4, zero_5, zero_6, zero_7, zero_8, zero_9, zero_10, zero_11, zero_12, zero_13, zero_14, zero_15, zero_16, zero_17, zero_18, zero_19, zero_20, column_21, column_22, column_23, column_24, column_25, column_26, column_27, column_28, column_29, column_30, column_31, column_32, column_33, column_34, column_35, column_36, column_37, column_38, column_39, zero_40, zero_41, zero_42, zero_43, zero_44, zero_45, zero_46, zero_47, zero_48]
  all_goals decide +kernel

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.total_upper_exact
