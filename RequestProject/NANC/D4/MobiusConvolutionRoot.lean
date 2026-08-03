import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace NANC.D4

open scoped BigOperators

def rhoPrimePow : ℕ → ℚ
  | 0 => 1
  | n+1 => -((catalan n : ℚ) / (2:ℚ)^(2*n+1))

@[simp] theorem rhoPrimePow_zero : rhoPrimePow 0 = 1 := rfl
@[simp] theorem rhoPrimePow_one : rhoPrimePow 1 = -(1:ℚ)/2 := by norm_num [rhoPrimePow]
@[simp] theorem rhoPrimePow_two : rhoPrimePow 2 = -(1:ℚ)/8 := by norm_num [rhoPrimePow]
@[simp] theorem rhoPrimePow_three : rhoPrimePow 3 = -(1:ℚ)/16 := by norm_num [rhoPrimePow, catalan_two]

theorem rhoPrimePow_nonpos {n : ℕ} (hn : 1 ≤ n) : rhoPrimePow n ≤ 0 := by
  cases n with
  | zero => omega
  | succ k =>
    simp only [rhoPrimePow]
    exact neg_nonpos.mpr (div_nonneg (by positivity) (by positivity))

/- Remaining Möbius-root convolution and variation declarations are open in this partial increment. -/

end NANC.D4
