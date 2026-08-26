/-
# Gate 1B v8.2 — defect-order exponent ledger (exact ℚ arithmetic)

With `C = Y^j` and `X = Y^9`, the exponent of `C² / X` in base `Y` is
`2j/9 − 1`.  This file banks that ledger and nothing else.

**FIREWALL.**  This is exponent bookkeeping in ℚ.  It does **not** declare
"orders 1–4 analytically closed": no large-sieve or any other analytic input
appears anywhere in this file.
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- The base-`Y` exponent of `C²/X` when `C = Y^j` and `X = Y^9`. -/
def defectOrderC2OverX (j : ℕ) : ℚ := 2 * (j : ℚ) / 9 - 1

/-- **Orders 1–4 have exponent margin at most `−1/9`.** -/
theorem defectOrder_le_four_C2OverX_margin {j : ℕ} (h1 : 1 ≤ j) (h4 : j ≤ 4) :
    defectOrderC2OverX j ≤ -(1 / 9) := by
  have hj : (j : ℚ) ≤ 4 := by exact_mod_cast h4
  have : (1 : ℚ) ≤ (j : ℚ) := by exact_mod_cast h1
  unfold defectOrderC2OverX
  linarith

/-- **Order 4 is exactly `−1/9`.** -/
theorem defectOrder_four_C2OverX_eq_neg_one_ninth :
    defectOrderC2OverX 4 = -(1 / 9) := by
  unfold defectOrderC2OverX; norm_num

/-- **Order 5 is exactly `+1/9`** — the coefficient-blind tax. -/
theorem defectOrder_five_C2OverX_eq_one_ninth :
    defectOrderC2OverX 5 = 1 / 9 := by
  unfold defectOrderC2OverX; norm_num

/-- The ledger is strictly increasing in the defect order. -/
theorem defectOrderC2OverX_strictMono {i j : ℕ} (h : i < j) :
    defectOrderC2OverX i < defectOrderC2OverX j := by
  have : (i : ℚ) < (j : ℚ) := by exact_mod_cast h
  unfold defectOrderC2OverX
  linarith

end Gate1B.SafeExtensions
