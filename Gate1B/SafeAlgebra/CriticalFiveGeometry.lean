/-
# Gate 1B v8.2 — critical-five product geometry (capacity arithmetic only)

Exact rational exponent bookkeeping for the nine-box labelled product.  For
`J ⊆ Fin 9` with `|J| = j` the labels carry

    C_J exponent = j/9,      a_J exponent = (9-j)/9,

so `C_J · a_J` has total exponent `1` (`labelExponent_total`), and the defect
energy exponent is

    defectEnergyExponent j = 2j/9 − 1.

`defectEnergy_le_neg_one_ninth_of_le_four`, `defectEnergy_order_four` and
`defectEnergy_order_five` are the three requested facts.

**This is capacity arithmetic only.**  Nothing here says that `j ≤ 4` is
analytically closed, and no defect term is given an analytic interpretation.
The nine-box ANOVA identity itself is *not* restated: it is already banked as
`Universal.SafeAlgebra.finset_prod_add_eq_sum_powerset` and
`Gate1B.SafeExtensions.fullNine_anova`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- Exponent of the `C_J` label, `j/9`. -/
def cLabelExponent (j : ℕ) : ℚ := (j : ℚ) / 9

/-- Exponent of the `a_J` label, `(9-j)/9`, for `j ≤ 9`. -/
def aLabelExponent (j : ℕ) : ℚ := (9 - (j : ℚ)) / 9

/-- **The labelled product has total exponent one.** -/
theorem labelExponent_total (j : ℕ) : cLabelExponent j + aLabelExponent j = 1 := by
  unfold cLabelExponent aLabelExponent
  ring

/-- The defect energy exponent `2j/9 − 1`. -/
def defectEnergyExponent (j : ℕ) : ℚ := 2 * (j : ℚ) / 9 - 1

/-- **Orders at most four have exponent at most `−1/9`.** -/
theorem defectEnergy_le_neg_one_ninth_of_le_four {j : ℕ} (hj : j ≤ 4) :
    defectEnergyExponent j ≤ -(1 / 9) := by
  have hjq : (j : ℚ) ≤ 4 := by exact_mod_cast hj
  unfold defectEnergyExponent
  linarith

/-- Order exactly four is the boundary case `−1/9`. -/
theorem defectEnergy_order_four : defectEnergyExponent 4 = -(1 / 9) := by
  norm_num [defectEnergyExponent]

/-- Order five is already positive, `+1/9`. -/
theorem defectEnergy_order_five : defectEnergyExponent 5 = 1 / 9 := by
  norm_num [defectEnergyExponent]

/-- The exponent is strictly increasing in the defect order. -/
theorem defectEnergyExponent_strictMono {j k : ℕ} (h : j < k) :
    defectEnergyExponent j < defectEnergyExponent k := by
  have : (j : ℚ) < (k : ℚ) := by exact_mod_cast h
  unfold defectEnergyExponent
  linarith

/-- Consequently order four is the last order with a negative exponent. -/
theorem defectEnergy_neg_iff_le_four (j : ℕ) : defectEnergyExponent j < 0 ↔ j ≤ 4 := by
  constructor
  · intro h
    by_contra hj
    push_neg at hj
    have h5 : defectEnergyExponent 5 ≤ defectEnergyExponent j := by
      have hj5 : 5 ≤ j := hj
      rcases eq_or_lt_of_le hj5 with h' | h'
      · rw [h']
      · exact le_of_lt (defectEnergyExponent_strictMono h')
    rw [defectEnergy_order_five] at h5
    linarith
  · intro hj
    have := defectEnergy_le_neg_one_ninth_of_le_four hj
    linarith

end Gate1B.SafeAlgebra
