import RequestProject.NANC.Gate1BDet2.DeltaExponentLedger

/-!
# Gate 1B / determinant-2 bank, Module 14: Karatsuba-regime exponent ledger

**EXPONENT INEQUALITIES ONLY.**  This module proves rational inequalities; it
does *not* prove, assume, or import Karatsuba's analytic bilinear
character-sum theorem, and it does *not* state `PrimeMC45Closed`.  The analytic
theorem (bilinear character sums over arbitrary subsets with bounded weights,
together with the explicit Appendix-A estimate) is an **external input**.

Relative to the modulus `c = X^ω` the two lengths have relative exponents

  `U_c = (4/9)/ω`,  `V_c = (5/9)/ω`.

For `13/18 ≤ ω ≤ 8/9` these satisfy `U_c ≥ 1/2` and `V_c ≥ 5/8`, i.e. the
lengths are comfortably inside the numerical hypotheses `U_c > η`,
`V_c > 1/2 + η` of the classical regime with the choice `η = 1/9`.

With `r = 10` the two normalised Appendix-A exponent expressions evaluate to
`−1/160` and `−37/160`, so the weaker (i.e. smaller in absolute value)
numerical saving is `1/160`.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Karatsuba

open Delta

/-! ## 1. Relative lengths -/

/-- `U` relative to the modulus `c = X^ω`: `U_c = (4/9)/ω`. -/
def Uc (omega : ℚ) : ℚ := 4 / (9 * omega)

/-- `V` relative to the modulus `c = X^ω`: `V_c = (5/9)/ω`. -/
def Vc (omega : ℚ) : ℚ := 5 / (9 * omega)

theorem Uc_eq_div (omega : ℚ) (h : omega ≠ 0) : Uc omega = Ue / omega := by
  simp only [Uc, Ue]
  field_simp

theorem Vc_eq_div (omega : ℚ) (h : omega ≠ 0) : Vc omega = Ve / omega := by
  simp only [Vc, Ve]
  field_simp

/-! ## 2. The window bounds -/

theorem nine_omega_pos {omega : ℚ} (h : InWindow omega) : 0 < 9 * omega := by
  have : (13 : ℚ) / 18 ≤ omega := by simpa [omegaLow] using h.1
  linarith

theorem nine_omega_le_eight {omega : ℚ} (h : InWindow omega) : 9 * omega ≤ 8 := by
  have : omega ≤ 8 / 9 := by simpa [omegaHigh] using h.2
  linarith

/-- In the window, `U_c ≥ 1/2`. -/
theorem half_le_Uc {omega : ℚ} (h : InWindow omega) : (1 : ℚ) / 2 ≤ Uc omega := by
  have hp := nine_omega_pos h
  have hl := nine_omega_le_eight h
  rw [Uc, le_div_iff₀ hp]
  linarith

/-- In the window, `V_c ≥ 5/8`. -/
theorem five_eighths_le_Vc {omega : ℚ} (h : InWindow omega) : (5 : ℚ) / 8 ≤ Vc omega := by
  have hp := nine_omega_pos h
  have hl := nine_omega_le_eight h
  rw [Vc, le_div_iff₀ hp]
  linarith

/-! ## 3. The numerical hypotheses of the classical regime -/

/-- The chosen slack parameter. -/
def etaK : ℚ := 1 / 9

/-- The chosen moment order. -/
def rK : ℕ := 10

/-- `5/8 > 1/2 + 1/9 = 11/18`. -/
theorem five_eighths_gt_half_add_eta : (5 : ℚ) / 8 > 1 / 2 + etaK := by
  norm_num [etaK]

theorem half_add_eta_eq : (1 : ℚ) / 2 + etaK = 11 / 18 := by norm_num [etaK]

/-- `1/2 > 1/9`. -/
theorem half_gt_eta : (1 : ℚ) / 2 > etaK := by norm_num [etaK]

/-- **Window ⟹ numerical hypotheses.**  In the window the relative lengths
satisfy `U_c > η` and `V_c > 1/2 + η` with `η = 1/9`. -/
theorem window_inside_numerical_hypotheses {omega : ℚ} (h : InWindow omega) :
    etaK < Uc omega ∧ 1 / 2 + etaK < Vc omega := by
  refine ⟨lt_of_lt_of_le ?_ (half_le_Uc h), lt_of_lt_of_le ?_ (five_eighths_le_Vc h)⟩
  · exact half_gt_eta
  · exact five_eighths_gt_half_add_eta

/-! ## 4. The two Appendix-A normalised exponents at `r = 10` -/

/-- First normalised Appendix-A term, `1/(4r) − V/(2r)` with `V = 5/8`. -/
def firstTerm (r : ℚ) (V : ℚ) : ℚ := 1 / (4 * r) - V / (2 * r)

/-- Second normalised Appendix-A term, `1/(2r) − V/(2r) − U/2` with
`V = 5/8`, `U = 1/2`. -/
def secondTerm (r : ℚ) (U V : ℚ) : ℚ := 1 / (2 * r) - V / (2 * r) - U / 2

/-- `1/40 − (5/8)/20 = −1/160`. -/
theorem firstTerm_r10 : firstTerm 10 (5 / 8) = -(1 / 160) := by
  norm_num [firstTerm]

/-- `1/20 − (5/8)/20 − (1/2)/2 = −37/160`. -/
theorem secondTerm_r10 : secondTerm 10 (1 / 2) (5 / 8) = -(37 / 160) := by
  norm_num [secondTerm]

/-- **`karatsuba_r10_uniform_exponent_margin`.**  At `r = 10`, with the window
values `U = 1/2`, `V = 5/8`, the two normalised Appendix-A exponents are
`−1/160` and `−37/160`; the weaker (smaller) numerical saving is therefore
`1/160`, and it is strictly positive. -/
theorem karatsuba_r10_uniform_exponent_margin :
    firstTerm 10 (5 / 8) = -(1 / 160) ∧
      secondTerm 10 (1 / 2) (5 / 8) = -(37 / 160) ∧
      min (-firstTerm 10 (5 / 8)) (-secondTerm 10 (1 / 2) (5 / 8)) = 1 / 160 ∧
      (0 : ℚ) < 1 / 160 := by
  refine ⟨firstTerm_r10, secondTerm_r10, ?_, by norm_num⟩
  rw [firstTerm_r10, secondTerm_r10]
  norm_num

/-! ## 5. Guard -/

/-- **Guard.**  Nothing above is an analytic theorem.  The inequalities are
rational and, in particular, hold for exponent values that carry no analytic
meaning; no bilinear character-sum bound is proved, assumed, or axiomatised in
this bank. -/
theorem karatsuba_ledger_is_purely_rational :
    firstTerm 10 (5 / 8) = -(1 / 160) ∧ firstTerm 10 0 = 1 / 40 := by
  refine ⟨firstTerm_r10, by norm_num [firstTerm]⟩

end Karatsuba
end Gate1BDet2
end TwinPrimeProject
