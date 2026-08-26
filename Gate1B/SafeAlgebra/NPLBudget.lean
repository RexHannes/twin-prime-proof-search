/-
# Gate 1B — exponent / no-wrap rational ledger

Exact rational exponent arithmetic ONLY.

NO Parseval theorem, NO Möbius estimate, NO Gate closure is inferred from this file.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- `u = 4/9`, the `U`-exponent. -/
def uExp : ℚ := 4 / 9

/-- `v = 5/9`, the `V`-exponent. -/
def vExp : ℚ := 5 / 9

/-- The residual exponent `r = 1 − ω`. -/
def rExp (omega : ℚ) : ℚ := 1 - omega

theorem u_add_v : uExp + vExp = 1 := by unfold uExp vExp; norm_num

theorem omega_add_r (omega : ℚ) : omega + rExp omega = 1 := by unfold rExp; ring

theorem v_gt_u : uExp < vExp := by unfold uExp vExp; norm_num

/-- **Near-primitive no-wrap exponent condition.**  For `ω ≥ 13/18` and `0 < η < 1/6`,
the exponent of `g ≥ Q X^{-η}` strictly exceeds the `V`-exponent `v = 5/9`.

The hypothesis `0 < η` is kept because it is part of the requested statement; the
inequality already follows from `η < 1/6` and `ω ≥ 13/18`. -/
theorem nearPrimitiveNoWrapExponent (omega eta : ℚ) (homega : 13 / 18 ≤ omega)
    (heta0 : 0 < eta) (heta : eta < 1 / 6) : vExp < omega - eta := by
  unfold vExp; linarith

/-- Diagonal exponent identity `(u + v + ω)/2 = (1 + ω)/2 = 1 − r/2`. -/
theorem diagonal_exponent_identity (omega : ℚ) :
    (uExp + vExp + omega) / 2 = (1 + omega) / 2 ∧ (1 + omega) / 2 = 1 - rExp omega / 2 := by
  constructor
  · unfold uExp vExp; ring
  · unfold rExp; ring

/-- `ω ≤ 8/9` forces `r ≥ 1/9`. -/
theorem gate1B_R_exponent_lower (omega : ℚ) (h : omega ≤ 8 / 9) : 1 / 9 ≤ rExp omega := by
  unfold rExp; linarith

/-- **Diagonal saving floor.**  `ω ≤ 8/9` gives `r/2 ≥ 1/18`. -/
theorem npl_diagonal_saving_floor (omega : ℚ) (h : omega ≤ 8 / 9) :
    1 / 18 ≤ rExp omega / 2 := by
  unfold rExp; linarith

/-- Alias with the name requested in the exponent ledger. -/
theorem gate1B_diagSavingExponent (omega : ℚ) (h : omega ≤ 8 / 9) :
    1 / 18 ≤ rExp omega / 2 := npl_diagonal_saving_floor omega h

/-- Endpoint value: at `ω = 8/9` the diagonal saving exponent is exactly `1/18`. -/
theorem npl_diagonal_saving_endpoint : rExp (8 / 9) / 2 = 1 / 18 := by
  unfold rExp; norm_num

/-! ## Budget identity -/

/-- `U V = X` and `Q R = X` with `Q > 0` give `X / Q = R`.

The hypothesis `U V = X` is kept because it is part of the requested normalisation; only
`Q R = X` and `Q > 0` are used. -/
theorem X_div_Q_eq_R (U V Q R X : ℝ) (hQ : 0 < Q) (hUV : U * V = X) (hQR : Q * R = X) :
    X / Q = R := by
  rw [← hQR]
  field_simp

/-- The allowed congestion of the Gate-1B normalisation is `R`: IF the natural energy is
`B₂C₂` and the allowed energy is `R B₂ C₂`, the admissible congestion ratio is exactly `R`.
This does NOT assert that the actual congestion is at most `R`. -/
theorem npl_allowedCongestion (B2 C2 R : ℝ) (hB : 0 < B2) (hC : 0 < C2) :
    (R * B2 * C2) / (B2 * C2) = R := by
  field_simp

end Gate1B.SafeAlgebra
