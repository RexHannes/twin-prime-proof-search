/-
# Gate04Root.ExponentLedger

Exact rational exponent arithmetic for the parameter dictionary

  `M = X^{1/3}`, `R = X^a`, `L = X^b`,
  `H = X^{a + 2b - 2/3}`, `D = X^{2/3 - a}`, `K = X^{1/3 - a}`,

with the structural identities `D H = L²` and `R K = M` at the level of
exponents, and the four ledger ratios evaluated at the three vertices

  `V₁ = (5/18, 1/3)`, `V₂ = (5/18, 25/72)`, `V₃ = (7/24, 1/3)`.

Only exact `ℚ` values are formalised; no `X^{o(1)}` bookkeeping is attempted.
-/
import Mathlib

namespace Gate04Root.Exponents

/-- Exponent of `M`. -/
def expM : ℚ := 1 / 3

/-- Exponent of `R`. -/
def expR (a : ℚ) : ℚ := a

/-- Exponent of `L`. -/
def expL (b : ℚ) : ℚ := b

/-- Exponent of `H`. -/
def expH (a b : ℚ) : ℚ := a + 2 * b - 2 / 3

/-- Exponent of `D`. -/
def expD (a : ℚ) : ℚ := 2 / 3 - a

/-- Exponent of `K`. -/
def expK (a : ℚ) : ℚ := 1 / 3 - a

/-- `D H = L²` at the level of exponents. -/
theorem exp_DH_eq_L_sq (a b : ℚ) : expD a + expH a b = 2 * expL b := by
  unfold expD expH expL; ring

/-- `R K = M` at the level of exponents. -/
theorem exp_RK_eq_M (a : ℚ) : expR a + expK a = expM := by
  unfold expR expK expM; ring

/-- `M D L² = M L⁴ / H` at the level of exponents. -/
theorem exp_MDL2_eq_ML4_div_H (a b : ℚ) :
    expM + expD a + 2 * expL b = expM + 4 * expL b - expH a b := by
  unfold expM expD expL expH; ring

/-- `(M D L)² = M² L⁶ / H²` at the level of exponents. -/
theorem exp_MDL_sq (a b : ℚ) :
    2 * (expM + expD a + expL b) = 2 * expM + 6 * expL b - 2 * expH a b := by
  unfold expM expD expL expH; ring

/-- The R4C diagonal ratio `H^{-2}`. -/
def r4cDiagonalExp (a b : ℚ) : ℚ := -2 * expH a b

/-- The determinant-zero ratio `K / H²`. -/
def deltaZeroExp (a b : ℚ) : ℚ := expK a - 2 * expH a b

/-- The repeated-`p` ratio `M² / (H² L)`, i.e. `X^{2 - 2a - 5b}`. -/
def repeatedPExp (a b : ℚ) : ℚ := 2 * expM - 2 * expH a b - expL b

/-- The required PPD squared saving `(M/H)² = X^{2(1 - a - 2b)}`. -/
def ppdSavingExp (a b : ℚ) : ℚ := 2 * (expM - expH a b)

/-- The repeated-`p` ratio in closed form. -/
theorem repeatedPExp_eq (a b : ℚ) : repeatedPExp a b = 2 - 2 * a - 5 * b := by
  unfold repeatedPExp expM expH expL; ring

/-- The PPD saving in closed form. -/
theorem ppdSavingExp_eq (a b : ℚ) : ppdSavingExp a b = 2 * (1 - a - 2 * b) := by
  unfold ppdSavingExp expM expH; ring

/-- Vertex `V₁ = (5/18, 1/3)`. -/
def V1 : ℚ × ℚ := (5 / 18, 1 / 3)

/-- Vertex `V₂ = (5/18, 25/72)`. -/
def V2 : ℚ × ℚ := (5 / 18, 25 / 72)

/-- Vertex `V₃ = (7/24, 1/3)`. -/
def V3 : ℚ × ℚ := (7 / 24, 1 / 3)

theorem r4cDiagonal_vertex1 : r4cDiagonalExp V1.1 V1.2 = -5 / 9 := by
  norm_num [r4cDiagonalExp, expH, V1]

theorem r4cDiagonal_vertex2 : r4cDiagonalExp V2.1 V2.2 = -11 / 18 := by
  norm_num [r4cDiagonalExp, expH, V2]

theorem r4cDiagonal_vertex3 : r4cDiagonalExp V3.1 V3.2 = -7 / 12 := by
  norm_num [r4cDiagonalExp, expH, V3]

theorem deltaZero_vertex1 : deltaZeroExp V1.1 V1.2 = -1 / 2 := by
  norm_num [deltaZeroExp, expH, expK, V1]

theorem deltaZero_vertex2 : deltaZeroExp V2.1 V2.2 = -5 / 9 := by
  norm_num [deltaZeroExp, expH, expK, V2]

theorem deltaZero_vertex3 : deltaZeroExp V3.1 V3.2 = -13 / 24 := by
  norm_num [deltaZeroExp, expH, expK, V3]

theorem repeatedP_vertex1 : repeatedPExp V1.1 V1.2 = -2 / 9 := by
  norm_num [repeatedPExp_eq, V1]

theorem repeatedP_vertex2 : repeatedPExp V2.1 V2.2 = -7 / 24 := by
  norm_num [repeatedPExp_eq, V2]

theorem repeatedP_vertex3 : repeatedPExp V3.1 V3.2 = -1 / 4 := by
  norm_num [repeatedPExp_eq, V3]

theorem ppdSaving_vertex1 : ppdSavingExp V1.1 V1.2 = 1 / 9 := by
  norm_num [ppdSavingExp_eq, V1]

theorem ppdSaving_vertex2 : ppdSavingExp V2.1 V2.2 = 1 / 18 := by
  norm_num [ppdSavingExp_eq, V2]

theorem ppdSaving_vertex3 : ppdSavingExp V3.1 V3.2 = 1 / 12 := by
  norm_num [ppdSavingExp_eq, V3]

/-- All three vertices have strictly negative R4C diagonal exponent. -/
theorem r4cDiagonal_neg_at_vertices :
    r4cDiagonalExp V1.1 V1.2 < 0 ∧ r4cDiagonalExp V2.1 V2.2 < 0 ∧
      r4cDiagonalExp V3.1 V3.2 < 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [r4cDiagonal_vertex1, r4cDiagonal_vertex2, r4cDiagonal_vertex3] <;> norm_num

end Gate04Root.Exponents
