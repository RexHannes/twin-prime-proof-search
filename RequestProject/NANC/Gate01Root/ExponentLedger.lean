import Gate04Root.ExponentLedger
import RequestProject.NANC.Gate01Root.SourceGConsistency

/-!
# Gate01Root: the exact rational exponent ledger

Parameter dictionary `M = X^{1/3}`, `R = X^a`, `L = X^b`,
`H = X^{a+2b-2/3}`, `D = X^{2/3-a}`, `K = X^{1/3-a}` with `D H = L²`, `R K = M`,
evaluated at the three vertices

`V₁ = (5/18, 1/3)`, `V₂ = (5/18, 25/72)`, `V₃ = (7/24, 1/3)`.

All values are exact rationals.
-/

namespace RouteAFibreFrame
namespace Gate01Root

open Gate04Root.Exponents

/-- `D H = L²` at the level of exponents. -/
theorem exponent_DH_eq_L_sq (a b : ℚ) : expD a + expH a b = 2 * expL b :=
  Gate04Root.Exponents.exp_DH_eq_L_sq a b

/-- `R K = M` at the level of exponents. -/
theorem exponent_RK_eq_M (a : ℚ) : expR a + expK a = expM :=
  Gate04Root.Exponents.exp_RK_eq_M a

theorem r4cDiagonal_vertex1 : r4cDiagonalExp V1.1 V1.2 = -5 / 9 :=
  Gate04Root.Exponents.r4cDiagonal_vertex1

theorem r4cDiagonal_vertex2 : r4cDiagonalExp V2.1 V2.2 = -11 / 18 :=
  Gate04Root.Exponents.r4cDiagonal_vertex2

theorem r4cDiagonal_vertex3 : r4cDiagonalExp V3.1 V3.2 = -7 / 12 :=
  Gate04Root.Exponents.r4cDiagonal_vertex3

theorem deltaZero_vertex1 : deltaZeroExp V1.1 V1.2 = -1 / 2 :=
  Gate04Root.Exponents.deltaZero_vertex1

theorem deltaZero_vertex2 : deltaZeroExp V2.1 V2.2 = -5 / 9 :=
  Gate04Root.Exponents.deltaZero_vertex2

theorem deltaZero_vertex3 : deltaZeroExp V3.1 V3.2 = -13 / 24 :=
  Gate04Root.Exponents.deltaZero_vertex3

theorem repeatedP_vertex1 : repeatedPExp V1.1 V1.2 = -2 / 9 :=
  Gate04Root.Exponents.repeatedP_vertex1

theorem repeatedP_vertex2 : repeatedPExp V2.1 V2.2 = -7 / 24 :=
  Gate04Root.Exponents.repeatedP_vertex2

theorem repeatedP_vertex3 : repeatedPExp V3.1 V3.2 = -1 / 4 :=
  Gate04Root.Exponents.repeatedP_vertex3

theorem ppdSaving_vertex1 : ppdSavingExp V1.1 V1.2 = 1 / 9 :=
  Gate04Root.Exponents.ppdSaving_vertex1

theorem ppdSaving_vertex2 : ppdSavingExp V2.1 V2.2 = 1 / 18 :=
  Gate04Root.Exponents.ppdSaving_vertex2

theorem ppdSaving_vertex3 : ppdSavingExp V3.1 V3.2 = 1 / 12 :=
  Gate04Root.Exponents.ppdSaving_vertex3

/-- The repeated-`p` ratio is `X^{2 - 2a - 5b}`. -/
theorem repeatedPExp_closed_form (a b : ℚ) : repeatedPExp a b = 2 - 2 * a - 5 * b :=
  Gate04Root.Exponents.repeatedPExp_eq a b

/-- The required PPD squared saving is `X^{2(1 - a - 2b)}`. -/
theorem ppdSavingExp_closed_form (a b : ℚ) : ppdSavingExp a b = 2 * (1 - a - 2 * b) :=
  Gate04Root.Exponents.ppdSavingExp_eq a b

end Gate01Root
end RouteAFibreFrame
