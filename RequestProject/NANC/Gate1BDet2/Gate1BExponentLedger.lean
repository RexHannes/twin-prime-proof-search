import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 6: the rational exponent ledger

Only rational exponent algebra is banked here.  Nothing about `X^r` asymptotics
is asserted as an equality of sizes: these are identities in `ℚ` between the
exponent labels

  `Uexp = 4/9`,  `Vexp = 5/9`,  `Qexp = ω`,  `Rexp = 1 − ω`,

together with the endpoint computation `ω − 4/9 = 5/18` at `ω = 13/18`, which is
the exponent of the affine-line parameter length `H = Q / U` (Module 4).

The exponents `4/9`, `5/9`, `13/18` agree with the ones already banked in
`RequestProject.NANC.HFMVGate1B.HFMVExponentLedger`; the content added here is
the symbolic `ω` layer and the `H = Q/U` endpoint exponent.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. Numeric ledger -/

/-- `U = X^(4/9)`. -/
def Uexp : ℚ := 4 / 9

/-- `V = X^(5/9)`. -/
def Vexp : ℚ := 5 / 9

theorem four_ninths_add_five_ninths : (4 : ℚ) / 9 + 5 / 9 = 1 := by norm_num

/-- `U V = X`. -/
theorem Uexp_add_Vexp : Uexp + Vexp = 1 := by norm_num [Uexp, Vexp]

/-! ## 2. Symbolic ledger -/

/-- `Q = X^ω`, with `ω` symbolic. -/
def Qexp (omega : ℚ) : ℚ := omega

/-- `R = X^(1−ω)`, the complementary exponent. -/
def Rexp (omega : ℚ) : ℚ := 1 - omega

theorem omega_add_one_sub_omega (omega : ℚ) : omega + (1 - omega) = 1 := by ring

/-- `Q R = X`. -/
theorem Qexp_add_Rexp (omega : ℚ) : Qexp omega + Rexp omega = 1 := by
  simp [Qexp, Rexp]

/-! ## 3. The first hard endpoint `ω = 13/18` -/

/-- The first hard endpoint. -/
def omegaHard : ℚ := 13 / 18

/-- **Affine-parameter length exponent.**  At the first hard endpoint,
`H = Q / U` has exponent `ω − 4/9 = 5/18`. -/
theorem omegaHard_sub_Uexp : omegaHard - Uexp = 5 / 18 := by
  norm_num [omegaHard, Uexp]

/-- The same computation stated for the ledger labels. -/
theorem Qexp_sub_Uexp_at_hard : Qexp omegaHard - Uexp = 5 / 18 := by
  simp [Qexp, omegaHard_sub_Uexp]

/-- The hard endpoint lies strictly between `1/2` and `1`. -/
theorem omegaHard_bounds : (1 : ℚ) / 2 < omegaHard ∧ omegaHard < 1 := by
  constructor <;> norm_num [omegaHard]

/-- The complementary exponent at the hard endpoint. -/
theorem Rexp_at_hard : Rexp omegaHard = 5 / 18 := by norm_num [Rexp, omegaHard]

/-! ## 4. Guard -/

/-- **Guard.**  The ledger is pure rational arithmetic and carries no analytic
content: the identities hold for every value of the symbolic exponent, including
the degenerate ones. -/
theorem ledger_is_purely_rational (omega : ℚ) :
    Qexp omega + Rexp omega = 1 ∧ Qexp 0 + Rexp 0 = 1 :=
  ⟨Qexp_add_Rexp omega, Qexp_add_Rexp 0⟩

end Gate1BDet2
end TwinPrimeProject
