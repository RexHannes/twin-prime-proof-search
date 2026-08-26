import Mathlib

namespace TwinPrimeProject.NANC.D4

/-- Exponent of the main edge modulus. -/
def M_exp : ℚ := 1 / 3
/-- Exponent of `R`. -/
def R_exp (a : ℚ) : ℚ := a
/-- Exponent of `L`. -/
def L_exp (b : ℚ) : ℚ := b
/-- Exponent of `H`. -/
def H_exp (a b : ℚ) : ℚ := a + 2 * b - 2 / 3
/-- Exponent of `D`. -/
def D_exp (a : ℚ) : ℚ := 2 / 3 - a
/-- Exponent of `K`. -/
def K_exp (a : ℚ) : ℚ := 1 / 3 - a

/-- The closed high-`b` parameter region. -/
def HighBRegion (a b : ℚ) : Prop :=
  5 / 18 ≤ a ∧ 1 / 3 ≤ b ∧ a + b ≤ 5 / 8

theorem exp_D_add_H_eq_twoL (a b : ℚ) :
    D_exp a + H_exp a b = 2 * b := by
  unfold D_exp H_exp
  ring

theorem exp_M_add_K_eq_D (a : ℚ) :
    M_exp + K_exp a = D_exp a := by
  simp [M_exp, K_exp, D_exp]
  ring

theorem exp_H_lt_L {a b : ℚ} (h : HighBRegion a b) : H_exp a b < b := by
  rcases h with ⟨_, hb, hab⟩
  simp [H_exp]
  linarith

theorem exp_K_lt_one_ninth {a b : ℚ} (h : HighBRegion a b) :
    K_exp a < 1 / 9 := by
  rcases h with ⟨ha, _, _⟩
  simp [K_exp]
  linarith

theorem exp_R_lt_M {a b : ℚ} (h : HighBRegion a b) : a < 1 / 3 := by
  rcases h with ⟨_, hb, hab⟩
  linarith

theorem exp_D_lt_L2M {a b : ℚ} (h : HighBRegion a b) :
    D_exp a < 2 * b + 1 / 3 := by
  rcases h with ⟨ha, hb, _⟩
  simp [D_exp]
  linarith

theorem exp_archimedean_correction (a b : ℚ) :
    H_exp a b + K_exp a - 2 * b - 2 / 3 = -1 := by
  simp [H_exp, K_exp]
  ring

/-- Exponent of the hoped-for CRG gain after paying the `m`-edge `K` loss. -/
def crgNetExp (a b : ℚ) : ℚ := (1 - a - 2 * b) - (1 / 3 - a)

theorem exp_crg_net_nonpositive {a b : ℚ} (h : HighBRegion a b) :
    crgNetExp a b ≤ 0 := by
  rcases h with ⟨_, hb, _⟩
  simp [crgNetExp]
  linarith

theorem exp_crg_net_V1_eq_zero : crgNetExp (5 / 18) (1 / 3) = 0 := by
  norm_num [crgNetExp]

theorem exp_crg_net_V2_eq_neg_one_thirtysix :
    crgNetExp (5 / 18) (25 / 72) = -1 / 36 := by
  norm_num [crgNetExp]

theorem exp_crg_net_V3_eq_zero : crgNetExp (7 / 24) (1 / 3) = 0 := by
  norm_num [crgNetExp]

/-- The requested formal `m`-saving is the fixed exponent `1/6`. -/
def formalMSaving : ℚ := 1 / 6

theorem vertex_V1_audit :
    H_exp (5 / 18) (1 / 3) - M_exp / 2 = 1 / 9 ∧
    formalMSaving = 1 / 6 ∧ K_exp (5 / 18) = 1 / 18 := by
  norm_num [H_exp, M_exp, formalMSaving, K_exp]

theorem vertex_V2_audit :
    H_exp (5 / 18) (25 / 72) - M_exp / 2 = 5 / 36 ∧
    formalMSaving = 1 / 6 ∧ K_exp (5 / 18) = 1 / 18 := by
  norm_num [H_exp, M_exp, formalMSaving, K_exp]

theorem vertex_V3_audit :
    H_exp (7 / 24) (1 / 3) - M_exp / 2 = 1 / 8 ∧
    formalMSaving = 1 / 6 ∧ K_exp (7 / 24) = 1 / 24 := by
  norm_num [H_exp, M_exp, formalMSaving, K_exp]

end TwinPrimeProject.NANC.D4
