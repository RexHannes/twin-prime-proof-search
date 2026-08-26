/-
# Gate-1A frozen scale ledger (Section 2)

All asymptotic parameters are represented purely by their exponents in the
scale `X`.  Nothing here pretends that `X ^ a` is an exact natural number;
every statement is an ordinary rational-arithmetic theorem about exponents.

Dictionary:

```
M = X ^ (1/3)              mExp        = 1/3
R = X ^ a                  a
L = X ^ b                  b
H = X ^ (a + 2b - 2/3)     hExp a b
K = X ^ (1/3 - a)          kExp a
D = X ^ (2/3 - a)          dExp a         (defined by  D * H = L^2)
```
-/
import Mathlib

namespace Gate1A

/-! ## Exponent definitions -/

/-- Exponent of `M = X^(1/3)`. -/
def mExp : ℚ := 1 / 3

/-- Exponent of `H = X^(a + 2b - 2/3)`. -/
def hExp (a b : ℚ) : ℚ := a + 2 * b - 2 / 3

/-- Exponent of `K = X^(1/3 - a)`. -/
def kExp (a : ℚ) : ℚ := 1 / 3 - a

/-- Exponent of `D`, the companion length fixed by `D * H = L^2`. -/
def dExp (a : ℚ) : ℚ := 2 / 3 - a

/-- Exponent of the required variance saving `H / M = X^(a + 2b - 1)`. -/
def reqExp (a b : ℚ) : ℚ := a + 2 * b - 1

/-- Exponent of `U⁻¹ = X^(-(a + b - 2/3))`; `U = H/q`-type inverse scale. -/
def uInvExp (a b : ℚ) : ℚ := a + b - 2 / 3

/-- Exponent of the TRUE recombination amplitude error `ε = U^(-2)`. -/
def epsExp (a b : ℚ) : ℚ := 2 * a + 2 * b - 4 / 3

/-- Exponent of the projective energy ratio `M K / H^2 = L^2 / H^3`. -/
def projExp (a b : ℚ) : ℚ := 2 - 3 * a - 4 * b

/-- The Gate-1A polytope. -/
structure Polytope (a b : ℚ) : Prop where
  ha : 5 / 18 ≤ a
  hb : 1 / 3 ≤ b
  hab : a + b ≤ 5 / 8

/-! ## Controlling vertices -/

/-- `V1 = (5/18, 1/3)`. -/
def V1 : ℚ × ℚ := (5 / 18, 1 / 3)
/-- `V2 = (5/18, 25/72)`. -/
def V2 : ℚ × ℚ := (5 / 18, 25 / 72)
/-- `V3 = (7/24, 1/3)`. -/
def V3 : ℚ × ℚ := (7 / 24, 1 / 3)

theorem V1_mem : Polytope V1.1 V1.2 := ⟨by norm_num [V1], by norm_num [V1], by norm_num [V1]⟩
theorem V2_mem : Polytope V2.1 V2.2 := ⟨by norm_num [V2], by norm_num [V2], by norm_num [V2]⟩
theorem V3_mem : Polytope V3.1 V3.2 := ⟨by norm_num [V3], by norm_num [V3], by norm_num [V3]⟩

/-! ## Exact exponent identities

`D H = L^2`, `R K = M`, `M^2 H = R L^2`.
-/

theorem gate1a_DH_eq_Lsq (a b : ℚ) : dExp a + hExp a b = 2 * b := by
  simp only [dExp, hExp]; ring

theorem gate1a_RK_eq_M (a : ℚ) : a + kExp a = mExp := by
  simp only [kExp, mExp]; ring

theorem gate1a_MsqH_eq_RLsq (a b : ℚ) : 2 * mExp + hExp a b = a + 2 * b := by
  simp only [mExp, hExp]; ring

/-- `H / M` has exponent exactly the required saving `reqExp`. -/
theorem gate1a_H_over_M (a b : ℚ) : hExp a b - mExp = reqExp a b := by
  simp only [hExp, mExp, reqExp]; ring

/-- The recombination-error exponent is exactly twice the `U⁻¹` exponent. -/
theorem gate1a_eps_eq_two_uInv (a b : ℚ) : epsExp a b = 2 * uInvExp a b := by
  simp only [epsExp, uInvExp]; ring

/-- The projective ratio `M K / H^2` equals `L^2 / H^3` at the exponent level. -/
theorem gate1a_proj_two_forms (a b : ℚ) :
    mExp + kExp a - 2 * hExp a b = projExp a b ∧
      2 * b - 3 * hExp a b = projExp a b := by
  constructor <;> · simp only [mExp, kExp, hExp, projExp]; ring

/-! ## A. Outer-root capacity -/

/-- Over the polytope, `-a/2 ≤ a + 2b - 1`, i.e. `(3/2) a + 2 b ≥ 1`. -/
theorem gate1a_outer_capacity {a b : ℚ} (h : Polytope a b) :
    -a / 2 ≤ reqExp a b := by
  obtain ⟨ha, hb, _⟩ := h
  simp only [reqExp]
  linarith

theorem gate1a_outer_capacity' {a b : ℚ} (h : Polytope a b) :
    1 ≤ (3 / 2) * a + 2 * b := by
  obtain ⟨ha, hb, _⟩ := h; linarith

/-! ## B. p/q-face capacity -/

/-- Over the polytope, `-b/2 ≤ a + 2b - 1`, i.e. `a + (5/2) b ≥ 1`. -/
theorem gate1a_face_capacity {a b : ℚ} (h : Polytope a b) :
    -b / 2 ≤ reqExp a b := by
  obtain ⟨ha, hb, _⟩ := h
  simp only [reqExp]
  linarith

theorem gate1a_face_capacity' {a b : ℚ} (h : Polytope a b) :
    1 ≤ a + (5 / 2) * b := by
  obtain ⟨ha, hb, _⟩ := h; linarith

/-! ## C. True recombination-error comparison -/

/-- The true amplitude error `ε = U^{-2}` beats `sqrt(H/M)` on the whole polytope:
`epsExp ≤ reqExp / 2`. -/
theorem gate1a_u2_error_capacity {a b : ℚ} (h : Polytope a b) :
    epsExp a b ≤ reqExp a b / 2 := by
  obtain ⟨_, hb, hab⟩ := h
  simp only [epsExp, reqExp]
  linarith

/-- Exact vertex margin at `V1`. -/
theorem gate1a_u2_margin_v1 :
    reqExp V1.1 V1.2 / 2 - epsExp V1.1 V1.2 = 1 / 12 := by
  norm_num [reqExp, epsExp, V1]

/-- Exact vertex margin at `V2`. -/
theorem gate1a_u2_margin_v2 :
    reqExp V2.1 V2.2 / 2 - epsExp V2.1 V2.2 = 5 / 72 := by
  norm_num [reqExp, epsExp, V2]

/-- Exact vertex margin at `V3`. -/
theorem gate1a_u2_margin_v3 :
    reqExp V3.1 V3.2 / 2 - epsExp V3.1 V3.2 = 1 / 16 := by
  norm_num [reqExp, epsExp, V3]

/-! ## D. Outer `R^{-1/2}` versus `H/M` margins -/

theorem gate1a_outer_margin_v1 : reqExp V1.1 V1.2 - (-V1.1 / 2) = 1 / 12 := by
  norm_num [reqExp, V1]

theorem gate1a_outer_margin_v2 : reqExp V2.1 V2.2 - (-V2.1 / 2) = 1 / 9 := by
  norm_num [reqExp, V2]

theorem gate1a_outer_margin_v3 : reqExp V3.1 V3.2 - (-V3.1 / 2) = 5 / 48 := by
  norm_num [reqExp, V3]

/-! ## E. `L^{-1/2}` versus `H/M` margins -/

theorem gate1a_face_margin_v1 : reqExp V1.1 V1.2 - (-V1.2 / 2) = 1 / 9 := by
  norm_num [reqExp, V1]

theorem gate1a_face_margin_v2 : reqExp V2.1 V2.2 - (-V2.2 / 2) = 7 / 48 := by
  norm_num [reqExp, V2]

theorem gate1a_face_margin_v3 : reqExp V3.1 V3.2 - (-V3.2 / 2) = 1 / 8 := by
  norm_num [reqExp, V3]

/-! ## F. Projective energy ratio at the vertices -/

theorem gate1a_projective_exp_v1 : projExp V1.1 V1.2 = -(1 / 6) := by
  norm_num [projExp, V1]

theorem gate1a_projective_exp_v2 : projExp V2.1 V2.2 = -(2 / 9) := by
  norm_num [projExp, V2]

theorem gate1a_projective_exp_v3 : projExp V3.1 V3.2 = -(5 / 24) := by
  norm_num [projExp, V3]

/-- The projective ratio is negative (a genuine saving) throughout the polytope. -/
theorem gate1a_projective_exp_neg {a b : ℚ} (h : Polytope a b) : projExp a b < 0 := by
  obtain ⟨ha, hb, _⟩ := h
  simp only [projExp]
  linarith

/-- The required saving exponent is negative throughout the polytope: `H/M < 1`. -/
theorem gate1a_reqExp_neg {a b : ℚ} (h : Polytope a b) : reqExp a b < 0 := by
  obtain ⟨ha, _, hab⟩ := h
  simp only [reqExp]
  -- b ≤ 5/8 - a ≤ 5/8 - 5/18, so a + 2b - 1 ≤ (a+b) + b - 1 < 0
  linarith

/-- The polytope is nonempty. -/
theorem gate1a_polytope_nonempty : ∃ a b : ℚ, Polytope a b := ⟨V1.1, V1.2, V1_mem⟩

end Gate1A
