import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 30: the additive reciprocal frame

This module banks the **exact finite additive Fourier representation** of the
determinant congruence

  `u v ≡ -2 (mod q)`      (`u` a unit mod `q`),

namely

  `1_{u v = -2}  =  q⁻¹ ∑_{h mod q} e_q (h v + 2 h u⁻¹)`.

Everything is finite: the ambient group is `ZMod q` and the phase is the
standard additive character `ZMod.stdAddChar`.  The orthogonality relation is
proved here (from primitivity of `stdAddChar`), and the `h = 0` term is
separated from the `h ≠ 0` terms.

**No analytic asymptotics are hard-coded, and the `h = 0` mode is deliberately
NOT identified with the source expected term `E(q)`**: the guard
`additive_zero_mode_does_not_identify_source_expected_term` records that the
zero mode is the *same constant* `q⁻¹` for every admissible `(u, v)`, hence
carries no information about the source term, and
`zero_mode_ne_indicator` exhibits a pair where the zero mode and the indicator
genuinely differ.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Recip

open Finset

/-! ## 1. The finite additive phase `e_q` -/

/-- The standard additive phase `e_q (x) = exp (2 π i x / q)`, as a function on
`ZMod q`. -/
noncomputable def addPhase (q : ℕ) [NeZero q] (x : ZMod q) : ℂ := ZMod.stdAddChar x

variable {q : ℕ} [NeZero q]

@[simp] theorem addPhase_zero : addPhase q 0 = 1 := AddChar.map_zero_eq_one _

theorem addPhase_add (x y : ZMod q) :
    addPhase q (x + y) = addPhase q x * addPhase q y :=
  AddChar.map_add_eq_mul _ _ _

/-- The sign-correct splitting of the determinant phase:
`e_q (h v + 2 h u⁻¹) = e_q (h v) · e_q (2 h u⁻¹)`. -/
theorem addPhase_det2_split (h v w : ZMod q) :
    addPhase q (h * v + 2 * h * w) = addPhase q (h * v) * addPhase q (2 * h * w) :=
  addPhase_add _ _

/-! ## 2. Finite additive orthogonality -/

/-- **Additive orthogonality on `ZMod q`.**  `∑_{h} e_q (h t) = q` if `t = 0`
and `0` otherwise.  Proved from primitivity of the standard additive character;
no analytic input. -/
theorem sum_addPhase_mul (t : ZMod q) :
    ∑ h : ZMod q, addPhase q (h * t) = if t = 0 then (q : ℂ) else 0 := by
  classical
  split_ifs with ht
  · simp [addPhase, ht, ZMod.card q]
  · have : ∑ h : ZMod q, addPhase q (t * h) = 0 :=
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)
    simpa [mul_comm] using this

/-! ## 3. The exact indicator identity -/

/-- **Unit-sector determinant congruence, additively resolved.**  For `u` a unit
modulo `q`,

  `1_{u v = -2} = q⁻¹ ∑_{h mod q} e_q (h v + 2 h u⁻¹)`.

This is an exact finite identity in `ℂ`. -/
theorem det2_additive_frame {u : ZMod q} (hu : IsUnit u) (v : ZMod q) :
    (if u * v = -2 then (1 : ℂ) else 0)
      = (q : ℂ)⁻¹ * ∑ h : ZMod q, addPhase q (h * v + 2 * h * u⁻¹) := by
  have hqne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have hrw : ∀ h : ZMod q, h * v + 2 * h * u⁻¹ = h * (v + 2 * u⁻¹) := by
    intro h; ring
  have hkey : (u * v = -2) ↔ (v + 2 * u⁻¹ = 0) := by
    constructor
    · intro hv
      have h1 : u⁻¹ * (u * v) = u⁻¹ * (-2) := by rw [hv]
      rw [← mul_assoc, ZMod.inv_mul_of_unit u hu, one_mul] at h1
      rw [h1]; ring
    · intro hv
      have hv' : v = -(2 * u⁻¹) := by linear_combination hv
      rw [hv']
      have : u * (2 * u⁻¹) = 2 := by
        rw [show u * (2 * u⁻¹) = 2 * (u * u⁻¹) by ring, ZMod.mul_inv_of_unit u hu, mul_one]
      rw [mul_neg, this]
  simp only [hrw]
  rw [sum_addPhase_mul]
  by_cases hv : u * v = -2
  · rw [if_pos hv, if_pos (hkey.1 hv)]
    field_simp
  · rw [if_neg hv, if_neg (fun hc => hv (hkey.2 hc))]
    simp

/-! ## 4. Separation of the `h = 0` mode -/

/-- The `h = 0` term of the additive frame is the constant Fourier coefficient
`1`. -/
theorem addPhase_zero_mode (v w : ZMod q) :
    addPhase q ((0 : ZMod q) * v + 2 * (0 : ZMod q) * w) = 1 := by
  simp

/-- **Zero-mode separation.**  The additive frame splits as the constant
coefficient plus the nonzero frequencies. -/
theorem sum_addPhase_split (v w : ZMod q) :
    ∑ h : ZMod q, addPhase q (h * v + 2 * h * w)
      = 1 + ∑ h ∈ (univ.erase (0 : ZMod q)), addPhase q (h * v + 2 * h * w) := by
  classical
  rw [← Finset.add_sum_erase univ _ (mem_univ (0 : ZMod q)), addPhase_zero_mode]

/-! ## 5. Guards: the zero mode is not the source expected term -/

/-- The zero-mode contribution to the frame. -/
noncomputable def zeroModeTerm (q : ℕ) [NeZero q] (v w : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * addPhase q ((0 : ZMod q) * v + 2 * (0 : ZMod q) * w)

@[simp] theorem zeroModeTerm_eq (v w : ZMod q) : zeroModeTerm q v w = (q : ℂ)⁻¹ := by
  simp [zeroModeTerm]

/-- **GUARD.**  The additive zero mode is the *same* constant `q⁻¹` for every
`(u, v)`; it therefore cannot identify the source expected term, which depends
on the arithmetic data.  (Formally: the zero mode is a constant function of the
determinant data.) -/
theorem additive_zero_mode_does_not_identify_source_expected_term
    (v w v' w' : ZMod q) : zeroModeTerm q v w = zeroModeTerm q v' w' := by
  simp

/-- **GUARD (concrete separation).**  The zero mode does not even agree with the
indicator it is a mode of: for `q = 5`, `u = 1`, `v = 0` the congruence fails
(indicator `0`) while the zero-mode term is `1/5 ≠ 0`. -/
theorem zero_mode_ne_indicator :
    (if (1 : ZMod 5) * (0 : ZMod 5) = -2 then (1 : ℂ) else 0)
      ≠ zeroModeTerm 5 (0 : ZMod 5) (0 : ZMod 5) := by
  have h : ((1 : ZMod 5) * (0 : ZMod 5) = -2) ↔ False := by decide
  rw [if_neg (by simpa using h.mp), zeroModeTerm_eq]
  norm_num

end Recip
end Gate1BDet2
end TwinPrimeProject
