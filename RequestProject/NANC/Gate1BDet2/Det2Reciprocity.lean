import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 31: reciprocity for the determinant phase

This module banks, **exactly**, the reciprocity algebra behind

  `e_q (2 h u⁻¹) = e_u (-2 h q⁻¹) · e (2 h / (u q))`,   `(u, q) = 1`.

Two layers are banked:

* the **integer congruence layer** (`reciprocity_dvd`): for any inverses
  `u ū ≡ 1 (mod q)` and `q q̄ ≡ 1 (mod u)` of coprime `u, q`,

    `u q ∣ u ū + q q̄ - 1`,

  which is exactly the statement that `ū/q + q̄/u - 1/(u q)` is an integer;

* the **analytic translation** (`det2_reciprocity_phase`), stated with the
  additive phase `e(x) = exp (2 π i x)` on `ℝ`, in which the above divisibility
  is turned into the multiplicative identity above.

Also banked is the sign-correct companion `phase_det2_split`, i.e. the
factorisation `e_q (h v + 2 h ū) = e_q(h v) · e_q(2 h ū)` in the same
convention.

**No range, saving, or cancellation claim is made anywhere in this module.**
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Recip

open Complex

/-! ## 1. The integer congruence layer -/

/-- **Reciprocity divisibility.**  If `u` and `q` are coprime and `ū`, `q̄` are
inverses of `u` mod `q` and of `q` mod `u`, then `u q ∣ u ū + q q̄ - 1`.

Equivalently: `ū/q + q̄/u - 1/(u q) ∈ ℤ`.  This is the exact rational identity
underlying Kloosterman-fraction reciprocity. -/
theorem reciprocity_dvd {u q ubar qbar : ℤ} (hcop : IsCoprime u q)
    (hu : u * ubar ≡ 1 [ZMOD q]) (hq : q * qbar ≡ 1 [ZMOD u]) :
    u * q ∣ u * ubar + q * qbar - 1 := by
  refine hcop.mul_dvd ?_ ?_
  · obtain ⟨c, hc⟩ : u ∣ (q * qbar - 1) := Int.ModEq.dvd hq.symm
    exact ⟨ubar + c, by linarith [hc]⟩
  · obtain ⟨c, hc⟩ : q ∣ (u * ubar - 1) := Int.ModEq.dvd hu.symm
    exact ⟨qbar + c, by linarith [hc]⟩

/-- The witnessed form of `reciprocity_dvd`: there is an integer `k` with
`u ū + q q̄ - 1 = u q k`. -/
theorem reciprocity_witness {u q ubar qbar : ℤ} (hcop : IsCoprime u q)
    (hu : u * ubar ≡ 1 [ZMOD q]) (hq : q * qbar ≡ 1 [ZMOD u]) :
    ∃ k : ℤ, u * ubar + q * qbar - 1 = u * q * k :=
  reciprocity_dvd hcop hu hq

/-! ## 2. The additive phase on `ℝ` -/

/-- `e (x) = exp (2 π i x)`. -/
noncomputable def phase (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- `e` is `1`-periodic: integer shifts of the argument are invisible. -/
theorem phase_int_add (x : ℝ) (n : ℤ) : phase (x + (n : ℝ)) = phase x := by
  rw [phase_add]
  have : phase (n : ℝ) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I n
    simpa [phase, mul_comm, mul_left_comm, mul_assoc] using this
  rw [this, mul_one]

/-- **Sign-correct companion.**  The determinant phase factors as
`e(h v / q + 2 h ū / q) = e(h v / q) · e(2 h ū / q)`. -/
theorem phase_det2_split (a b : ℝ) : phase (a + b) = phase a * phase b := phase_add a b

/-! ## 3. Analytic translation: the reciprocity identity -/

/-- **Kloosterman-fraction reciprocity for the determinant-2 phase.**

For coprime nonzero integers `u, q` with inverses `ū` (mod `q`) and `q̄`
(mod `u`), and any integer `h`,

  `e(2 h ū / q) = e(-2 h q̄ / u) · e(2 h / (u q))`.

The proof is purely the integer divisibility `reciprocity_dvd` plus
`1`-periodicity of `e`; **no analytic estimate is involved.** -/
theorem det2_reciprocity_phase {u q ubar qbar : ℤ} (hcop : IsCoprime u q)
    (hu0 : u ≠ 0) (hq0 : q ≠ 0)
    (hu : u * ubar ≡ 1 [ZMOD q]) (hq : q * qbar ≡ 1 [ZMOD u]) (h : ℤ) :
    phase ((2 * h * ubar : ℝ) / (q : ℝ))
      = phase (-(2 * h * qbar : ℝ) / (u : ℝ)) * phase ((2 * h : ℝ) / ((u : ℝ) * (q : ℝ))) := by
  obtain ⟨k, hk⟩ := reciprocity_witness hcop hu hq
  have hu0' : (u : ℝ) ≠ 0 := Int.cast_ne_zero.2 hu0
  have hq0' : (q : ℝ) ≠ 0 := Int.cast_ne_zero.2 hq0
  have hkR : (u : ℝ) * (ubar : ℝ) + (q : ℝ) * (qbar : ℝ) - 1 = (u : ℝ) * (q : ℝ) * (k : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hk
  have hsplit :
      (2 * (h : ℝ) * (ubar : ℝ)) / (q : ℝ)
        = (-(2 * (h : ℝ) * (qbar : ℝ)) / (u : ℝ)
            + (2 * (h : ℝ)) / ((u : ℝ) * (q : ℝ))) + ((2 * h * k : ℤ) : ℝ) := by
    push_cast
    field_simp
    linear_combination (h : ℝ) * hkR
  calc phase ((2 * (h:ℝ) * (ubar:ℝ)) / (q:ℝ))
      = phase ((-(2 * (h:ℝ) * (qbar:ℝ)) / (u:ℝ) + (2 * (h:ℝ)) / ((u:ℝ) * (q:ℝ)))
          + ((2 * h * k : ℤ) : ℝ)) := by rw [← hsplit]
    _ = phase (-(2 * (h:ℝ) * (qbar:ℝ)) / (u:ℝ) + (2 * (h:ℝ)) / ((u:ℝ) * (q:ℝ))) :=
        phase_int_add _ _
    _ = phase (-(2 * (h:ℝ) * (qbar:ℝ)) / (u:ℝ)) * phase ((2 * (h:ℝ)) / ((u:ℝ) * (q:ℝ))) :=
        phase_add _ _

end Recip
end Gate1BDet2
end TwinPrimeProject
