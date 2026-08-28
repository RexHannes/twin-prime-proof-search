import Mathlib

/-!
# Shifted determinant-line algebra (high-`k` short-shift bank, Phase A)

Exact algebra for the shifted determinant shell.  Everything here is a ring or
field identity: **no estimate, no analytic input, no source assumption.**

Notation.  On a determinant line one has
```
z_t = z₀ + u·t,      v_t = v₀ + ℓ·t,      ℓ·z₀ - u·v₀ = 2,
```
and the *shifted* determinant with shift `h` is
```
ℓ·z_{t+h} - u·v_t = 2 + u·ℓ·h.
```
Opening `z_{t+h} = d·p` turns this into the `β`-form shell
```
d·p·ℓ - u·v = 2 + u·ℓ·h,
```
which is the shell of the shifted MAM packets.

Banked here:

* `shifted_lineDet2`, `shiftedDeterminant_eq`, `shiftedDeterminant_betaForm`;
* the phase-difference identity `determinantDefect_phase_identity`;
* the two shift-independent congruences `shiftedMAM_mod_u`, `shiftedMAM_mod_ell`
  and the `ZMod` form `shiftedDet_zmod`;
* the divisor-switch and solve forms `shiftedMAM_divisorSwitch`,
  `shiftedMAM_solve_v`, `shiftedMAM_prime_solve`.

**Variable-name firewall.**  Throughout this bank the determinant shift is
called `hSh`, never `r`.  The letter `r` is reserved for the *model* factor of
the `2|2` split `u = m·r`.  These are different objects and must never be
identified.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace ShiftedDet

/-! ## 1. The shifted determinant identity -/

/-- **`shifted_lineDet2`.**  On the determinant line `z_t = z₀ + u t`,
`v_t = v₀ + ℓ t` with `ℓ z₀ - u v₀ = 2`, the shifted determinant is
`ℓ z_{t+hSh} - u v_t = 2 + u ℓ hSh`. -/
theorem shifted_lineDet2 (z0 u v0 ell t hSh : ℤ) (hdet : ell * z0 - u * v0 = 2) :
    ell * (z0 + u * (t + hSh)) - u * (v0 + ell * t) = 2 + u * ell * hSh := by
  linear_combination hdet

/-- The same identity written with the shifted point `z` and the unshifted `v`
supplied abstractly. -/
theorem shiftedDeterminant_eq (z0 u v0 ell t hSh z v : ℤ) (hdet : ell * z0 - u * v0 = 2)
    (hz : z = z0 + u * (t + hSh)) (hv : v = v0 + ell * t) :
    ell * z - u * v = 2 + u * ell * hSh := by
  subst hz; subst hv; linear_combination hdet

/-- **`shiftedDeterminant_betaForm`.**  Opening the shifted point as `z = d·p`
gives the `β`-form shell `d p ℓ - u v = 2 + u ℓ hSh`. -/
theorem shiftedDeterminant_betaForm (z0 u v0 ell t hSh d p v : ℤ)
    (hdet : ell * z0 - u * v0 = 2)
    (hz : d * p = z0 + u * (t + hSh)) (hv : v = v0 + ell * t) :
    d * p * ell - u * v = 2 + u * ell * hSh := by
  have := shiftedDeterminant_eq z0 u v0 ell t hSh (d * p) v hdet hz hv
  linarith [this]

/-! ## 2. The phase-difference identity -/

/-- **`determinantDefect_phase_identity`.**  Over a field, the difference of the
two natural line parameters `t = (z - z₀)/u` (from the `d p` side) and
`t = (v - v₀)/ℓ` (from the `v` side) equals the normalised determinant defect.

This is pure algebra: no Fourier estimate is asserted. -/
theorem determinantDefect_phase_identity (u ell z0 v0 dp v : ℚ)
    (hu : u ≠ 0) (hell : ell ≠ 0) (hdet : ell * z0 - u * v0 = 2) :
    (dp - z0) / u - (v - v0) / ell = (ell * dp - u * v - 2) / (u * ell) := by
  have hsplit : (dp - z0) / u - (v - v0) / ell
      = (ell * dp - u * v - (ell * z0 - u * v0)) / (u * ell) := by
    field_simp
    ring
  rw [hsplit, hdet]

/-- With the shell `ℓ dp - u v = 2 + u ℓ hSh` the phase defect is exactly the
shift `hSh`. -/
theorem determinantDefect_eq_shift (u ell z0 v0 dp v hSh : ℚ)
    (hu : u ≠ 0) (hell : ell ≠ 0) (hdet : ell * z0 - u * v0 = 2)
    (hshell : ell * dp - u * v = 2 + u * ell * hSh) :
    (dp - z0) / u - (v - v0) / ell = hSh := by
  rw [determinantDefect_phase_identity u ell z0 v0 dp v hu hell hdet, hshell]
  field_simp
  ring

/-! ## 3. Shift-independent congruences -/

/-- **`shiftedMAM_mod_u`.**  The shell forces `d p ℓ ≡ 2 (mod u)`, *independently
of the shift* `hSh`. -/
theorem shiftedMAM_mod_u (u ell d p v hSh : ℤ)
    (hshell : d * p * ell - u * v = 2 + u * ell * hSh) :
    d * p * ell ≡ 2 [ZMOD u] := by
  exact Int.modEq_iff_dvd.mpr ⟨-(v + ell * hSh), by linarith [hshell]⟩

/-- **`shiftedMAM_mod_ell`.**  The shell forces `u v ≡ -2 (mod ℓ)`, *independently
of the shift* `hSh`. -/
theorem shiftedMAM_mod_ell (u ell d p v hSh : ℤ)
    (hshell : d * p * ell - u * v = 2 + u * ell * hSh) :
    u * v ≡ -2 [ZMOD ell] := by
  refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨d * p - u * hSh, ?_⟩)
  linarith [hshell]

/-- Shift-independence, stated explicitly: two different shifts give the same
mod-`ℓ` congruence. -/
theorem shiftedMAM_mod_ell_shift_independent (u ell d₁ p₁ d₂ p₂ v hSh₁ hSh₂ : ℤ)
    (h₁ : d₁ * p₁ * ell - u * v = 2 + u * ell * hSh₁)
    (h₂ : d₂ * p₂ * ell - u * v = 2 + u * ell * hSh₂) :
    (u * v ≡ -2 [ZMOD ell]) ∧ (u * v ≡ -2 [ZMOD ell]) :=
  ⟨shiftedMAM_mod_ell u ell d₁ p₁ v hSh₁ h₁, shiftedMAM_mod_ell u ell d₂ p₂ v hSh₂ h₂⟩

/-- **`shiftedDet_zmod`.**  The mod-`ℓ` consequence in `ZMod` form, for a natural
modulus `n` playing the role of `ℓ`: the shell gives `u v = -2` in `ZMod n`, with
no trace of the shift. -/
theorem shiftedDet_zmod (n : ℕ) (u v d p hSh : ℤ)
    (hshell : d * p * (n : ℤ) - u * v = 2 + u * (n : ℤ) * hSh) :
    ((u : ZMod n)) * (v : ZMod n) = -2 := by
  have hcast := congrArg (fun z : ℤ => (z : ZMod n)) hshell
  push_cast at hcast
  simp only [ZMod.natCast_self, mul_zero, zero_mul] at hcast
  linear_combination -hcast

/-! ## 4. Divisor-switch and solve forms -/

/-- **`shiftedMAM_divisorSwitch`.**  The shell is equivalent to the divisor-switch
form `u (v + ℓ hSh) = d p ℓ - 2`. -/
theorem shiftedMAM_divisorSwitch (u ell d p v hSh : ℤ) :
    d * p * ell - u * v = 2 + u * ell * hSh ↔ u * (v + ell * hSh) = d * p * ell - 2 := by
  constructor <;> intro h <;> linarith [h]

/-- **`shiftedMAM_prime_solve`.**  Equivalently, `d p ℓ = u (v + ℓ hSh) + 2`.  No
primality or solvability is asserted. -/
theorem shiftedMAM_prime_solve (u ell d p v hSh : ℤ) :
    d * p * ell - u * v = 2 + u * ell * hSh ↔ d * p * ell = u * (v + ell * hSh) + 2 := by
  constructor <;> intro h <;> linarith [h]

/-- **`shiftedMAM_solve_v`.**  Over a field with `u ≠ 0`, the shell solves for
`v`. -/
theorem shiftedMAM_solve_v (u ell d p v hSh : ℚ) (hu : u ≠ 0)
    (hshell : d * p * ell - u * v = 2 + u * ell * hSh) :
    v = (d * p * ell - 2) / u - ell * hSh := by
  field_simp
  linarith [hshell]

/-- Solved form of the prime slot over a field, when `d ℓ ≠ 0`.  This is an
identity, not an existence or primality claim. -/
theorem shiftedMAM_solve_p (u ell d p v hSh : ℚ) (hd : d ≠ 0) (hell : ell ≠ 0)
    (hshell : d * p * ell - u * v = 2 + u * ell * hSh) :
    p = (u * (v + ell * hSh) + 2) / (d * ell) := by
  field_simp
  linear_combination hshell

/-! ## 5. Integrality of the line parameter -/

/-- If the shifted point and the `v`-slot are on the line, the two line
parameters differ by exactly the shift, over the integers. -/
theorem line_parameters_differ_by_shift (u ell z0 v0 t hSh d p v : ℤ)
    (hz : d * p = z0 + u * (t + hSh)) (hv : v = v0 + ell * t) :
    d * p - z0 = u * (t + hSh) ∧ v - v0 = ell * t := by
  constructor
  · linarith [hz]
  · linarith [hv]

end ShiftedDet
end CurrentProgramme
end TwinPrimeProject
