import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 15: the prime-modulus coordinate change

Only the **finite-field algebra** behind the new prime-modulus coordinate is
formalized here.  For a nonzero `u` in a field,

  `u v + 2 = u (v + 2 u⁻¹)`,

so a multiplicative character factors as

  `χ(u v + 2) = χ(u) · χ(v + 2 u⁻¹)`.

The second factor genuinely can vanish: `v + 2u⁻¹ = 0` exactly when
`u v + 2 = 0`.  This is recorded explicitly (`shifted_factor_eq_zero_iff`)
rather than silently excluded; the character identity itself needs no
nonvanishing hypothesis, because `MulChar` is multiplicative on all of the
ring.

Finally, the coordinate change `u ↦ 2 u⁻¹` is injective on nonzero elements
whenever `2 ≠ 0`.

**Not formalized (interface, see `Gate1BMCInterfaces`):** any analytic
consequence of this coordinate change — the character-sum estimates, their
uniformity, the coefficient-class matching, and the `(c, χ)`-covariance.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace PrimeChar

variable {K : Type*} [Field K]

/-! ## 1. The ring identity -/

/-- **The prime-modulus coordinate change.**  For `u ≠ 0` in a field,
`u v + 2 = u (v + 2 u⁻¹)`. -/
theorem mul_add_two_eq (u v : K) (hu : u ≠ 0) : u * v + 2 = u * (v + 2 * u⁻¹) := by
  field_simp

/-- The general shifted version, for an arbitrary shift `s`. -/
theorem mul_add_eq (u v s : K) (hu : u ≠ 0) : u * v + s = u * (v + s * u⁻¹) := by
  field_simp

/-- The second factor vanishes exactly when the original quantity does. -/
theorem shifted_factor_eq_zero_iff (u v : K) (hu : u ≠ 0) :
    v + 2 * u⁻¹ = 0 ↔ u * v + 2 = 0 := by
  rw [mul_add_two_eq u v hu]
  simp [hu]

/-! ## 2. The character rewrite -/

variable {R : Type*} [CommMonoidWithZero R]

/-- **The multiplicative rewrite.**  For any multiplicative character `χ` of a
field `K` with values in a commutative monoid with zero, and any `u ≠ 0`,

  `χ(u v + 2) = χ(u) · χ(v + 2 u⁻¹)`.

No nonvanishing hypothesis on `u v + 2` is needed: if the shifted factor is
zero then both sides are `χ 0`-multiples and the identity still holds, since it
is obtained from the ring identity by multiplicativity. -/
theorem mulChar_mul_add_two (χ : MulChar K R) (u v : K) (hu : u ≠ 0) :
    χ (u * v + 2) = χ u * χ (v + 2 * u⁻¹) := by
  rw [mul_add_two_eq u v hu, map_mul]

/-- The general shifted version of the character rewrite. -/
theorem mulChar_mul_add (χ : MulChar K R) (u v s : K) (hu : u ≠ 0) :
    χ (u * v + s) = χ u * χ (v + s * u⁻¹) := by
  rw [mul_add_eq u v s hu, map_mul]

/-- Degenerate case, recorded explicitly: when the shifted factor vanishes both
sides of the rewrite are `χ u * χ 0`. -/
theorem mulChar_mul_add_two_of_factor_zero (χ : MulChar K R) (u v : K) (hu : u ≠ 0)
    (h0 : v + 2 * u⁻¹ = 0) :
    χ (u * v + 2) = χ u * χ 0 := by
  rw [mulChar_mul_add_two χ u v hu, h0]

/-! ## 3. Injectivity of the coordinate change -/

/-- **Injectivity of `u ↦ 2 u⁻¹`** on nonzero elements, whenever `2 ≠ 0`. -/
theorem two_inv_injOn (h2 : (2 : K) ≠ 0) :
    Set.InjOn (fun u : K => 2 * u⁻¹) {u : K | u ≠ 0} := by
  intro u₁ h₁ u₂ h₂ h
  simp only at h
  have hinv : u₁⁻¹ = u₂⁻¹ := by
    exact mul_left_cancel₀ h2 h
  have := congrArg (fun x : K => x⁻¹) hinv
  simpa using this

/-- The same statement in explicit form. -/
theorem two_inv_inj (h2 : (2 : K) ≠ 0) {u₁ u₂ : K} (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0)
    (h : 2 * u₁⁻¹ = 2 * u₂⁻¹) : u₁ = u₂ :=
  two_inv_injOn h2 h₁ h₂ h

/-! ## 4. Specialisation to `ZMod p` -/

section ZModP

variable {p : ℕ} [Fact p.Prime]

/-- The coordinate change over `ZMod p`. -/
theorem zmod_mul_add_two_eq (u v : ZMod p) (hu : u ≠ 0) :
    u * v + 2 = u * (v + 2 * u⁻¹) :=
  mul_add_two_eq u v hu

/-- The character rewrite over `ZMod p`. -/
theorem zmod_mulChar_mul_add_two (χ : MulChar (ZMod p) R) (u v : ZMod p) (hu : u ≠ 0) :
    χ (u * v + 2) = χ u * χ (v + 2 * u⁻¹) :=
  mulChar_mul_add_two χ u v hu

/-- For odd `p`, `u ↦ 2 u⁻¹` is injective on the nonzero residues. -/
theorem zmod_two_inv_injOn (hp : p ≠ 2) :
    Set.InjOn (fun u : ZMod p => 2 * u⁻¹) {u : ZMod p | u ≠ 0} := by
  refine two_inv_injOn ?_
  have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
  simpa using h

end ZModP

/-! ## 5. Guard -/

/-- **Guard.**  The identity is genuinely restricted to `u ≠ 0`: over any field
the statement `u v + 2 = u (v + 2 u⁻¹)` fails at `u = 0`, `v` arbitrary, since
the left side is `2` and the right side is `0`. -/
theorem coordinate_change_needs_u_ne_zero :
    ((0 : ℚ) * 1 + 2 ≠ 0 * (1 + 2 * (0 : ℚ)⁻¹)) := by
  norm_num

/-- **Guard.**  This module contains no analytic content: it proves a ring
identity, its character image, and an injectivity statement.  No bound on any
character sum is asserted. -/
theorem prime_character_module_is_algebraic (u v : ℚ) (hu : u ≠ 0) :
    u * v + 2 = u * (v + 2 * u⁻¹) :=
  mul_add_two_eq u v hu

end PrimeChar
end Gate1BDet2
end TwinPrimeProject
