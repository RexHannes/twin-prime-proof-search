import RequestProject.NANC.Gate1BDet2.PrimitiveDet2PairSurface

/-!
# Gate 1B / determinant-2 bank, Module 20: gcd recovery for a common shift

For a common shift

  `Δv = ℓ h`,  `Δz = u h`

with `gcd(u, ℓ) = 1`, the shift parameter `h` is recovered as the gcd of the
increments:

  `gcd(Δv, Δz) = h`.

The decomposition used is the two-line one requested:

  `gcd(ℓ h, u h) = h · gcd(ℓ, u) = h`.

Both the `ℕ` form (where `gcd` is literally `h`) and the `ℤ` form (where the
`ℕ`-valued `Int.gcd` is `h.natAbs`, hence `h` for `h > 0`) are banked, and the
whole pair-surface package (`determinant = 2h` *and* `gcd of increments = h`) is
assembled at the end.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. The gcd computation over `ℕ` -/

/-- **`COMMON_SHIFT_GCD_RECOVERY` (naturals).**  `gcd(ℓ h, u h) = h` when
`u` and `ℓ` are coprime. -/
theorem gcd_shift_pair_eq_h {u l h : ℕ} (hc : Nat.Coprime u l) :
    Nat.gcd (l * h) (u * h) = h := by
  rw [Nat.gcd_mul_right]
  rw [Nat.Coprime] at hc
  rw [Nat.gcd_comm l u, hc, one_mul]

/-- The intermediate decomposition, banked separately: the gcd of the two
increments always factors as `gcd(ℓ, u) · h`. -/
theorem gcd_shift_pair_factors (l u h : ℕ) :
    Nat.gcd (l * h) (u * h) = Nat.gcd l u * h := Nat.gcd_mul_right l h u

/-! ## 2. The gcd computation over `ℤ` -/

/-- **`COMMON_SHIFT_GCD_RECOVERY` (integers).**  With `Int.gcd u ℓ = 1`,
`Int.gcd (ℓ h) (u h) = |h|`. -/
theorem int_gcd_shift_pair_eq_natAbs {u l h : ℤ} (hc : Int.gcd u l = 1) :
    Int.gcd (l * h) (u * h) = h.natAbs := by
  rw [Int.gcd_mul_right]
  rw [Int.gcd_comm l u, hc, one_mul]

/-- For a positive shift the integer statement reads `gcd = h` on the nose. -/
theorem int_gcd_shift_pair_eq_h {u l h : ℤ} (hc : Int.gcd u l = 1) (hh : 0 < h) :
    (Int.gcd (l * h) (u * h) : ℤ) = h := by
  rw [int_gcd_shift_pair_eq_natAbs hc]
  exact Int.natAbs_of_nonneg hh.le

/-! ## 3. The packaged forward pair-surface theorem -/

/-- **`PRIMITIVE_DET2_PAIR_SURFACE_FORWARD`.**  Let `ℓ z₁ − u v₁ = 2` (the
determinant-2 shell), let `(v₂, z₂)` be the common shift of `(v₁, z₁)` by
`h > 0`, and let `u, ℓ` be coprime.  Then simultaneously

* `v₂ z₁ − v₁ z₂ = 2 h`, and
* `gcd(v₂ − v₁, z₂ − z₁) = h`.

This is an exact structural coordinate on the shell; it is *not* an analytic
statement and carries no saving. -/
theorem primitive_det2_pair_surface_forward {u l v₁ z₁ v₂ z₂ h : ℤ}
    (hdet : OnDet2Line u l v₁ z₁) (hc : Int.gcd u l = 1) (hh : 0 < h)
    (hv : v₂ = v₁ + l * h) (hz : z₂ = z₁ + u * h) :
    v₂ * z₁ - v₁ * z₂ = 2 * h ∧ (Int.gcd (v₂ - v₁) (z₂ - z₁) : ℤ) = h := by
  refine ⟨pair_det_eq_two_mul_shift hdet hv hz, ?_⟩
  have h1 : v₂ - v₁ = l * h := by rw [hv]; ring
  have h2 : z₂ - z₁ = u * h := by rw [hz]; ring
  rw [h1, h2]
  exact int_gcd_shift_pair_eq_h hc hh

/-! ## 4. Guard -/

/-- **Guard.**  Coprimality is load-bearing: with `u = ℓ = 2`, `h = 1` the gcd of
the increments is `2 ≠ h`. -/
theorem gcd_shift_pair_needs_coprimality :
    Nat.gcd (2 * 1) (2 * 1) ≠ 1 := by decide

end Gate1BDet2
end TwinPrimeProject
