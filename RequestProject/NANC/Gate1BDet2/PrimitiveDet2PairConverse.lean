import RequestProject.NANC.Gate1BDet2.CommonShiftGCD

/-!
# Gate 1B / determinant-2 bank, Module 21: the pair-surface converse

The converse direction of the pair surface, in the Lean-friendly formulation
that avoids dividing arbitrary integers by a gcd.

Given a common shift

  `v₂ = v₁ + ℓ h`,  `z₂ = z₁ + u h`,  `h > 0`,

the equation

  `v₂ z₁ − v₁ z₂ = 2 h`

forces the base point onto the determinant-2 shell, `ℓ z₁ − u v₁ = 2`; this is
cancellation of `h` in `h (ℓ z₁ − u v₁) = 2 h`.

Separately the *normalisation* fact is banked: under `gcd(u, ℓ) = 1` the shift
parameter `h` is exactly the gcd of the increments, and the triple `(u, ℓ, h)`
is uniquely determined by the pair of increments.  Together these give the exact
mathematical content of the pair-surface bijection without any quotient
definitions.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. The converse -/

/-- **`PRIMITIVE_DET2_PAIR_SURFACE_CONVERSE`.**  A common shift by `h > 0` whose
pair determinant equals `2 h` has its base point on the determinant-2 shell. -/
theorem primitive_det2_pair_surface_converse {u l v₁ z₁ v₂ z₂ h : ℤ}
    (hh : 0 < h) (hv : v₂ = v₁ + l * h) (hz : z₂ = z₁ + u * h)
    (hpair : v₂ * z₁ - v₁ * z₂ = 2 * h) :
    l * z₁ - u * v₁ = 2 :=
  onDet2Line_of_pair_det_eq_two_mul_shift (ne_of_gt hh) hv hz hpair

/-! ## 2. Normalisation: `h` is the gcd of the increments -/

/-- **Normalisation fact.**  If `Δv = ℓ h`, `Δz = u h` with `gcd(u, ℓ) = 1` and
`h > 0`, then `h` is precisely the gcd of the increments. -/
theorem shift_parameter_eq_gcd_of_increments {u l h dv dz : ℤ}
    (hc : Int.gcd u l = 1) (hh : 0 < h) (hv : dv = l * h) (hz : dz = u * h) :
    (Int.gcd dv dz : ℤ) = h := by
  subst hv; subst hz
  exact int_gcd_shift_pair_eq_h hc hh

/-- **Uniqueness of the primitive normal form.**  A pair of increments
determines the direction `(ℓ, u)` and the shift `h` uniquely, once the direction
is required to be primitive and the shift positive. -/
theorem primitive_shift_normal_form_unique {u l h u' l' h' dv dz : ℤ}
    (hc : Int.gcd u l = 1) (hc' : Int.gcd u' l' = 1)
    (hh : 0 < h) (hh' : 0 < h')
    (hv : dv = l * h) (hz : dz = u * h)
    (hv' : dv = l' * h') (hz' : dz = u' * h') :
    h = h' ∧ l = l' ∧ u = u' := by
  have e1 : (Int.gcd dv dz : ℤ) = h := shift_parameter_eq_gcd_of_increments hc hh hv hz
  have e2 : (Int.gcd dv dz : ℤ) = h' := shift_parameter_eq_gcd_of_increments hc' hh' hv' hz'
  have hEq : h = h' := by rw [← e1, e2]
  subst hEq
  refine ⟨rfl, ?_, ?_⟩
  · have : l * h = l' * h := by rw [← hv, hv']
    exact mul_right_cancel₀ (ne_of_gt hh) this
  · have : u * h = u' * h := by rw [← hz, hz']
    exact mul_right_cancel₀ (ne_of_gt hh) this

/-! ## 3. The packaged equivalence -/

/-- **Pair-surface package.**  For a common shift by `h > 0` with primitive
direction `(u, ℓ)`, membership of the base point on the determinant-2 shell is
equivalent to the pair determinant being `2 h`, and in either case the gcd of
the increments is `h`. -/
theorem primitive_det2_pair_surface {u l v₁ z₁ v₂ z₂ h : ℤ}
    (hc : Int.gcd u l = 1) (hh : 0 < h)
    (hv : v₂ = v₁ + l * h) (hz : z₂ = z₁ + u * h) :
    (OnDet2Line u l v₁ z₁ ↔ v₂ * z₁ - v₁ * z₂ = 2 * h) ∧
      (Int.gcd (v₂ - v₁) (z₂ - z₁) : ℤ) = h := by
  refine ⟨onDet2Line_iff_pair_det (ne_of_gt hh) hv hz, ?_⟩
  refine shift_parameter_eq_gcd_of_increments hc hh ?_ ?_
  · rw [hv]; ring
  · rw [hz]; ring

end Gate1BDet2
end TwinPrimeProject
