import RequestProject.NANC.Gate1BDet2.Det2AffineLines

/-!
# Gate 1B / determinant-2 bank, Module 19: the primitive pair surface

The physical equation of the on-shell Gate-1B investigation is

  `ℓ z − u v = 2`,

which is exactly the determinant-2 line predicate `OnDet2Line u ℓ v z` already
banked in Module 4 (`Det2AffineLines`); it is reused here rather than
duplicated.

A *common shift* of a pair of points of the same line is

  `v₂ = v₁ + ℓ h`,  `z₂ = z₁ + u h`.

The content of this module is the exact identity

  `v₂ z₁ − v₁ z₂ = h (ℓ z₁ − u v₁)`,

whose specialisation to the determinant-2 shell is

  `v₂ z₁ − v₁ z₂ = 2 h`,

together with the converse (cancellation of `h ≠ 0`) and the translation
stability of the shell, which is `det2_translate` of Module 4.

Everything is over `ℤ`, so that no truncated subtraction can occur.  Nothing in
this module is analytic: it is an exact structural coordinate on the shell, and
by itself carries no saving whatsoever.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. The pair determinant and the shift identity -/

/-- The determinant of the pair `((v₁, z₁), (v₂, z₂))`, in the orientation used
by the on-shell pair surface. -/
def pairDet (v₁ z₁ v₂ z₂ : ℤ) : ℤ := v₂ * z₁ - v₁ * z₂

@[simp] theorem pairDet_def (v₁ z₁ v₂ z₂ : ℤ) :
    pairDet v₁ z₁ v₂ z₂ = v₂ * z₁ - v₁ * z₂ := rfl

/-- **`PRIMITIVE_DET2_PAIR_SHIFT_IDENTITY`.**  For a common shift
`v₂ = v₁ + ℓ h`, `z₂ = z₁ + u h`, the pair determinant is `h` times the
determinant form of the base point.  No hypothesis at all is needed. -/
theorem pair_det_shift_identity (u l v₁ z₁ h : ℤ) :
    pairDet v₁ z₁ (v₁ + l * h) (z₁ + u * h) = h * (l * z₁ - u * v₁) := by
  simp only [pairDet_def]
  ring

/-- The same identity stated for arbitrary `v₂, z₂` satisfying the shift
equations. -/
theorem pair_det_shift_identity' {u l v₁ z₁ v₂ z₂ h : ℤ}
    (hv : v₂ = v₁ + l * h) (hz : z₂ = z₁ + u * h) :
    v₂ * z₁ - v₁ * z₂ = h * (l * z₁ - u * v₁) := by
  subst hv; subst hz; ring

/-! ## 2. On the determinant-2 shell -/

/-- **`PAIR_DETERMINANT_EQUALS_2H`.**  On the determinant-2 shell
`ℓ z₁ − u v₁ = 2`, a common shift by `h` produces pair determinant `2 h`. -/
theorem pair_det_eq_two_mul_shift {u l v₁ z₁ v₂ z₂ h : ℤ}
    (hdet : OnDet2Line u l v₁ z₁)
    (hv : v₂ = v₁ + l * h) (hz : z₂ = z₁ + u * h) :
    v₂ * z₁ - v₁ * z₂ = 2 * h := by
  have := pair_det_shift_identity' (u := u) (l := l) hv hz
  rw [this]
  unfold OnDet2Line at hdet
  rw [hdet]
  ring

/-- **Converse (cancellation of `h`).**  If a common shift with `h ≠ 0` has pair
determinant `2 h`, then the base point lies on the determinant-2 shell. -/
theorem onDet2Line_of_pair_det_eq_two_mul_shift {u l v₁ z₁ v₂ z₂ h : ℤ}
    (hh : h ≠ 0)
    (hv : v₂ = v₁ + l * h) (hz : z₂ = z₁ + u * h)
    (hpair : v₂ * z₁ - v₁ * z₂ = 2 * h) :
    OnDet2Line u l v₁ z₁ := by
  have hid : h * (l * z₁ - u * v₁) = h * 2 := by
    rw [← pair_det_shift_identity' (u := u) (l := l) hv hz, hpair]; ring
  have := mul_left_cancel₀ hh hid
  exact this

/-- The two directions packaged: for `h ≠ 0`, being on the shell is *equivalent*
to the shifted pair having determinant `2 h`. -/
theorem onDet2Line_iff_pair_det {u l v₁ z₁ v₂ z₂ h : ℤ}
    (hh : h ≠ 0) (hv : v₂ = v₁ + l * h) (hz : z₂ = z₁ + u * h) :
    OnDet2Line u l v₁ z₁ ↔ v₂ * z₁ - v₁ * z₂ = 2 * h :=
  ⟨fun hd => pair_det_eq_two_mul_shift hd hv hz,
   fun hp => onDet2Line_of_pair_det_eq_two_mul_shift hh hv hz hp⟩

/-! ## 3. Translation stability -/

/-- **Translation stability of the shell**, from the same algebra:
`ℓ (z + u h) − u (v + ℓ h) = ℓ z − u v`.  (The determinant-2 specialisation is
`det2_translate` of Module 4, which is reused rather than restated.) -/
theorem det2_form_translation_invariant (u l v z h : ℤ) :
    l * (z + u * h) - u * (v + l * h) = l * z - u * v := by ring

/-- The determinant-2 case, deduced from `det2_translate` of Module 4 (no
duplicate proof). -/
theorem det2_shell_translate {u l v z : ℤ} (hdet : OnDet2Line u l v z) (h : ℤ) :
    OnDet2Line u l (v + l * h) (z + u * h) := det2_translate' hdet h

/-! ## 4. Guard -/

/-- **Guard.**  The hypothesis `h ≠ 0` in the converse is load-bearing: with
`h = 0` the pair determinant is `0 = 2·0` for *every* `(u, ℓ, v₁, z₁)`, in
particular for points off the shell. -/
theorem pair_det_converse_needs_h_ne_zero :
    ∃ u l v₁ z₁ v₂ z₂ h : ℤ,
      v₂ = v₁ + l * h ∧ z₂ = z₁ + u * h ∧ v₂ * z₁ - v₁ * z₂ = 2 * h ∧
        ¬ OnDet2Line u l v₁ z₁ := by
  refine ⟨1, 1, 0, 0, 0, 0, 0, by ring, by ring, by ring, ?_⟩
  unfold OnDet2Line
  norm_num

end Gate1BDet2
end TwinPrimeProject
