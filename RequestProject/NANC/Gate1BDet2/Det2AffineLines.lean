import Mathlib
import RequestProject.NANC.Gate1BDet2.Det2Coprime

/-!
# Gate 1B / determinant-2 bank, Module 4: the affine-line parametrisation

Fix `u, l` coprime.  The integral points `(v, q)` of the fixed determinant-2 line

  `l q − u v = 2`

form a single affine progression: once one solution `(v₀, q₀)` is known, every
solution is `(v₀ + l t, q₀ + u t)` for a *unique* `t : ℤ`.

Everything is over `ℤ`; positivity and dyadic range restrictions are stated
separately (Module 5 and the source ranges) and never mixed into the algebra.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-- The determinant-2 line with fixed direction data `(u, l)`. -/
def OnDet2Line (u l v q : ℤ) : Prop := l * q - u * v = 2

/-! ## 1. The difference identity -/

/-- **Difference identity.**  Two points of the same determinant-2 line differ
along the direction `(l, u)`. -/
theorem det2_diff {u l v₁ q₁ v₂ q₂ : ℤ}
    (h₁ : OnDet2Line u l v₁ q₁) (h₂ : OnDet2Line u l v₂ q₂) :
    u * (v₂ - v₁) = l * (q₂ - q₁) := by
  unfold OnDet2Line at h₁ h₂
  linear_combination h₁ - h₂

/-! ## 2. Existence and uniqueness of the affine parameter -/

/-- **Uniqueness of the affine parameter.**  If `u` and `l` are coprime, the
direction vector `(l, u)` is not a proper multiple of itself: `t` is determined
by `(l t, u t)`. -/
theorem det2_param_unique {u l t t' : ℤ} (hc : IsCoprime u l)
    (hv : l * t = l * t') (hq : u * t = u * t') : t = t' := by
  obtain ⟨a, b, hab⟩ := hc
  have key : (a * u + b * l) * t = (a * u + b * l) * t' := by
    calc (a * u + b * l) * t = a * (u * t) + b * (l * t) := by ring
      _ = a * (u * t') + b * (l * t') := by rw [hv, hq]
      _ = (a * u + b * l) * t' := by ring
  rw [hab, one_mul, one_mul] at key
  exact key

/-- **Existence of the affine parameter.**  Any two points of the determinant-2
line with coprime `(u, l)` differ by an integral multiple of `(l, u)`. -/
theorem det2_exists_param {u l v₁ q₁ v₂ q₂ : ℤ} (hc : IsCoprime u l)
    (h₁ : OnDet2Line u l v₁ q₁) (h₂ : OnDet2Line u l v₂ q₂) :
    ∃ t : ℤ, v₂ - v₁ = l * t ∧ q₂ - q₁ = u * t := by
  have hdiff : u * (v₂ - v₁) = l * (q₂ - q₁) := det2_diff h₁ h₂
  have hl_dvd : l ∣ (v₂ - v₁) := by
    refine (hc.symm).dvd_of_dvd_mul_left ?_
    exact ⟨q₂ - q₁, hdiff⟩
  have hu_dvd : u ∣ (q₂ - q₁) := by
    refine hc.dvd_of_dvd_mul_left ?_
    exact ⟨v₂ - v₁, hdiff.symm⟩
  obtain ⟨s, hs⟩ := hl_dvd
  obtain ⟨r, hr⟩ := hu_dvd
  by_cases hl : l = 0
  · -- then `u` is a unit, in particular nonzero, and `v₂ = v₁`
    have hu : IsUnit u := by
      rw [hl] at hc; exact isCoprime_zero_right.mp hc
    have hune : u ≠ 0 := hu.ne_zero
    refine ⟨r, ?_, hr⟩
    have : u * (v₂ - v₁) = 0 := by rw [hdiff, hl, zero_mul]
    have hv : v₂ - v₁ = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hune
      · exact h
    rw [hv, hl, zero_mul]
  · refine ⟨s, hs, ?_⟩
    have : l * (q₂ - q₁) = l * (u * s) := by
      rw [← hdiff, hs]; ring
    exact mul_left_cancel₀ hl this

/-! ## 3. Translation stability -/

/-- **Translation stability.**  Translating a solution by `t · (l, u)` again
solves the determinant-2 equation. -/
theorem det2_translate {u l v₀ q₀ : ℤ} (h : OnDet2Line u l v₀ q₀) (t : ℤ) :
    l * (q₀ + u * t) - u * (v₀ + l * t) = 2 := by
  unfold OnDet2Line at h
  linear_combination h

/-- Translation stability, restated with the line predicate. -/
theorem det2_translate' {u l v₀ q₀ : ℤ} (h : OnDet2Line u l v₀ q₀) (t : ℤ) :
    OnDet2Line u l (v₀ + l * t) (q₀ + u * t) := det2_translate h t

/-! ## 4. The full parametrisation -/

/-- **Affine-line parametrisation.**  Given coprime `(u, l)` and one solution
`(v₀, q₀)`, a pair `(v, q)` lies on the determinant-2 line iff it is the
translate of `(v₀, q₀)` by a unique integral parameter `t`. -/
theorem det2_line_param_iff {u l v₀ q₀ : ℤ} (hc : IsCoprime u l)
    (h₀ : OnDet2Line u l v₀ q₀) (v q : ℤ) :
    OnDet2Line u l v q ↔ ∃! t : ℤ, v = v₀ + l * t ∧ q = q₀ + u * t := by
  constructor
  · intro h
    obtain ⟨t, hv, hq⟩ := det2_exists_param hc h₀ h
    refine ⟨t, ⟨by linarith, by linarith⟩, ?_⟩
    rintro t' ⟨hv', hq'⟩
    refine det2_param_unique hc ?_ ?_
    · have : l * t' = v - v₀ := by linarith
      rw [this]; linarith
    · have : u * t' = q - q₀ := by linarith
      rw [this]; linarith
  · rintro ⟨t, ⟨hv, hq⟩, -⟩
    subst hv; subst hq
    exact det2_translate' h₀ t

end Gate1BDet2
end TwinPrimeProject
