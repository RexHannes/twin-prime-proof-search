import RequestProject.NANC.HPoissonComplementaryDivisor.PoissonCongruenceCore

/-!
# HPoissonComplementaryDivisor, Module 3: the complementary divisor variable

The divisibility `q ∣ y v - 2` is converted into the *equation* `y v - q ℓ = 2`
with a complementary divisor variable `ℓ ∈ ℤ`.

All statements are over `ℤ`: `y` may be negative and `ℓ` may be negative.
Positivity of `ℓ` is **never** assumed, and `ell_can_be_negative` records an
explicit instance with `ℓ < 0`.
-/

namespace TwinPrimeProject
namespace HPoissonCD

/-! ## 1. The complementary-divisor bijection -/

/-- **Complementary divisor, existence.**  For integers `y, v` and any integer
modulus `q`, `q ∣ y v - 2` iff the shifted equation `y v - q ℓ = 2` is solvable
in `ℓ ∈ ℤ`. -/
theorem dvd_iff_exists_ell (y v q : ℤ) :
    q ∣ (y * v - 2) ↔ ∃ ℓ : ℤ, y * v - q * ℓ = 2 := by
  constructor
  · rintro ⟨ℓ, hℓ⟩; exact ⟨ℓ, by linarith⟩
  · rintro ⟨ℓ, hℓ⟩; exact ⟨ℓ, by linarith⟩

/-- **Uniqueness of the complementary divisor** for a nonzero modulus. -/
theorem ell_unique {y v q ℓ ℓ' : ℤ} (hq : q ≠ 0)
    (h : y * v - q * ℓ = 2) (h' : y * v - q * ℓ' = 2) : ℓ = ℓ' := by
  have : q * ℓ = q * ℓ' := by linarith
  exact mul_left_cancel₀ hq this

/-- The complementary divisor is `ℓ = (y v - 2) / q` (exact division). -/
theorem ell_eq_div {y v q ℓ : ℤ} (hq : q ≠ 0) (h : y * v - q * ℓ = 2) :
    ℓ = (y * v - 2) / q := by
  have : y * v - 2 = q * ℓ := by linarith
  rw [this, Int.mul_ediv_cancel_left _ hq]

/-- Existence *and* uniqueness in one statement, for `q ≠ 0`. -/
theorem existsUnique_ell {y v q : ℤ} (hq : q ≠ 0) (hdvd : q ∣ (y * v - 2)) :
    ∃! ℓ : ℤ, y * v - q * ℓ = 2 := by
  obtain ⟨ℓ, hℓ⟩ := (dvd_iff_exists_ell y v q).mp hdvd
  exact ⟨ℓ, hℓ, fun ℓ' hℓ' => ell_unique hq hℓ' hℓ⟩

/-- **Negative data are handled.**  With `y = -1`, `v = 1`, `q = 3` the
complementary divisor is `ℓ = -1 < 0`: positivity of `ℓ` is not available. -/
theorem ell_can_be_negative :
    ∃ (y v q ℓ : ℤ), 0 < q ∧ y < 0 ∧ ℓ < 0 ∧ y * v - q * ℓ = 2 :=
  ⟨-1, 1, 3, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Positive `q`, positive `y` may still give `ℓ = 0` (the equation is not a
statement about the size of `ℓ`). -/
theorem ell_can_be_zero :
    ∃ (y v q ℓ : ℤ), 0 < q ∧ 0 < y ∧ ℓ = 0 ∧ y * v - q * ℓ = 2 :=
  ⟨2, 1, 5, 0, by norm_num, by norm_num, rfl, by norm_num⟩

/-! ## 2. Substitution of a factorization of the modulus -/

/-- **Generic substitution.**  If `q = d p` and `y v - q ℓ = 2` then
`y v - d p ℓ = 2`. -/
theorem subst_factor {y v q d p ℓ : ℤ} (hq : q = d * p) (h : y * v - q * ℓ = 2) :
    y * v - d * p * ℓ = 2 := by
  rw [hq] at h; linarith [h]

/-- The converse substitution. -/
theorem subst_factor' {y v q d p ℓ : ℤ} (hq : q = d * p) (h : y * v - d * p * ℓ = 2) :
    y * v - q * ℓ = 2 := by
  rw [hq]; linarith [h]

/-- Combined with the divisibility form: for `q = d p`,
`q ∣ y v - 2 ↔ ∃ ℓ, y v - d p ℓ = 2`. -/
theorem dvd_iff_exists_ell_factored {y v q d p : ℤ} (hq : q = d * p) :
    q ∣ (y * v - 2) ↔ ∃ ℓ : ℤ, y * v - d * p * ℓ = 2 := by
  rw [dvd_iff_exists_ell]
  constructor
  · rintro ⟨ℓ, hℓ⟩; exact ⟨ℓ, subst_factor hq hℓ⟩
  · rintro ⟨ℓ, hℓ⟩; exact ⟨ℓ, subst_factor' hq hℓ⟩

/-! ## 3. Link with the CRT split of Module 2 -/

/-- Under the CRT hypotheses of Module 2, membership of the dual variable `y`
in the residue class `2 w̄ (mod q₁ q₂)` is equivalent to the solvability of two
complementary-divisor equations, one for each coprime factor. -/
theorem residue_iff_two_ell {q₁ q₂ v₁ v₂ w wbar y : ℤ} (hq : IsCoprime q₁ q₂)
    (hw₁ : w ≡ v₁ [ZMOD q₁]) (hw₂ : w ≡ v₂ [ZMOD q₂])
    (hinv : w * wbar ≡ 1 [ZMOD q₁ * q₂]) :
    y ≡ 2 * wbar [ZMOD q₁ * q₂] ↔
      ((∃ ℓ₁ : ℤ, y * v₁ - q₁ * ℓ₁ = 2) ∧ (∃ ℓ₂ : ℤ, y * v₂ - q₂ * ℓ₂ = 2)) := by
  rw [residue_iff_split hq hw₁ hw₂ hinv, dvd_iff_exists_ell, dvd_iff_exists_ell]

end HPoissonCD
end TwinPrimeProject
