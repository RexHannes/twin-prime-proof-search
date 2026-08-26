import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 2: complementary divisor, fixed shift 2

The congruence side condition `q ∣ u v + 2` (fixed shift `2`, never averaged) is
equivalent to the existence of a *named* complementary divisor `l` with

  `u v + 2 = q l`,

and, over `ℤ`, to the determinant normal form

  `l q − u v = 2`,  equivalently  `u v − q l = −2`.

No dyadic or asymptotic information is encoded here.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. Natural-number form -/

/-- The determinant-2 incidence predicate over `ℕ`, with fixed shift `2`. -/
def Det2 (u v q l : ℕ) : Prop := u * v + 2 = q * l

/-- **Congruence ↔ complementary divisor.** -/
theorem dvd_iff_exists_det2 (u v q : ℕ) :
    q ∣ u * v + 2 ↔ ∃ l : ℕ, Det2 u v q l := by
  constructor
  · rintro ⟨l, hl⟩; exact ⟨l, hl⟩
  · rintro ⟨l, hl⟩; exact ⟨l, hl⟩

theorem Det2.dvd {u v q l : ℕ} (h : Det2 u v q l) : q ∣ u * v + 2 := ⟨l, h⟩

/-- Uniqueness of the complementary divisor for a nonzero modulus. -/
theorem det2_ell_unique {u v q l l' : ℕ} (hq : 0 < q)
    (h : Det2 u v q l) (h' : Det2 u v q l') : l = l' :=
  Nat.eq_of_mul_eq_mul_left hq (by rw [← h, ← h'] : q * l = q * l')

/-- `l` is the exact quotient `(u v + 2) / q`. -/
theorem det2_ell_eq_div {u v q l : ℕ} (hq : 0 < q) (h : Det2 u v q l) :
    l = (u * v + 2) / q := by
  rw [Det2] at h
  rw [h, Nat.mul_div_cancel_left _ hq]

/-- The complementary divisor is positive (the shift `2` is nonzero). -/
theorem det2_ell_pos {u v q l : ℕ} (h : Det2 u v q l) : 0 < l := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · rw [Det2, hl, Nat.mul_zero] at h; omega
  · exact hl

/-- The modulus is positive. -/
theorem det2_modulus_pos {u v q l : ℕ} (h : Det2 u v q l) : 0 < q := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · rw [Det2, hq, Nat.zero_mul] at h; omega
  · exact hq

/-! ## 2. Integer determinant normal form -/

/-- The determinant-2 predicate over `ℤ`, written as an exact determinant. -/
def Det2Int (u v q l : ℤ) : Prop := l * q - u * v = 2

/-- The `ℕ` incidence and the `ℤ` determinant normal form agree. -/
theorem det2_iff_int (u v q l : ℕ) :
    Det2 u v q l ↔ Det2Int (u : ℤ) (v : ℤ) (q : ℤ) (l : ℤ) := by
  unfold Det2 Det2Int
  constructor
  · intro h
    have : ((u * v + 2 : ℕ) : ℤ) = ((q * l : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at this
    linarith
  · intro h
    have : ((u * v + 2 : ℕ) : ℤ) = ((q * l : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this

/-- The two orientations of the integer determinant form are equivalent. -/
theorem det2Int_iff_neg (u v q l : ℤ) :
    Det2Int u v q l ↔ u * v - q * l = -2 := by
  unfold Det2Int; constructor <;> intro h <;> linarith [h]

/-- The integer form of the complementary-divisor equation. -/
theorem det2Int_iff_add (u v q l : ℤ) :
    Det2Int u v q l ↔ u * v + 2 = q * l := by
  unfold Det2Int; constructor <;> intro h <;> linarith [h]

/-- **Congruence ↔ determinant normal form** over `ℤ`. -/
theorem int_dvd_iff_exists_det2Int (u v q : ℤ) :
    q ∣ u * v + 2 ↔ ∃ l : ℤ, Det2Int u v q l := by
  constructor
  · rintro ⟨l, hl⟩; exact ⟨l, by unfold Det2Int; linarith⟩
  · rintro ⟨l, hl⟩; exact ⟨l, by rw [det2Int_iff_add] at hl; linarith⟩

/-- Combined statement: for naturals, the congruence `q ∣ u v + 2` is equivalent
to solvability of the integer determinant equation `l q − u v = 2` in naturals. -/
theorem dvd_iff_exists_det2Int_nat (u v q : ℕ) :
    q ∣ u * v + 2 ↔ ∃ l : ℕ, ((l : ℤ) * q - (u : ℤ) * v = 2) := by
  rw [dvd_iff_exists_det2]
  exact exists_congr fun l => det2_iff_int u v q l

end Gate1BDet2
end TwinPrimeProject
