/-
# Gate-1A §16: the hard-support finite-exclusion lemma

Elementary clean-range arithmetic for the moving prime family.

**Scope warning (kernel-checked scope, not a census).**  These theorems cover
exactly the *listed unit conditions*: `p` prime, `ν ≢ 0`, `|ν| < p`, and a
moving variable `r` confined to an interval of diameter `< p`.  They do
**not** classify all source hard indicators.
-/
import Mathlib

namespace Gate1A

namespace HardSupport

/-- **`at_most_one_moving_r_bad`.**  Fix `m, ν, p` with `p` prime,
`ν ≠ 0` and `|ν| < p`.  Then in any interval of diameter `< p` there is at
most one `r` with `p ∣ m + ν r`. -/
theorem at_most_one_moving_r_bad {p : ℕ} (hp : p.Prime) (m nu r1 r2 : ℤ)
    (hnu : nu ≠ 0) (hnult : |nu| < (p : ℤ)) (hdiam : |r1 - r2| < (p : ℤ))
    (h1 : (p : ℤ) ∣ m + nu * r1) (h2 : (p : ℤ) ∣ m + nu * r2) :
    r1 = r2 := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ∣ nu * (r1 - r2) := by
    have := dvd_sub h1 h2
    simpa [mul_sub] using this
  have hnotdvd : ¬ (p : ℤ) ∣ nu := by
    intro hc
    have := Int.le_of_dvd (abs_pos.mpr hnu) ((dvd_abs _ _).mpr hc)
    omega
  have hr : (p : ℤ) ∣ r1 - r2 := (hpp.dvd_mul.mp hdvd).resolve_left hnotdvd
  rcases eq_or_ne (r1 - r2) 0 with h0 | h0
  · omega
  · exact absurd (Int.le_of_dvd (abs_pos.mpr h0) ((dvd_abs _ _).mpr hr)) (by omega)

/-- **`moving_r_bad_of_nu_zero_independent`.**  When `ν = 0` the condition
`p ∣ m + ν r` does not depend on the moving variable `r` at all. -/
theorem moving_r_bad_of_nu_zero_independent {p : ℕ} (m : ℤ) (r r' : ℤ) :
    ((p : ℤ) ∣ m + 0 * r) ↔ ((p : ℤ) ∣ m + 0 * r') := by
  simp

/-- The `k`-formulation: for fixed `m, ν, p` with `p` prime, `ν ≠ 0`,
`|ν| < p`, the bad set of `r` inside a window `[r₀, r₀ + p)` is a subsingleton. -/
theorem bad_set_subsingleton {p : ℕ} (hp : p.Prime) (m nu r0 : ℤ)
    (hnu : nu ≠ 0) (hnult : |nu| < (p : ℤ)) :
    Set.Subsingleton {r : ℤ | r0 ≤ r ∧ r < r0 + p ∧ (p : ℤ) ∣ m + nu * r} := by
  rintro r1 ⟨hl1, hu1, hd1⟩ r2 ⟨hl2, hu2, hd2⟩
  exact at_most_one_moving_r_bad hp m nu r1 r2 hnu hnult (by rw [abs_lt]; omega) hd1 hd2

end HardSupport

end Gate1A
