/-
# Gate 1B safe extension — primitive-conductor branch partition

The finite divisor/router statement behind the primitive-conductor trichotomy:
a divisor of `d p` (with `p` prime) either avoids `p` entirely (and then divides `d`),
or equals `p`, or is `p h` with `h ∣ d`, `h > 1`.

This is combinatorics of divisors.  It is NOT a Ramanujan-sum bound and NOT an
analytic statement; the Ramanujan analysis stays in the interfaces.
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- **Primitive-conductor trichotomy.**  Every divisor of `d p` (with `p` prime, `d > 0`)
falls into exactly one of the three router branches. -/
theorem primitiveConductorTrichotomy {d p c : ℕ} (hp : p.Prime) (hd : 0 < d) (hc : c ∣ d * p) :
    (¬ p ∣ c ∧ c ∣ d) ∨ c = p ∨ ∃ h, h ∣ d ∧ 1 < h ∧ c = p * h := by
  by_cases hpc : p ∣ c
  · obtain ⟨h, rfl⟩ := hpc
    have hpd : p * h ∣ p * d := by rwa [mul_comm d p] at hc
    have hhd : h ∣ d := (mul_dvd_mul_iff_left hp.pos.ne').mp hpd
    rcases Nat.lt_or_ge h 2 with hlt | h2
    · interval_cases h
      · exact absurd (Nat.eq_zero_of_zero_dvd (by simpa using hhd)) hd.ne'
      · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr ⟨h, hhd, h2, rfl⟩)
  · exact Or.inl ⟨hpc, Nat.Coprime.dvd_of_dvd_mul_right
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc).symm hc⟩

/-- The three branches are pairwise exclusive, so the trichotomy is a genuine partition. -/
theorem primitiveConductor_cases_disjoint {d p c : ℕ} (hp : p.Prime) :
    ¬ ((¬ p ∣ c ∧ c ∣ d) ∧ c = p) ∧
      ¬ ((¬ p ∣ c ∧ c ∣ d) ∧ ∃ h, h ∣ d ∧ 1 < h ∧ c = p * h) ∧
      ¬ (c = p ∧ ∃ h, h ∣ d ∧ 1 < h ∧ c = p * h) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨hnp, -⟩, rfl⟩; exact hnp dvd_rfl
  · rintro ⟨⟨hnp, -⟩, h, -, -, rfl⟩; exact hnp ⟨h, rfl⟩
  · rintro ⟨hcp, h, -, hh1, hph⟩
    rw [hcp] at hph
    have h1 : p * 1 = p * h := by simpa using hph
    have := Nat.eq_of_mul_eq_mul_left hp.pos h1
    omega

end Gate1B.SafeExtensions
