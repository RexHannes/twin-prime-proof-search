/-
# Universal / D0WP — clean-unit arithmetic

**Status of this module: KERNEL_PROVED elementary arithmetic.**

The provider needs, for the outer product `N` and a modulus `q` dividing `N+2`,
that `N` is a unit modulo `q`.  This is true exactly because the shift is the
fixed shift `2` and `q` is odd: a common prime divisor of `q` and `N` would
divide `2` and be odd.

The even branch is *not* proved here and is not silently merged: it is typed
separately as a local / parity branch (`TwoAdicBranch`), exactly as the source
architecture requires.  Nothing in this module averages over the shift.
-/
import Mathlib

namespace Universal.D0WP

/-- **CLEAN UNIT (kernel-proved).**  If `q ∣ N + 2` and `q` is odd then
`gcd(q, N) = 1`. -/
theorem coprime_of_dvd_add_two_of_odd {q N : ℕ} (hq : q ∣ N + 2) (hodd : ¬ 2 ∣ q) :
    Nat.Coprime q N := by
  by_contra hcop
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hcop
  have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_left q N)
  have hpN : p ∣ N := hpg.trans (Nat.gcd_dvd_right q N)
  have hp2 : p ∣ 2 := (Nat.dvd_add_right hpN).mp (hpq.trans hq)
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
  exact hodd (this ▸ hpq)

/-- The clean-unit corollary in the form used for source inverses: `N` is
invertible modulo `q`. -/
theorem exists_inverse_of_dvd_add_two_of_odd {q N : ℕ} (hq : q ∣ N + 2) (hodd : ¬ 2 ∣ q) :
    ∃ x : ℤ, (N : ℤ) * x ≡ 1 [ZMOD (q : ℤ)] := by
  have hcop : Nat.Coprime q N := coprime_of_dvd_add_two_of_odd hq hodd
  have hZ : IsCoprime (N : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast, Nat.coprime_comm] using hcop
  obtain ⟨a, b, hab⟩ := hZ
  exact ⟨a, Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨-b, by linarith [hab]⟩)⟩

/-- The two-adic branch is kept separately typed: it is a local / parity object,
never a clean-unit object. -/
inductive TwoAdicBranch (q : ℕ)
  /-- `q` is odd: the clean-unit branch applies. -/
  | cleanUnit (hodd : ¬ 2 ∣ q)
  /-- `q` is even: local / parity handling, no clean-unit claim. -/
  | localParity (heven : 2 ∣ q)

/-- Every modulus lies in exactly one of the two branches; the classification is
decidable and total. -/
def twoAdicBranch (q : ℕ) : TwoAdicBranch q :=
  if h : 2 ∣ q then TwoAdicBranch.localParity h else TwoAdicBranch.cleanUnit h

end Universal.D0WP
