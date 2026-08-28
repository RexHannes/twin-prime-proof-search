/-
# Gate 1B v8.4 — the H7 dual determinant shell

**Status: PROVED_FINITE (exact integer arithmetic).**

From the prime congruence `p ∣ m e N - 2` and the projector divisor congruence
`d ∣ m e N - 2`, with `gcd(p, d) = 1`, one gets `p d ∣ m e N - 2`; writing
`n = m e` this is the determinant shell

  `n N - p d ℓ' = 2`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- Coprime divisors multiply: `p ∣ k`, `d ∣ k`, `gcd(p,d) = 1 ⇒ p d ∣ k`. -/
theorem pd_dvd_dualDet {p d k : ℤ} (hp : p ∣ k) (hd : d ∣ k) (hcop : IsCoprime p d) :
    p * d ∣ k := hcop.mul_dvd hp hd

/-- Natural-number form of the same statement. -/
theorem pd_dvd_dualDet_nat {p d k : ℕ} (hp : p ∣ k) (hd : d ∣ k) (hcop : Nat.Coprime p d) :
    p * d ∣ k := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hp hd

/-- **H7 dual determinant shell.**  If `p d ∣ n N - 2` then there is `ℓ'` with
`n N - p d ℓ' = 2`. -/
theorem h7_dualDet_shell {p d n N : ℤ} (h : p * d ∣ n * N - 2) :
    ∃ ell : ℤ, n * N - p * d * ell = 2 := by
  obtain ⟨ell, hell⟩ := h
  exact ⟨ell, by linarith [hell]⟩

/-- The shell assembled directly from the two congruences, with `n = m e`. -/
theorem h7_dualDet_shell_of_congruences {p d m e N : ℤ}
    (hp : p ∣ m * e * N - 2) (hd : d ∣ m * e * N - 2) (hcop : IsCoprime p d) :
    ∃ ell : ℤ, (m * e) * N - p * d * ell = 2 := by
  refine h7_dualDet_shell (n := m * e) ?_
  have : (m * e) * N - 2 = m * e * N - 2 := by ring
  rw [this]
  exact pd_dvd_dualDet hp hd hcop

end Gate1B.SafeAlgebra
