import Mathlib

namespace NANC

/-- Congruence-level two-block CRT phase decomposition.  `E₁,E₂` are the two
CRT idempotent weights; the two middle hypotheses are precisely the local
phase congruences after multiplication by the full modulus. -/
theorem crt_phase_two_block_congruence (n : ℕ) (v q rp x y E₁ E₂ : ZMod n)
    (hpartition : E₁ + E₂ = 1)
    (hleft : v * E₁ = -2 * q * x)
    (hright : v * E₂ = -2 * rp * y) :
    v = -2 * q * x + -2 * rp * y := by
  calc
    v = v * E₁ + v * E₂ := by rw [← mul_add, hpartition, mul_one]
    _ = _ := by rw [hleft, hright]

/-- The corresponding prime split: complementary CRT weights split a phase
numerator into its `r` and `p` local pieces. -/
theorem crt_phase_prime_split_congruence (n : ℕ) (x ep er : ZMod n)
    (hsplit : ep + er = 1) : x = x * ep + x * er := by
  rw [← mul_add, hsplit, mul_one]

end NANC
