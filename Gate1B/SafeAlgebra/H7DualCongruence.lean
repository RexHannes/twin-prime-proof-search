/-
# Gate 1B v8.4 — the H7 dual congruence

**Status: PROVED_FINITE.**

The prime-character collapse produces the additive frequency `a` and the hybrid
residue transform imposes `m ≡ a c₀ (mod p)`.  Together with the source relation
`a c₀ e N ≡ 2 (mod p)` this yields the exact dual congruence

  `m e N ≡ 2 (mod p)`

with the sign convention of the source (no size estimate is made).
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- **H7 dual prime congruence.**  From `m ≡ a c₀ (mod p)` and
`(a c₀) e N ≡ 2 (mod p)` one gets `m e N ≡ 2 (mod p)`. -/
theorem h7_dual_prime_congruence {p m a c0 e N : ℤ}
    (hres : p ∣ m - a * c0) (hsrc : p ∣ a * c0 * e * N - 2) :
    p ∣ m * e * N - 2 := by
  have hid : m * e * N - 2 = (m - a * c0) * (e * N) + (a * c0 * e * N - 2) := by ring
  rw [hid]
  exact dvd_add (Dvd.dvd.mul_right hres _) hsrc

/-- `ZMod`-flavoured restatement of the same congruence. -/
theorem h7_dual_prime_congruence_zmod {p : ℕ} [NeZero p] {m a c0 e N : ZMod p}
    (hres : m = a * c0) (hsrc : a * c0 * e * N = 2) :
    m * e * N = 2 := by rw [hres]; exact hsrc

end Gate1B.SafeAlgebra
