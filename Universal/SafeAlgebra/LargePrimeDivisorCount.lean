/-
# Universal v8.4 — large-prime divisor capacity

**Status: PROVED_FINITE (generic lemma) + CAPACITY_ONLY (Gate 1B reading).**

Generic finite lemma: if `s` is a finite set of distinct primes, each at least
`V`, whose product divides a nonzero `M`, then `V ^ |s| ≤ M`.  Contrapositive:
if `V ^ k > M` then fewer than `k` such primes divide `M`.

No asymptotics are used and none are claimed.  The Gate 1B reading — with
`|M| ≤ Y ^ 9 X^{o(1)}` and the lane-E exponent `> 2` for `V` this gives `O(1)`
admissible large-prime divisors — is recorded as rational-exponent capacity
bookkeeping (`largePrime_capacity_exponent`), *not* as a literal asymptotic
theorem.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

/-- **Large-prime divisor count.**  Distinct primes `≥ V` whose product divides
`M ≠ 0` force `V ^ |s| ≤ M`. -/
theorem largePrime_pow_card_le {V M : ℕ} {s : Finset ℕ} (hM : M ≠ 0)
    (hV : ∀ p ∈ s, V ≤ p) (hdvd : (∏ p ∈ s, p) ∣ M) :
    V ^ s.card ≤ M := by
  have h1 : V ^ s.card ≤ ∏ p ∈ s, p := by
    calc V ^ s.card = ∏ _p ∈ s, V := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ s, p := Finset.prod_le_prod' hV
  exact h1.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hdvd)

/-- **Capacity contrapositive.**  If `V ^ k > M` then any set of distinct primes
`≥ V` dividing `M` has fewer than `k` elements. -/
theorem largePrime_card_lt {V M k : ℕ} {s : Finset ℕ} (hM : M ≠ 0)
    (hV : ∀ p ∈ s, V ≤ p) (hdvd : (∏ p ∈ s, p) ∣ M) (hk : M < V ^ k) :
    s.card < k := by
  by_contra hcon
  push_neg at hcon
  have hV1 : 1 ≤ V := by
    rcases Nat.eq_zero_or_pos V with rfl | h
    · rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [pow_zero] at hk; omega
      · rw [Nat.zero_pow hkpos] at hk; omega
    · exact h
  have hmono : V ^ k ≤ V ^ s.card := Nat.pow_le_pow_right hV1 hcon
  have := largePrime_pow_card_le hM hV hdvd
  omega

/-- Gate 1B exponent reading (base `Y`, CAPACITY_ONLY): five primes of exponent
`> 2` already exceed the source-mass exponent `9`, so at most four large prime
divisors are admissible at natural scale. -/
theorem largePrime_five_exceeds_nine {vexp : ℚ} (hv : 2 < vexp) : (9 : ℚ) < 5 * vexp := by
  linarith

/-- The finite counterpart of the exponent reading: if the source mass `M` is
below `V ^ 5`, at most four distinct primes `≥ V` can divide it. -/
theorem largePrime_capacity_bound {V M : ℕ} {s : Finset ℕ} (hM : M ≠ 0)
    (hV : ∀ p ∈ s, V ≤ p) (hdvd : (∏ p ∈ s, p) ∣ M) (hmass : M < V ^ 5) :
    s.card < 5 := largePrime_card_lt hM hV hdvd hmass

end Universal.SafeAlgebra
