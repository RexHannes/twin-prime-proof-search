/-
# Gate 1B safe extension — weighted fixed-`q` sign collapse

Exact arithmetic of the Möbius function on squarefree moduli, and the resulting
factorisation of a routed weighted sum over the prime divisors of `q`.

No analytic input; no Gate closure.
-/
import Mathlib

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace Gate1B.SafeExtensions

/-- On a squarefree modulus, removing one prime factor flips the sign of the Möbius
function: `μ(q/p) = −μ(q)`. -/
theorem squarefree_moebius_remove_prime (q p : ℕ) (hq : Squarefree q) (hp : p.Prime)
    (hdvd : p ∣ q) : μ (q / p) = - μ q := by
  obtain ⟨k, rfl⟩ := hdvd
  have hpk : Nat.Coprime p k := by
    rcases Nat.coprime_or_dvd_of_prime hp k with h | h
    · exact h
    · exfalso
      obtain ⟨j, rfl⟩ := h
      exact hp.not_isUnit (hq p ⟨j, by ring⟩)
  rw [Nat.mul_div_cancel_left _ hp.pos, isMultiplicative_moebius.map_mul_of_coprime hpk,
    moebius_apply_prime hp]
  ring

/-- **Fixed-`q` weighted sign collapse.**  For squarefree `q` and any finite routed weight
`f` on the prime divisors of `q`,
`∑_{p ∣ q} μ(q/p) f p = −μ(q) ∑_{p ∣ q} f p`. -/
theorem fixedQ_weightedSignCollapse (q : ℕ) (hq : Squarefree q) (f : ℕ → ℝ) :
    ∑ p ∈ q.primeFactors, (μ (q / p) : ℝ) * f p
      = -(μ q : ℝ) * ∑ p ∈ q.primeFactors, f p := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
  rw [squarefree_moebius_remove_prime q p hq hpp hdvd]
  push_cast
  ring

/-- The squarefree hypothesis is load-bearing: for `q = 4`, `p = 2` one has
`μ(q/p) = −1` but `−μ(q) = 0`. -/
theorem squarefree_hypothesis_load_bearing :
    μ (4 / 2) ≠ - μ 4 := by
  simp [show (4 : ℕ) / 2 = 2 from rfl, moebius_apply_prime Nat.prime_two,
    moebius_eq_zero_of_not_squarefree (by decide : ¬ Squarefree 4)]

end Gate1B.SafeExtensions
