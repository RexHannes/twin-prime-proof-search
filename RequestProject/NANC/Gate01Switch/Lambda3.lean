import RequestProject.NANC.Gate01Switch.ResidueMinusTwo

/-!
# Gate01Switch: the exact `λ₃` weight

The switched branch uses **the archive's own** high-high modulus weight
`TwinPrimeProject.lambda3` from `RequestProject/VaughanPacketAlgebra.lean`:

`λ₃(U,V;q) = ∑_{d ∣ q, U < d, V < q/d} μ(d) Λ(q/d)`,

with codomain `ℝ` and Mathlib's `ArithmeticFunction.moebius` /
`ArithmeticFunction.vonMangoldt`.  **No second `lambda3` is introduced.**

Contents:

* `lambda3_term_support` — the exact support conditions of a contributing
  divisor, including `d * (q/d) = q`;
* `lambda3_eq_sum_over_ell` — the reindexing `d ↦ ℓ = q/d`;
* `lambda3_primePow` — the prime-power expansion (L3-PP): only prime powers
  `ℓ = p^ν` with `ℓ > V` and `q/ℓ > U` contribute;
* `lambda3_squarefree` — the squarefree specialization (L3-SF)
  `λ₃(U,V;q) = -μ(q) ∑_{p ∣ q, p > V, q/p > U} log p`.

The von Mangoldt values are Mathlib's real-valued `Λ`, so `Λ(p^ν) = log p`
holds on the nose (`vonMangoldt_apply_prime` at `ν = 1`); no fake `log p` is
invented anywhere.  A single `q` may well have several admissible `p`, and the
squarefree formula is a genuine *sum* over them, not a single term.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open ArithmeticFunction Finset

/-! ## Support -/

/-- The exact support conditions on a contributing divisor of `λ₃`. -/
theorem lambda3_term_support {U V q d : ℕ} (hd : d ∈ q.divisors)
    (hne : (if U < d ∧ V < q / d then (moebius d : ℝ) * Λ (q / d) else 0) ≠ 0) :
    d ∣ q ∧ q ≠ 0 ∧ U < d ∧ V < q / d ∧ d * (q / d) = q := by
  rw [Nat.mem_divisors] at hd
  by_cases h : U < d ∧ V < q / d
  · exact ⟨hd.1, hd.2, h.1, h.2, Nat.mul_div_cancel' hd.1⟩
  · exact absurd (if_neg h) hne

/-- Only divisors of `q` contribute; the complementary terms vanish. -/
theorem lambda3_eq_zero_of_zero (U V : ℕ) : lambda3 U V 0 = 0 := by
  simp [lambda3]

/-! ## Reindexing by the cofactor -/

/-- Reindexing `d ↦ ℓ = q/d` in the definition of `λ₃`. -/
theorem lambda3_eq_sum_over_ell (U V q : ℕ) :
    lambda3 U V q =
      ∑ l ∈ q.divisors, if V < l ∧ U < q / l then (moebius (q / l) : ℝ) * Λ l else 0 := by
  have h1 := Nat.sum_divisorsAntidiagonal
    (n := q) (fun d l => if U < d ∧ V < l then (moebius d : ℝ) * Λ l else 0)
  have h2 := Nat.sum_divisorsAntidiagonal'
    (n := q) (fun d l => if U < d ∧ V < l then (moebius d : ℝ) * Λ l else 0)
  rw [lambda3, ← h1, h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : U < q / l ∧ V < l
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hc => h ⟨hc.2, hc.1⟩)]

/-! ## Prime-power expansion (L3-PP) -/

/-- **(L3-PP)** — the prime-power expansion.  Only prime powers `ℓ = p^ν`
dividing `q` with `ℓ > V` and `q/ℓ > U` contribute, with weight
`μ(q/ℓ) Λ(ℓ) = μ(q/p^ν) log p`. -/
theorem lambda3_primePow (U V q : ℕ) :
    lambda3 U V q =
      ∑ l ∈ q.divisors.filter (fun l => IsPrimePow l ∧ V < l ∧ U < q / l),
        (moebius (q / l) : ℝ) * Λ l := by
  rw [lambda3_eq_sum_over_ell, ← Finset.sum_filter]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hpp : IsPrimePow l
  · by_cases h : V < l ∧ U < q / l <;> simp [hpp, h]
  · have hz : Λ l = 0 := vonMangoldt_eq_zero_iff.mpr hpp
    by_cases h : V < l ∧ U < q / l <;> simp [hpp, h, hz]

/-! ## Squarefree specialization (L3-SF) -/

/-- A prime power dividing a squarefree number is prime. -/
theorem prime_of_isPrimePow_dvd_squarefree {q l : ℕ} (hq : Squarefree q) (hl : l ∣ q)
    (hpp : IsPrimePow l) : l.Prime := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hpp
  have hprime : Nat.Prime p := hp.nat_prime
  rcases Nat.lt_or_ge k 2 with h | h
  · have : k = 1 := by omega
    simpa [this] using hprime
  · exfalso
    have hdvd : p ^ 2 ∣ q := dvd_trans (pow_dvd_pow p h) hl
    have := hq p (by simpa [pow_two] using hdvd)
    exact hprime.one_lt.ne' (Nat.isUnit_iff.mp this)

/-- For squarefree `q` and a prime `p ∣ q`, `μ(q/p) = -μ(q)`. -/
theorem moebius_div_prime_of_squarefree {q p : ℕ} (hq : Squarefree q) (hp : p.Prime)
    (hd : p ∣ q) : moebius (q / p) = -moebius q := by
  obtain ⟨k, rfl⟩ := hd
  have hk : p * k / p = k := Nat.mul_div_cancel_left _ hp.pos
  rw [hk]
  have hcop : Nat.Coprime p k := by
    rcases Nat.coprime_or_dvd_of_prime hp k with h | h
    · exact h
    · exfalso
      obtain ⟨j, rfl⟩ := h
      have := hq p ⟨j, by ring⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp]
  ring

/-- **(L3-SF)** — the squarefree specialization.  For squarefree `q`,

`λ₃(U,V;q) = -μ(q) ∑_{p ∣ q prime, p > V, q/p > U} log p`.

Several primes `p` may satisfy the two inequalities; the right-hand side is a
genuine sum over all of them. -/
theorem lambda3_squarefree (U V q : ℕ) (hq : Squarefree q) :
    lambda3 U V q =
      -(moebius q : ℝ) *
        ∑ p ∈ q.primeFactors.filter (fun p => V < p ∧ U < q / p), Real.log p := by
  have hq0 : q ≠ 0 := hq.ne_zero
  rw [lambda3_primePow, Finset.mul_sum]
  refine Finset.sum_nbij' (fun l => l) (fun p => p) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Nat.mem_divisors] at hl
    obtain ⟨⟨hdvd, -⟩, hpp, hV, hU⟩ := hl
    have hprime := prime_of_isPrimePow_dvd_squarefree hq hdvd hpp
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hq0⟩, hV, hU⟩
  · intro p hp
    simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hprime, hdvd, -⟩, hV, hU⟩ := hp
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdvd, hq0⟩, hprime.isPrimePow, hV, hU⟩
  · intro l _; rfl
  · intro p _; rfl
  · intro l hl
    simp only [Finset.mem_filter, Nat.mem_divisors] at hl
    obtain ⟨⟨hdvd, -⟩, hpp, -, -⟩ := hl
    have hprime := prime_of_isPrimePow_dvd_squarefree hq hdvd hpp
    rw [vonMangoldt_apply_prime hprime, moebius_div_prime_of_squarefree hq hprime hdvd]
    push_cast
    ring

end Gate01Switch
end TwinPrimeProject
