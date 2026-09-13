/-
# Gate1B / R11 / Frontier : complement-threshold high-fibre lemmas

Append-only module of the minimal-gap-kernel delta.  These are the exact reusable lemmas of the
hybrid (complement-threshold) run; the minimal-kernel coordinate is now preferred, but they stay
banked and kernel-checked.

With `√M < D < M` and `K = M/D` — encoded here by the finite hypothesis `M ≤ D·K` — we prove:

* every divisor `d > D` of `M` carries the **full** `p`-adic power of `M` for every prime
  `p > K`;
* `p > K` and `p² | M` force `H_D(M) = 0`;
* two large primes `M = p·q·m`, `K < p`, `K < q` give `H_D(M) = H_{D/(pq)}(m)`, hence `Λ(m)`
  under `D < p·q`;
* one large prime `M = p·m` gives `H_D(M) = −H_{D/p}(m)`, together with the exact
  prefix-minus-`Λ` identity.
-/
import Gate1B.R11.Frontier.CompleteDivisorFibre

namespace Gate1B.R11.Frontier

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## 1. Full `p`-adic power in every large divisor -/

/-- **Complement threshold.**  Every divisor above `D` contains the full `p`-adic power of `M`
for every prime `p > K`. -/
theorem full_padic_of_large_divisor {M D K d p : ℕ} (hM : M ≠ 0)
    (hDK : M ≤ D * K) (hd : d ∣ M) (hdD : D < d) (hp : p.Prime) (hpK : K < p) :
    p ^ M.factorization p ∣ d := by
  obtain ⟨c, hc⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; simp at hc; exact hM hc
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hM hc
  have hcK : c < K := by
    have h1 : D * c < d * c := by
      exact Nat.mul_lt_mul_of_lt_of_le hdD (le_refl c) (Nat.pos_of_ne_zero hc0)
    have h2 : d * c ≤ D * K := by rw [← hc]; exact hDK
    have : D * c < D * K := lt_of_lt_of_le h1 h2
    exact lt_of_mul_lt_mul_left this (Nat.zero_le D)
  have hpc : ¬ p ∣ c := by
    intro hdvd
    have : p ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hdvd
    omega
  have hvc : c.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpc
  have hfac : M.factorization p = d.factorization p := by
    rw [hc, Nat.factorization_mul hd0 hc0]
    simp [hvc]
  rw [hfac, Nat.Prime.pow_dvd_iff_le_factorization hp hd0]

/-- A large prime square kills the whole high fibre. -/
theorem Hdiv_eq_zero_of_large_prime_sq {M D K p : ℕ} (hM : M ≠ 0)
    (hDK : M ≤ D * K) (hp : p.Prime) (hpK : K < p) (hp2 : p ^ 2 ∣ M) :
    Hdiv (D : ℝ) M = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Nat.mem_divisors] at hd
  by_cases hz : (D : ℝ) < (d : ℝ)
  · rw [if_pos hz]
    have hdD : D < d := by exact_mod_cast hz
    have hfull := full_padic_of_large_divisor hM hDK hd.1 hdD hp hpK
    have h2le : 2 ≤ M.factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hM).1 hp2
    have hsq : ¬ Squarefree d := by
      intro hsq
      have : p * p ∣ d := by
        refine dvd_trans ?_ hfull
        calc p * p = p ^ 2 := by ring
          _ ∣ p ^ M.factorization p := pow_dvd_pow p h2le
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p this))
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp
  · rw [if_neg hz]

/-! ## 2. Two large primes -/

/-- **Two large primes.**  `H_D(p·q·m) = H_{D/(pq)}(m)`. -/
theorem Hdiv_two_large_primes {D K m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpK : K < p) (hqK : K < q)
    (hcop : Nat.Coprime (p * q) m) (hDK : p * q * m ≤ D * K) :
    Hdiv (D : ℝ) (p * q * m) = Hdiv ((D : ℝ) / ((p * q : ℕ) : ℝ)) m := by
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq.ne_zero
  have hM : p * q * m ≠ 0 := Nat.mul_ne_zero hpq0 hm
  have hsq : Squarefree (p * q) := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨(Nat.coprime_primes hp hq).2 hpq, hp.squarefree, hq.squarefree⟩
  have hforce : ∀ d, d ∣ p * q * m → (D : ℝ) < (d : ℝ) → (μ d : ℝ) ≠ 0 → p * q ∣ d := by
    intro d hd hz _
    have hdD : D < d := by exact_mod_cast hz
    have hfp := full_padic_of_large_divisor hM hDK hd hdD hp hpK
    have hfq := full_padic_of_large_divisor hM hDK hd hdD hq hqK
    have hp1 : 1 ≤ (p * q * m).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp hM ⟨q * m, by ring⟩
    have hq1 : 1 ≤ (p * q * m).factorization q :=
      Nat.Prime.factorization_pos_of_dvd hq hM ⟨p * m, by ring⟩
    have hpd : p ∣ d := dvd_trans (by simpa using pow_dvd_pow p hp1) hfp
    have hqd : q ∣ d := dvd_trans (by simpa using pow_dvd_pow q hq1) hfq
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).2 hpq) hpd hqd
  have hmu : (μ (p * q) : ℝ) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      ((Nat.coprime_primes hp hq).2 hpq)]
    push_cast [ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.moebius_apply_prime hq]
    ring
  rw [Hdiv_forced_fibre hpq0 hm hsq hcop hforce, hmu, one_mul]

/-- Under `D < p·q` the two-large-prime fibre is von Mangoldt. -/
theorem Hdiv_two_large_primes_vonMangoldt {D K m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpK : K < p) (hqK : K < q)
    (hcop : Nat.Coprime (p * q) m) (hDK : p * q * m ≤ D * K) (hDpq : D < p * q) :
    Hdiv (D : ℝ) (p * q * m) = Λ m := by
  rw [Hdiv_two_large_primes hm hp hq hpq hpK hqK hcop hDK]
  refine Hdiv_of_lt_one ?_ m
  have hpos : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero)
  rw [div_lt_one hpos]
  exact_mod_cast hDpq

/-! ## 3. One large prime -/

/-- **One large prime.**  `H_D(p·m) = −H_{D/p}(m)`. -/
theorem Hdiv_one_large_prime {D K m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hpK : K < p) (hcop : Nat.Coprime p m) (hDK : p * m ≤ D * K) :
    Hdiv (D : ℝ) (p * m) = - Hdiv ((D : ℝ) / (p : ℝ)) m := by
  have hM : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm
  have hforce : ∀ d, d ∣ p * m → (D : ℝ) < (d : ℝ) → (μ d : ℝ) ≠ 0 → p ∣ d := by
    intro d hd hz _
    have hdD : D < d := by exact_mod_cast hz
    have hfp := full_padic_of_large_divisor hM hDK hd hdD hp hpK
    have hp1 : 1 ≤ (p * m).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp hM ⟨m, rfl⟩
    exact dvd_trans (by simpa using pow_dvd_pow p hp1) hfp
  rw [Hdiv_forced_fibre hp.ne_zero hm hp.squarefree hcop hforce,
    ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-- The exact prefix-minus-`Λ` identity of the one-large-prime fibre. -/
theorem Hdiv_one_large_prime_prefix {D K m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hpK : K < p) (hcop : Nat.Coprime p m) (hDK : p * m ≤ D * K) :
    Hdiv (D : ℝ) (p * m) = - Λ m +
      ∑ d ∈ m.divisors, (if (D : ℝ) / (p : ℝ) < (d : ℝ) then 0
        else (μ d : ℝ) * Real.log ((m : ℝ) / (d : ℝ))) := by
  rw [Hdiv_one_large_prime hm hp hpK hcop hDK,
    Hdiv_eq_vonMangoldt_sub_prefix ((D : ℝ) / (p : ℝ)) m]
  ring

end Gate1B.R11.Frontier
