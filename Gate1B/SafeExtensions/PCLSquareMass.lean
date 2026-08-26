/-
# Gate 1B safe extension — the finite Euler identity behind the PCL core square mass

Exact finite rational arithmetic.  **No** `X^o(1)` statement, no divisor-bound
asymptotics, no prime-counting input: the final product is *not* claimed to be
`X^o(1)` anywhere in this file.

For a finite set `S` of primes and the local factors

    f_p(N) = 1/p − 1_{p ∣ N},

we bank

* `subsetProductSquareSum_eq_eulerProduct` — `∑_{T ⊆ S} ∏_{p ∈ T} f_p(N)^2
  = ∏_{p ∈ S} (1 + f_p(N)^2)`;
* `pclCoreSquareMass_factorization` — the split of the Euler product into the
  `p ∣ N` and `p ∤ N` parts;
* `pclCoreSquareMass_finiteBound` — the exact finite bound
  `∏_{p ∈ S} (1 + f_p(N)^2) ≤ 2^{#{p ∈ S : p ∣ N}} ∏_{p ∈ S, p ∤ N} (1 + 1/p²)`.
-/
import Mathlib

namespace Gate1B.SafeExtensions

open Finset

/-- Local PCL factor `f_p(N) = 1/p − 1_{p ∣ N}`, over the rationals. -/
def pclLocal (p N : ℕ) : ℚ := 1 / p - (if p ∣ N then 1 else 0)

theorem pclLocal_of_not_dvd {p N : ℕ} (h : ¬ p ∣ N) : pclLocal p N = 1 / p := by
  simp [pclLocal, h]

theorem pclLocal_of_dvd {p N : ℕ} (h : p ∣ N) : pclLocal p N = 1 / p - 1 := by
  simp [pclLocal, h]

/-- **Finite subset / Euler identity.**  Summing the squared local factors over
all subsets of `S` is exactly the Euler product `∏ (1 + f_p²)`. -/
theorem subsetProductSquareSum_eq_eulerProduct (S : Finset ℕ) (N : ℕ) :
    ∑ T ∈ S.powerset, ∏ p ∈ T, (pclLocal p N) ^ 2
      = ∏ p ∈ S, (1 + (pclLocal p N) ^ 2) := by
  have h := Finset.prod_add (f := fun p => (pclLocal p N) ^ 2) (g := fun _ => (1 : ℚ)) (s := S)
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun p _ => by ring

/-- **Square-mass factorisation.**  Split the Euler product according to
`p ∣ N` or `p ∤ N`. -/
theorem pclCoreSquareMass_factorization (S : Finset ℕ) (N : ℕ) :
    ∏ p ∈ S, (1 + (pclLocal p N) ^ 2)
      = (∏ p ∈ S.filter (fun p => p ∣ N), (1 + (1 / (p : ℚ) - 1) ^ 2)) *
        ∏ p ∈ S.filter (fun p => ¬ p ∣ N), (1 + (1 / (p : ℚ)) ^ 2) := by
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p ∣ N)]
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by
      rw [pclLocal_of_dvd (Finset.mem_filter.mp hp).2]
  · exact Finset.prod_congr rfl fun p hp => by
      rw [pclLocal_of_not_dvd (Finset.mem_filter.mp hp).2]

/-- **Finite square-mass bound.**  With every `p ∈ S` at least `1`,

    ∏_{p ∈ S} (1 + f_p(N)²) ≤ 2^{#{p ∈ S : p ∣ N}} · ∏_{p ∈ S, p ∤ N} (1 + 1/p²).

This is an exact finite inequality; **no** claim is made that the right-hand
side is `X^{o(1)}`. -/
theorem pclCoreSquareMass_finiteBound (S : Finset ℕ) (N : ℕ) (hS : ∀ p ∈ S, 1 ≤ p) :
    ∏ p ∈ S, (1 + (pclLocal p N) ^ 2)
      ≤ 2 ^ ((S.filter (fun p => p ∣ N)).card) *
        ∏ p ∈ S.filter (fun p => ¬ p ∣ N), (1 + (1 / (p : ℚ)) ^ 2) := by
  rw [pclCoreSquareMass_factorization S N]
  have hnn : (0 : ℚ) ≤ ∏ p ∈ S.filter (fun p => ¬ p ∣ N), (1 + (1 / (p : ℚ)) ^ 2) :=
    Finset.prod_nonneg fun p _ => by positivity
  refine mul_le_mul_of_nonneg_right ?_ hnn
  have hbound : ∀ p ∈ S.filter (fun p => p ∣ N), (1 + (1 / (p : ℚ) - 1) ^ 2) ≤ 2 := by
    intro p hp
    have hp1 : 1 ≤ p := hS p (Finset.mem_filter.mp hp).1
    have hpQ : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp1
    have h0 : (0 : ℚ) < (p : ℚ) := lt_of_lt_of_le zero_lt_one hpQ
    have hle : 1 / (p : ℚ) ≤ 1 := by
      rw [div_le_one h0]; exact hpQ
    have hge : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    nlinarith [hle, hge]
  calc (∏ p ∈ S.filter (fun p => p ∣ N), (1 + (1 / (p : ℚ) - 1) ^ 2))
      ≤ ∏ _p ∈ S.filter (fun p => p ∣ N), (2 : ℚ) :=
        Finset.prod_le_prod (fun p _ => by positivity) hbound
    _ = 2 ^ ((S.filter (fun p => p ∣ N)).card) := by rw [Finset.prod_const]

end Gate1B.SafeExtensions
