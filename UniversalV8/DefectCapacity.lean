/-
# UniversalV8 Module J — defect capacity

Elementary multiplicative arithmetic.  A defect `D > 0` divisible by a product of
pairwise coprime moduli each of size at least `Y ≥ 2` can only carry `log D / log Y`
of them.

This says NOTHING about source-weighted Gram congestion; it is a divisibility bound.
-/
import Mathlib

open Finset

namespace UniversalV8

/-- A product of pairwise coprime numbers, each dividing `D`, divides `D`. -/
theorem nat_prod_dvd_of_pairwiseCoprime {ι : Type*} [DecidableEq ι] (I : Finset ι) (m : ι → ℕ)
    (D : ℕ) (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (m i) (m j))
    (hdvd : ∀ i ∈ I, m i ∣ D) : (∏ i ∈ I, m i) ∣ D := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hs : (∏ i ∈ s, m i) ∣ D :=
        ih (fun i hi j hj hij => hcop i (by simp [hi]) j (by simp [hj]) hij)
          (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))
      have hca : Nat.Coprime (m a) (∏ i ∈ s, m i) :=
        Nat.Coprime.prod_right fun i hi =>
          hcop a (by simp) i (by simp [hi]) (by rintro rfl; exact ha hi)
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hca (hdvd a (by simp)) hs

/-- `defectValuation_product_le`: a divisor of a positive defect is at most the defect. -/
theorem defectValuation_product_le {ι : Type*} (I : Finset ι) (m : ι → ℕ) (D : ℕ)
    (hD : 0 < D) (hdvd : (∏ i ∈ I, m i) ∣ D) : (∏ i ∈ I, m i) ≤ D :=
  Nat.le_of_dvd hD hdvd

/-- **Defect capacity, exponent-one form.**  If `∏_{i ∈ I} m i ∣ D`, `D > 0` and every
`m i ≥ Y`, then `Y ^ |I| ≤ D`.

Pairwise coprimality is NOT needed in this form: it is only needed to deduce the
divisibility hypothesis from `m i ∣ D` for each `i`
(see `pow_card_le_of_pairwiseCoprime_product_dvd`). -/
theorem defectCapacity {ι : Type*} (I : Finset ι) (m : ι → ℕ) (D Y : ℕ)
    (hD : 0 < D) (hY : ∀ i ∈ I, Y ≤ m i) (hdvd : (∏ i ∈ I, m i) ∣ D) :
    Y ^ I.card ≤ D := by
  calc Y ^ I.card = ∏ _i ∈ I, Y := by rw [Finset.prod_const]
    _ ≤ ∏ i ∈ I, m i := Finset.prod_le_prod' hY
    _ ≤ D := Nat.le_of_dvd hD hdvd

/-- Defect capacity from pairwise coprime moduli each dividing the defect. -/
theorem pow_card_le_of_pairwiseCoprime_product_dvd {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (m : ι → ℕ) (D Y : ℕ) (hD : 0 < D) (hY : ∀ i ∈ I, Y ≤ m i)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (m i) (m j))
    (hdvd : ∀ i ∈ I, m i ∣ D) : Y ^ I.card ≤ D :=
  defectCapacity I m D Y hD hY (nat_prod_dvd_of_pairwiseCoprime I m D hcop hdvd)

/-- **Defect capacity with exponents.**  If `∏ m i ^ a i ∣ D` and `m i ≥ Y`, then
`Y ^ (∑ a i) ≤ D`. -/
theorem defectCapacity_pow {ι : Type*} (I : Finset ι) (m a : ι → ℕ) (D Y : ℕ)
    (hD : 0 < D) (hY : ∀ i ∈ I, Y ≤ m i) (hdvd : (∏ i ∈ I, m i ^ a i) ∣ D) :
    Y ^ (∑ i ∈ I, a i) ≤ D := by
  calc Y ^ (∑ i ∈ I, a i) = ∏ i ∈ I, Y ^ a i := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ i ∈ I, m i ^ a i := Finset.prod_le_prod' fun i hi => Nat.pow_le_pow_left (hY i hi) _
    _ ≤ D := Nat.le_of_dvd hD hdvd

/-- Logarithmic corollary: `|I| log Y ≤ log D`. -/
theorem defectCapacity_log {ι : Type*} (I : Finset ι) (m : ι → ℕ) (D Y : ℕ)
    (hD : 0 < D) (hY2 : 2 ≤ Y) (hY : ∀ i ∈ I, Y ≤ m i) (hdvd : (∏ i ∈ I, m i) ∣ D) :
    (I.card : ℝ) * Real.log Y ≤ Real.log D := by
  have h := defectCapacity I m D Y hD hY hdvd
  have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hY2
  have hcast : ((Y : ℝ)) ^ I.card ≤ (D : ℝ) := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hcast
  rwa [Real.log_pow] at hlog

end UniversalV8
