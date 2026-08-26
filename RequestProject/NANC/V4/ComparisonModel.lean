/-
NANC V4 — the twin comparison candidate: ALGEBRA ONLY.

We define the local twin factor

    twinLocalFactor C₂ n = 0                                        if n is even
    twinLocalFactor C₂ n = 2 C₂ ∏_{p ∣ n, p > 2} (p-1)/(p-2)        otherwise

and prove only the elementary identities that genuinely follow.  No
prime-number theorem, no progression mean, no singular-series asymptotic is
proved or assumed; those live in `EndgameInterfaces.lean` as UNINHABITED
analytic Props.
-/
import Mathlib
import RequestProject.NANC.V4.Status
import RequestProject.NANC.V4.ShiftedPrimeModel

namespace NANC.V4

open scoped BigOperators

/-- The odd prime divisors of `n`. -/
def oddPrimeFactors (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => 2 < p)

/-- The finite Euler product `∏_{p ∣ n, p odd} (p-1)/(p-2)`. -/
noncomputable def oddPrimeProduct (n : ℕ) : ℝ :=
  ∏ p ∈ oddPrimeFactors n, ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- The twin-prime local (singular-series) factor candidate, with the twin
constant supplied as a parameter `C₂`. -/
noncomputable def twinLocalFactor (C2 : ℝ) (n : ℕ) : ℝ :=
  if 2 ∣ n then 0 else 2 * C2 * oddPrimeProduct n

theorem oddPrimeFactors_prime_gt_two {n p : ℕ} (hp : p ∈ oddPrimeFactors n) :
    p.Prime ∧ 2 < p := by
  simp only [oddPrimeFactors, Finset.mem_filter, Nat.mem_primeFactors] at hp
  exact ⟨hp.1.1, hp.2⟩

theorem oddPrimeProduct_nonneg (n : ℕ) : 0 ≤ oddPrimeProduct n := by
  refine Finset.prod_nonneg ?_
  intro p hp
  obtain ⟨-, hp2⟩ := oddPrimeFactors_prime_gt_two hp
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have h1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

theorem oddPrimeProduct_pos (n : ℕ) : 0 < oddPrimeProduct n := by
  refine Finset.prod_pos ?_
  intro p hp
  obtain ⟨-, hp2⟩ := oddPrimeFactors_prime_gt_two hp
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

/-- Nonnegativity of the comparison local factor, assuming `0 ≤ C₂`. -/
theorem twinLocalFactor_nonneg {C2 : ℝ} (hC : 0 ≤ C2) (n : ℕ) : 0 ≤ twinLocalFactor C2 n := by
  unfold twinLocalFactor
  split
  · exact le_refl 0
  · have := oddPrimeProduct_nonneg n
    positivity

/-- Even-support vanishing. -/
theorem twinLocalFactor_even {C2 : ℝ} {n : ℕ} (h : 2 ∣ n) : twinLocalFactor C2 n = 0 := by
  simp [twinLocalFactor, h]

@[simp] theorem oddPrimeFactors_one : oddPrimeFactors 1 = ∅ := by
  simp [oddPrimeFactors]

@[simp] theorem oddPrimeProduct_one : oddPrimeProduct 1 = 1 := by
  simp [oddPrimeProduct]

/-- Value at `n = 1`. -/
theorem twinLocalFactor_one (C2 : ℝ) : twinLocalFactor C2 1 = 2 * C2 := by
  simp [twinLocalFactor]

/-- Finite-product decomposition: the factor is `2 C₂` times the odd Euler product
whenever `n` is odd. -/
theorem twinLocalFactor_of_odd {C2 : ℝ} {n : ℕ} (h : ¬ 2 ∣ n) :
    twinLocalFactor C2 n = 2 * C2 * oddPrimeProduct n := by
  simp [twinLocalFactor, h]

/-- Multiplying the argument by a new odd prime multiplies the Euler product by
the corresponding local factor. -/
theorem oddPrimeProduct_mul_new_prime {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hp2 : 2 < p)
    (hnp : ¬ p ∣ n) :
    oddPrimeProduct (n * p) = oddPrimeProduct n * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hfac : (n * p).primeFactors = n.primeFactors ∪ {p} := by
    rw [Nat.primeFactors_mul hn hp0, hp.primeFactors]
  have hodd : oddPrimeFactors (n * p) = oddPrimeFactors n ∪ {p} := by
    rw [oddPrimeFactors, hfac, Finset.filter_union, ← oddPrimeFactors]
    congr 1
    simp [hp2]
  have hdisj : Disjoint (oddPrimeFactors n) ({p} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]
    intro hmem
    have : p ∈ n.primeFactors := (Finset.mem_filter.mp hmem).1
    exact hnp (Nat.dvd_of_mem_primeFactors this)
  rw [oddPrimeProduct, hodd, Finset.prod_union hdisj, Finset.prod_singleton, oddPrimeProduct]

/-- The same statement for the full comparison factor. -/
theorem twinLocalFactor_mul_new_prime {C2 : ℝ} {n p : ℕ} (hn : n ≠ 0) (hodd : ¬ 2 ∣ n)
    (hp : p.Prime) (hp2 : 2 < p) (hnp : ¬ p ∣ n) :
    twinLocalFactor C2 (n * p) = twinLocalFactor C2 n * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  have h2 : ¬ 2 ∣ n * p := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
    · exact hodd h'
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h'
      omega
  rw [twinLocalFactor_of_odd h2, twinLocalFactor_of_odd hodd,
    oddPrimeProduct_mul_new_prime hn hp hp2 hnp]
  ring

/-- A shifted-prime comparison model built from a nonnegative "true" weight `a`
and the twin comparison candidate as `b`. -/
noncomputable def twinComparisonModel (C2 : ℝ) (hC : 0 ≤ C2) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) : ShiftedPrimeComparisonModel where
  a := a
  b := twinLocalFactor C2
  w := fun n => a n - twinLocalFactor C2 n
  a_nonneg := ha
  b_nonneg := twinLocalFactor_nonneg hC
  w_eq := fun _ => rfl

end NANC.V4
