/-
# Gate 1B safe algebra bank — §10: the CRT product over four labelled primes.

For pairwise coprime `sᵢ` and `u = s₁ s₂ s₃ s₄`,

  `u² ∣ D  ↔  ∀ i, sᵢ² ∣ D`,

and, combined with the local prime-square lift, the exact four-local-collision
equivalence.

**No independence between the four local conditions is inferred.**  The last
theorem of this file is an explicit finite guard against that inference.
-/
import Gate1B.PrimeSquareLift

namespace Gate1B

open Finset

/-- Multiplicativity of a square divisibility along a pairwise-coprime family. -/
theorem prod_sq_dvd_iff {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) (D : ℤ)
    (hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j)) :
    ((∏ i ∈ s, f i) ^ 2 ∣ D) ↔ ∀ i ∈ s, (f i) ^ 2 ∣ D := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hco' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j) := by
        intro i hi j hj hij
        exact hco i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij
      have hcoa : IsCoprime (f a) (∏ i ∈ s, f i) := by
        refine IsCoprime.prod_right ?_
        intro i hi
        exact hco a (mem_insert_self a s) i (mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
      rw [Finset.prod_insert ha, mul_pow]
      constructor
      · intro h i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact dvd_trans ⟨(∏ i ∈ s, f i) ^ 2, rfl⟩ h
        · exact (ih hco').mp (dvd_trans ⟨(f a) ^ 2, by ring⟩ h) i hi
      · intro h
        refine IsCoprime.mul_dvd hcoa.pow (h a (mem_insert_self a s)) ?_
        exact (ih hco').mpr fun i hi => h i (mem_insert_of_mem hi)

/-- Distinct primes give coprime integers. -/
theorem isCoprime_of_distinct_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsCoprime (p : ℤ) (q : ℤ) :=
  Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)

/-- **§10, four labelled primes.**  With `u = s₀ s₁ s₂ s₃` for pairwise distinct
primes, `u² ∣ D ↔ sᵢ² ∣ D` for all `i`. -/
theorem four_prime_sq_dvd_iff (s : Fin 4 → ℕ) (hp : ∀ i, (s i).Prime)
    (hinj : Function.Injective s) (D : ℤ) :
    ((∏ i, (s i : ℤ)) ^ 2 ∣ D) ↔ ∀ i, ((s i : ℤ)) ^ 2 ∣ D := by
  have hco : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      i ≠ j → IsCoprime ((s i : ℤ)) ((s j : ℤ)) := by
    intro i _ j _ hij
    exact isCoprime_of_distinct_primes (hp i) (hp j) (fun h => hij (hinj h))
  simpa using prod_sq_dvd_iff (Finset.univ : Finset (Fin 4)) (fun i => (s i : ℤ)) D hco

/-- **Exact four-local-collision equivalence.**  Combining `§10` with
`LOCAL-LIFT`: for `u = s₀ s₁ s₂ s₃` (pairwise distinct primes), with local
inverses and local coordinates at each place,

  `u² ∣ D  ↔  ∀ i, x₁ᵢ ≡ x₂ᵢ (mod sᵢ)`. -/
theorem four_local_collision {q1 q2 l1 l2 : ℤ} (s : Fin 4 → ℕ) (hp : ∀ i, (s i).Prime)
    (hinj : Function.Injective s) (l1' l2' x1 x2 : Fin 4 → ℤ)
    (hinv1 : ∀ i, ((s i : ℤ)) ^ 2 ∣ (l1 * l1' i - 1))
    (hinv2 : ∀ i, ((s i : ℤ)) ^ 2 ∣ (l2 * l2' i - 1))
    (hq1 : ∀ i, ((s i : ℤ)) ^ 2 ∣ (q1 - (2 * l1' i + (s i : ℤ) * x1 i)))
    (hq2 : ∀ i, ((s i : ℤ)) ^ 2 ∣ (q2 - (2 * l2' i + (s i : ℤ) * x2 i))) :
    ((∏ i, (s i : ℤ)) ^ 2 ∣ C45defect q1 q2 l1 l2) ↔ ∀ i, ((s i : ℤ)) ∣ (x1 i - x2 i) := by
  rw [four_prime_sq_dvd_iff s hp hinj]
  constructor
  · intro h i
    have hs : ((s i : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr (hp i).ne_zero
    exact (local_prime_square_lift hs (hinv1 i) (hinv2 i) (hq1 i) (hq2 i)).mp (h i)
  · intro h i
    have hs : ((s i : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr (hp i).ne_zero
    exact (local_prime_square_lift hs (hinv1 i) (hinv2 i) (hq1 i) (hq2 i)).mpr (h i)

/-! ## Guard: no independence is inferred -/

/-- Anti-independence guard.  The CRT factorisation is a statement about
*divisibility*, not about probabilities: conditions of density `1/2` each may
have conjunction of density `1/2`, not `1/4`.  Nothing in this file licenses
multiplying the four local densities. -/
theorem local_conditions_not_independent :
    ∃ A B : Finset (Fin 2),
      ((A.card : ℚ) / 2 = 1 / 2) ∧ ((B.card : ℚ) / 2 = 1 / 2) ∧
      (((A ∩ B).card : ℚ) / 2 ≠ (1 / 2) * (1 / 2)) := by
  refine ⟨{0}, {0}, by norm_num, by norm_num, ?_⟩
  norm_num

end Gate1B
