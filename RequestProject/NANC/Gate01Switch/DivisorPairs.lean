import RequestProject.NANC.Gate01Switch.SwitchedOperator

/-!
# Gate01Switch: SW1 → SW2, opening the divisor convolution

The generic finite lemma is `sum_lambda3_mul_eq_divisorPairs`:

`∑_{q ∈ Qset} λ₃(U,V;q) F(q) = ∑_{d>U, ℓ>V, dℓ ∈ Qset} μ(d) Λ(ℓ) F(dℓ)`,

an exact reindexing of a divisor sum as a sum over divisor *pairs* (the set
`divisorPairs`).  No multiplicity is dropped: `divisorPairs` records the pair
`(d, ℓ)`, not the product.

Specializing `F(q) = ∑_{r ∈ B_q} c(qr-2) - E(q)` gives **(SW2)**.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open ArithmeticFunction Finset

/-- The set of admissible divisor pairs `(d, ℓ)` with `d > U`, `ℓ > V` and
`dℓ ∈ Qset`. -/
def divisorPairs (Qset : Finset ℕ) (U V : ℕ) : Finset (ℕ × ℕ) :=
  Qset.biUnion (fun q => q.divisorsAntidiagonal.filter (fun x => U < x.1 ∧ V < x.2))

theorem mem_divisorPairs {Qset : Finset ℕ} {U V : ℕ} {x : ℕ × ℕ} :
    x ∈ divisorPairs Qset U V ↔
      U < x.1 ∧ V < x.2 ∧ x.1 * x.2 ∈ Qset ∧ x.1 * x.2 ≠ 0 := by
  simp only [divisorPairs, Finset.mem_biUnion, Finset.mem_filter,
    Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨q, hq, ⟨hprod, hne⟩, hU, hV⟩
    exact ⟨hU, hV, hprod ▸ hq, hprod ▸ hne⟩
  · rintro ⟨hU, hV, hmem, hne⟩
    exact ⟨x.1 * x.2, hmem, ⟨rfl, hne⟩, hU, hV⟩

/-- `λ₃` at `q`, times a value, as a sum over the divisor antidiagonal of `q`. -/
theorem lambda3_mul_eq_antidiagonal (U V q : ℕ) (F : ℕ → ℝ) :
    lambda3 U V q * F q =
      ∑ x ∈ q.divisorsAntidiagonal.filter (fun x => U < x.1 ∧ V < x.2),
        (moebius x.1 : ℝ) * Λ x.2 * F (x.1 * x.2) := by
  rw [Finset.sum_filter]
  have h := Nat.sum_divisorsAntidiagonal (n := q)
    (fun d l => if U < d ∧ V < l then (moebius d : ℝ) * Λ l * F (d * l) else 0)
  rw [h, lambda3, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hmul : d * (q / d) = q := Nat.mul_div_cancel' hdvd
  by_cases hc : U < d ∧ V < q / d
  · rw [if_pos hc, if_pos hc, hmul]
  · rw [if_neg hc, if_neg hc, zero_mul]

/-- **The generic finite opening lemma.**  Exact reindexing of a `λ₃`-weighted
sum as a sum over divisor pairs. -/
theorem sum_lambda3_mul_eq_divisorPairs (Qset : Finset ℕ) (U V : ℕ) (F : ℕ → ℝ) :
    ∑ q ∈ Qset, lambda3 U V q * F q =
      ∑ x ∈ divisorPairs Qset U V, (moebius x.1 : ℝ) * Λ x.2 * F (x.1 * x.2) := by
  rw [divisorPairs, Finset.sum_biUnion]
  · exact Finset.sum_congr rfl fun q _ => lambda3_mul_eq_antidiagonal U V q F
  · intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter,
      Nat.mem_divisorsAntidiagonal]
    rintro x ⟨⟨rfl, -⟩, -⟩ ⟨⟨h2, -⟩, -⟩
    exact hab h2

/-! ## (SW2) -/

/-- The `μΛ`-weighted sum of an arbitrary finite weight over a set of divisor
pairs.  Every switched stratum below is one of these. -/
noncomputable def pairSum (S : Finset (ℕ × ℕ)) (G : ℕ → ℕ → ℝ) : ℝ :=
  ∑ x ∈ S, (moebius x.1 : ℝ) * Λ x.2 * G x.1 x.2

/-- The coefficient weight `(d, ℓ) ↦ ∑_{r ∈ B_{dℓ}} c(dℓr - 2)`. -/
noncomputable def coeffWeight (K : ℕ) (c : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun d l => ∑ r ∈ multiplierSet K (d * l), c (d * l * r - 2)

/-- The expected-term weight `(d, ℓ) ↦ E(dℓ)`. -/
def expectedWeight (E : ℕ → ℝ) : ℕ → ℕ → ℝ := fun d l => E (d * l)

/-- The `c`-part of SW2: the fully opened switched main sum. -/
noncomputable def switchedSW2Coefficient (Qset : Finset ℕ) (U V K : ℕ) (c : ℕ → ℝ) : ℝ :=
  pairSum (divisorPairs Qset U V) (coeffWeight K c)

/-- The `E`-part of SW2: the fully opened expected term. -/
noncomputable def switchedSW2Expected (Qset : Finset ℕ) (U V : ℕ) (E : ℕ → ℝ) : ℝ :=
  pairSum (divisorPairs Qset U V) (expectedWeight E)

/-- **(SW2)** — the exact fully opened form of the switched operator. -/
theorem switchedOperator_eq_SW2 {Qset : Finset ℕ} (U V K : ℕ) (c E : ℕ → ℝ)
    (hQ : ∀ q ∈ Qset, 0 < q) :
    switchedOperator Qset U V K c E =
      switchedSW2Coefficient Qset U V K c - switchedSW2Expected Qset U V E := by
  rw [switchedOperator_eq_multiplier U V K c E hQ,
    sum_lambda3_mul_eq_divisorPairs Qset U V
      (fun q => (∑ r ∈ multiplierSet K q, c (q * r - 2)) - E q),
    switchedSW2Coefficient, switchedSW2Expected, pairSum, pairSum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by simp only [coeffWeight, expectedWeight]; ring

end Gate01Switch
end TwinPrimeProject
