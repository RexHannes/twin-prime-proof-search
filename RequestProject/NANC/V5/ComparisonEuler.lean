/-
NANC V5 — FINITE SQUAREFREE-DIVISOR EXPANSION, AND THE EULER-PRODUCT INTERFACES.

PROVED HERE (pure finite algebra):

* `prod_one_add_eq_powersetSum` :
      ∏_{p ∈ P} (1 + f p) = ∑_{T ⊆ P} ∏_{p ∈ T} f p
* `oddLocalRatio_eq_one_add` :
      (p-1)/(p-2) = 1 + 1/(p-2)      for a prime p > 2
* `twinLocalFactor_eq_squarefreeDivisorSum` :
      the local factor as a sum over squarefree divisors of the odd prime support
* `twinComparison_mul_argument_expansion` :
      the same after removing the prime factors of a fixed multiplier m
* `oddPrimeProduct_split_at` :
      the multiplicative split of the local factor at a fixed multiplier m

NOT PROVED (uninhabited analytic interfaces):

* the infinite Euler product identity for the twin constant;
* the comparison progression-mean asymptotic.
-/
import Mathlib
import RequestProject.NANC.V5.TwinComparison

namespace NANC.V5

open scoped BigOperators
open NANC.V4

/-! ### Finite squarefree-divisor expansion -/

/-- The elementary expansion `∏_{p ∈ P} (1 + f p) = ∑_{T ⊆ P} ∏_{p ∈ T} f p`:
the finite form of "sum over squarefree divisors of the support". -/
theorem prod_one_add_eq_powersetSum (P : Finset ℕ) (f : ℕ → ℝ) :
    ∏ p ∈ P, (1 + f p) = ∑ T ∈ P.powerset, ∏ p ∈ T, f p := by
  have := Finset.prod_add (f := f) (g := fun _ => (1 : ℝ)) (s := P)
  simpa [add_comm] using this

/-- For a prime `p > 2` the local ratio is `1 + 1/(p-2)`. -/
theorem oddLocalRatio_eq_one_add {p : ℕ} (hp : 2 < p) :
    ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + 1 / ((p : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : ((p : ℝ) - 2) ≠ 0 := by linarith
  field_simp
  ring

/-- The odd Euler product of `n` as a sum over squarefree divisors of its odd
prime support. -/
theorem oddPrimeProduct_eq_squarefreeDivisorSum (n : ℕ) :
    oddPrimeProduct n =
      ∑ T ∈ (oddPrimeFactors n).powerset, ∏ p ∈ T, 1 / ((p : ℝ) - 2) := by
  rw [← prod_one_add_eq_powersetSum]
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact oddLocalRatio_eq_one_add (oddPrimeFactors_prime_gt_two hp).2

/-- **The twin local factor as a squarefree-divisor sum** (odd `n`). -/
theorem twinLocalFactor_eq_squarefreeDivisorSum {C2 : ℝ} {n : ℕ} (h : ¬ 2 ∣ n) :
    twinLocalFactor C2 n =
      2 * C2 * ∑ T ∈ (oddPrimeFactors n).powerset, ∏ p ∈ T, 1 / ((p : ℝ) - 2) := by
  rw [twinLocalFactor_of_odd h, oddPrimeProduct_eq_squarefreeDivisorSum]

/-! ### Removing the prime factors of a fixed multiplier -/

/-- The odd prime factors of `n` that do **not** divide the multiplier `m`. -/
def oddPrimeFactorsAway (m n : ℕ) : Finset ℕ := (oddPrimeFactors n).filter (fun p => ¬ p ∣ m)

/-- The corresponding partial Euler product `∏_{p ∣ n, p ∤ m, p > 2} (p-1)/(p-2)`. -/
noncomputable def oddPrimeProductAway (m n : ℕ) : ℝ :=
  ∏ p ∈ oddPrimeFactorsAway m n, ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- The partial Euler product over the primes dividing the multiplier. -/
noncomputable def oddPrimeProductAt (m n : ℕ) : ℝ :=
  ∏ p ∈ (oddPrimeFactors n).filter (fun p => p ∣ m), ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- **Multiplicative local-factor identity**: the Euler product splits at a fixed
multiplier `m` into the part supported on primes dividing `m` and the part away
from `m`. -/
theorem oddPrimeProduct_split_at (m n : ℕ) :
    oddPrimeProduct n = oddPrimeProductAt m n * oddPrimeProductAway m n := by
  rw [oddPrimeProductAt, oddPrimeProductAway, oddPrimeFactorsAway, oddPrimeProduct]
  exact (Finset.prod_filter_mul_prod_filter_not (oddPrimeFactors n) (fun p => p ∣ m) _).symm

/-- **The `m`-away product as a squarefree-divisor sum**, i.e. the finite form of

    ∏_{p ∣ n, p ∤ m} (1 + 1/(p-2)) = ∑_{d squarefree, d ∣ n, (d,m)=1} ∏_{p ∣ d} 1/(p-2).
-/
theorem twinComparison_mul_argument_expansion (m n : ℕ) :
    oddPrimeProductAway m n =
      ∑ T ∈ (oddPrimeFactorsAway m n).powerset, ∏ p ∈ T, 1 / ((p : ℝ) - 2) := by
  rw [oddPrimeProductAway, ← prod_one_add_eq_powersetSum]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hp' : p ∈ oddPrimeFactors n := (Finset.mem_filter.mp hp).1
  exact oddLocalRatio_eq_one_add (oddPrimeFactors_prime_gt_two hp').2

/-- The comparison weight at a multiplicative argument, split at `m` (odd `n`). -/
theorem twinComparisonWeight_split_at {C2 : ℝ} {n : ℕ} (m : ℕ) (h : ¬ 2 ∣ n) :
    twinComparisonWeight C2 n = 2 * C2 * oddPrimeProductAt m n * oddPrimeProductAway m n := by
  rw [twinComparisonWeight_eq, twinLocalFactor_of_odd h, oddPrimeProduct_split_at m n]
  ring

/-! ### Analytic interfaces — NO INHABITANT -/

/-- **External analytic interface (UNINHABITED).**  The infinite Euler product
identity for the twin constant:

    ∏_{p > 2} (1 + 1/(p(p-2))) = C₂⁻¹,

stated as convergence of the truncated products.  This bank contains no proof of
it, and no inhabitant is produced. -/
def TwinConstantEulerIdentity (C2 : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => ∏ p ∈ (Finset.range N).filter (fun p => Nat.Prime p ∧ 2 < p),
      (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))))
    Filter.atTop (nhds C2⁻¹)

/-- Truncated Euler products are what is genuinely available in Lean: each finite
truncation is a well-defined positive number.  This is *not* the infinite identity. -/
noncomputable def truncatedTwinEulerProduct (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range N).filter (fun p => Nat.Prime p ∧ 2 < p),
    (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))

theorem truncatedTwinEulerProduct_pos (N : ℕ) : 0 < truncatedTwinEulerProduct N := by
  refine Finset.prod_pos ?_
  intro p hp
  have hp2 : 2 < p := (Finset.mem_filter.mp hp).2.2
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have h1 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
  have : (0 : ℝ) < 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by positivity
  linarith

/-- The truncated products are increasing in the truncation point: an elementary
monotonicity fact, and emphatically *not* a convergence statement. -/
theorem truncatedTwinEulerProduct_mono {M N : ℕ} (h : M ≤ N) :
    truncatedTwinEulerProduct M ≤ truncatedTwinEulerProduct N := by
  classical
  set f : ℕ → ℝ := fun p => 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)) with hf
  set s := (Finset.range M).filter (fun p => Nat.Prime p ∧ 2 < p) with hs
  set t := (Finset.range N).filter (fun p => Nat.Prime p ∧ 2 < p) with ht
  have hr : Finset.range M ⊆ Finset.range N := Finset.range_subset_range.mpr h
  have hsub : s ⊆ t := Finset.filter_subset_filter _ hr
  have hsplit : (∏ x ∈ t \ s, f x) * ∏ x ∈ s, f x = ∏ x ∈ t, f x := Finset.prod_sdiff hsub
  have hone : (1 : ℝ) ≤ ∏ x ∈ t \ s, f x := by
    calc (1 : ℝ) = ∏ _x ∈ t \ s, (1 : ℝ) := by simp
      _ ≤ ∏ x ∈ t \ s, f x := by
          refine Finset.prod_le_prod (fun i _ => by norm_num) ?_
          intro p hp
          have hp2 : 2 < p := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.2
          have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
          have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
          have : (0 : ℝ) < 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by positivity
          simp only [hf]
          linarith
  have hposM : 0 < ∏ x ∈ s, f x := truncatedTwinEulerProduct_pos M
  have : truncatedTwinEulerProduct N = (∏ x ∈ t \ s, f x) * ∏ x ∈ s, f x := by
    rw [hsplit]; rfl
  rw [this]
  have : truncatedTwinEulerProduct M = ∏ x ∈ s, f x := rfl
  rw [this]
  nlinarith

/-- **External analytic interface (UNINHABITED).**  The comparison progression
mean: uniformly over the given multipliers and intervals,

    ∑_{n ∈ I} b(m·n) = (m/φ(m)) · |I| + error.

No inhabitant is produced here. -/
def TwinComparisonProgressionMean (b : ℕ → ℝ) (mRange : Finset ℕ)
    (intervals : Finset (Finset ℕ)) (err : ℝ) : Prop :=
  ∀ m ∈ mRange, ∀ I ∈ intervals,
    |(∑ n ∈ I, b (m * n)) - ((m : ℝ) / (Nat.totient m : ℝ)) * (I.card : ℝ)| ≤ err

/-- Provenance: the infinite Euler identity and the progression mean are cited,
not proved. -/
def eulerInterfaceProvenance : Provenance :=
  provenanceExternalTheorem "twin-constant Euler product / comparison progression mean"
    "classical analytic number theory" "asymptotic statements outside this bank"

theorem eulerInterfaceProvenance_not_leanEvidence :
    Provenance.IsLeanEvidence eulerInterfaceProvenance = false := rfl

end NANC.V5
