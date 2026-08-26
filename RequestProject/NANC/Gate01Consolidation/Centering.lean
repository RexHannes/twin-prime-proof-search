import RequestProject.VaughanPacketAlgebra

/-!
# BANK A — the abstract source discrepancy

The Tier-A source object is

`Δ_{c,E}(q;a) = ∑_{0 ≤ n ≤ K, n ≡ a (mod q)} c n − E q`.

The project already contains the finite analogue
`TwinPrimeProject.finiteDiscrepancy` (in `RequestProject/VaughanPacketAlgebra.lean`),
so it is **reused** here rather than redefined.  Everything proved in this
module is structural: it holds for an *arbitrary* expected term `expected`, and
no formula for `E q` is ever assumed.  In particular neither
`expected q = totalMass / q` nor `expected q = totalMass / φ q` is used.

The genuine source formula for `E q` stays an **OPEN SOURCE FIELD**; the
interface recording that fact is `ExpectedDensitySourceInterface` in
`SourceInterfaces.lean`.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-- The restricted (progression) mass of `c`: the part of the discrepancy that
does not involve the expected term at all. -/
def progressionMass (K q a : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1), if n % q = a % q then c n else 0

/-- The total mass of `c` over the finite window. -/
def totalMass (K : ℕ) (c : ℕ → ℝ) : ℝ := ∑ n ∈ Finset.range (K + 1), c n

/-- Unfolding: the archive discrepancy is `progression mass − expected`. -/
theorem finiteDiscrepancy_eq_progressionMass_sub (K q a : ℕ) (c expected : ℕ → ℝ) :
    finiteDiscrepancy K q a c expected = progressionMass K q a c - expected q := rfl

/-- **Structural fact.**  The progression mass carries no information about the
expected term: two different expected terms give discrepancies differing by a
constant depending only on the expected terms. -/
theorem finiteDiscrepancy_sub_finiteDiscrepancy (K q a : ℕ) (c E₁ E₂ : ℕ → ℝ) :
    finiteDiscrepancy K q a c E₁ - finiteDiscrepancy K q a c E₂ = E₂ q - E₁ q := by
  simp [finiteDiscrepancy]

/-- **Structural fact.**  `progressionMass` is recovered from the discrepancy by
adding back the expected term; hence it is independent of `expected`. -/
theorem progressionMass_eq_add (K q a : ℕ) (c expected : ℕ → ℝ) :
    progressionMass K q a c = finiteDiscrepancy K q a c expected + expected q := by
  simp [finiteDiscrepancy, progressionMass]

/-- Additivity of the discrepancy in the pair (coefficient, expected term). -/
theorem finiteDiscrepancy_add (K q a : ℕ) (c₁ c₂ E₁ E₂ : ℕ → ℝ) :
    finiteDiscrepancy K q a (fun n => c₁ n + c₂ n) (fun r => E₁ r + E₂ r)
      = finiteDiscrepancy K q a c₁ E₁ + finiteDiscrepancy K q a c₂ E₂ := by
  simp only [finiteDiscrepancy]
  have h : ∀ n ∈ Finset.range (K + 1),
      (if n % q = a % q then c₁ n + c₂ n else 0)
        = (if n % q = a % q then c₁ n else 0) + (if n % q = a % q then c₂ n else 0) := by
    intro n _; split <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  ring

/-- Homogeneity of the discrepancy. -/
theorem finiteDiscrepancy_smul (K q a : ℕ) (t : ℝ) (c E : ℕ → ℝ) :
    finiteDiscrepancy K q a (fun n => t * c n) (fun r => t * E r)
      = t * finiteDiscrepancy K q a c E := by
  simp only [finiteDiscrepancy, Finset.mul_sum, mul_sub]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split <;> simp

/-- The progression mass at modulus `q = 1` is the full mass. -/
theorem progressionMass_one (K a : ℕ) (c : ℕ → ℝ) :
    progressionMass K 1 a c = totalMass K c := by
  simp [progressionMass, totalMass, Nat.mod_one]

/-- **Structural fact.**  Summing the progression masses over all residues
`a = 0, …, q−1` recovers the total mass. -/
theorem sum_progressionMass_over_residues {q : ℕ} (hq : 0 < q) (K : ℕ) (c : ℕ → ℝ) :
    ∑ a ∈ Finset.range q, progressionMass K q a c = totalMass K c := by
  simp only [progressionMass, totalMass]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have h : ∀ x ∈ Finset.range q, (if n % q = x % q then c n else 0)
      = (if x = n % q then c n else 0) := by
    intro x hx
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hx)]
    by_cases hxx : x = n % q
    · simp [hxx]
    · simp [hxx, Ne.symm hxx]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Finset.range q) (n % q) (fun _ => c n)]
  simp [Finset.mem_range.mpr (Nat.mod_lt n hq)]

end Gate01Consolidation
end TwinPrimeProject
