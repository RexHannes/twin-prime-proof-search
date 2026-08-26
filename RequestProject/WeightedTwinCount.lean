import RequestProject.TwinPrimeDefinitions

open scoped BigOperators

namespace TwinPrimeProject

/-- Primes in the dyadic interval, made finite using `⌊x⌋₊`. -/
noncomputable def dyadicPrimes (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter fun p => Nat.Prime p ∧ x / 2 < p ∧ (p : ℝ) ≤ x

/-- Twin primes in the same interval. -/
noncomputable def dyadicTwinPrimes (x : ℝ) : Finset ℕ :=
  (dyadicPrimes x).filter fun p => Nat.Prime (p + 2)

/-- Prime-power contamination among shifted primes. -/
noncomputable def primePowerContamination (x : ℝ) : Finset ℕ :=
  (dyadicPrimes x).filter fun p => IsPrimePow (p + 2) ∧ ¬ Nat.Prime (p + 2)

/-- The weighted contamination term, defined exactly rather than hidden in an
error notation. -/
noncomputable def primePowerError (x : ℝ) : ℝ :=
  ∑ p ∈ primePowerContamination x,
    ArithmeticFunction.vonMangoldt (p + 2) / Real.log x

/-- Explicit interface for the exact weighted decomposition.  Its finite proof
is not hidden as an axiom. -/
structure WeightedTwinPrimeCountDecompositionInput where
  decomposition : ∀ {x : ℝ}, 1 < x →
    ∑ p ∈ dyadicPrimes x, TwinPrimeWeightedDetector x p =
      (∑ p ∈ dyadicTwinPrimes x, Real.log (p + 2) / Real.log x) +
        primePowerError x

/-- Conditional accessor displaying the pending finite-decomposition dependency. -/
theorem WeightedTwinPrimeCountDecomposition
    (I : WeightedTwinPrimeCountDecompositionInput) {x : ℝ} (hx : 1 < x) :
    ∑ p ∈ dyadicPrimes x, TwinPrimeWeightedDetector x p =
      (∑ p ∈ dyadicTwinPrimes x, Real.log (p + 2) / Real.log x) +
        primePowerError x := I.decomposition hx

/-- The desired sharp elementary contamination count is kept as a visible
conditional interface until its finite combinatorial proof is supplied. -/
def PrimePowerContaminationBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    ((primePowerContamination x).card : ℝ) ≤ C * Real.sqrt x * Real.log x

end TwinPrimeProject
