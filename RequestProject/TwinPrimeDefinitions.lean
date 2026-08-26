import Mathlib

open scoped BigOperators

namespace TwinPrimeProject

/-- The odd primes at most `z`. -/
def oddPrimesUpTo (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter fun p => Nat.Prime p ∧ 2 < p

/-- The odd primorial `P₀(z)`. -/
def OddPrimorial (z : ℕ) : ℕ := ∏ p ∈ oddPrimesUpTo z, p

/-- The parity-normalized finite sieve density `V₀(z)`. -/
noncomputable def V0 (z : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∏ p ∈ oddPrimesUpTo z, (1 - (1 : ℝ) / p)

/-- Indicator of the half-open interval `x/2 < n ≤ x`. -/
noncomputable def intervalIndicator (x : ℝ) (n : ℕ) : ℝ :=
  if x / 2 < n ∧ (n : ℝ) ≤ x then 1 else 0

/-- Weighted shifted-prime detector `aₓ(n)`. -/
noncomputable def TwinPrimeWeightedDetector (x : ℝ) (n : ℕ) : ℝ :=
  intervalIndicator x n * ArithmeticFunction.vonMangoldt (n + 2) / Real.log x

/-- Residue-aware rough comparison candidate.  This name deliberately does not
assert any Ford--Maynard applicability. -/
noncomputable def ResidueAwareComparisonCandidate (x : ℝ) (z n : ℕ) : ℝ :=
  intervalIndicator x n * (if Odd n ∧ Nat.Coprime (n + 2) (OddPrimorial z) then 1 else 0) /
    (Real.log x * V0 z)

/-- Centered candidate difference `wₓ,z = aₓ - bₓ,z`. -/
noncomputable def CenteredCandidateDifference (x : ℝ) (z n : ℕ) : ℝ :=
  TwinPrimeWeightedDetector x n - ResidueAwareComparisonCandidate x z n

/-- The finite local correction contributed by odd prime divisors of `m` up to `z`. -/
noncomputable def ResidueAwareDensityFactor (z m : ℕ) : ℝ :=
  ∏ p ∈ (oddPrimesUpTo z).filter (fun p => p ∣ m), ((1 - (1 : ℝ) / p)⁻¹)

/-- The radical, represented as the product of the distinct prime divisors. -/
def radical (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

/-- The second finite sieve product. -/
noncomputable def W0 (z : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesUpTo z, (1 - (1 : ℝ) / (p - 1))

/-- The finite twin-prime singular-series product. -/
noncomputable def FiniteTwinPrimeSingularSeries (z : ℕ) : ℝ :=
  2 * ∏ p ∈ oddPrimesUpTo z, (1 - (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2)

end TwinPrimeProject
