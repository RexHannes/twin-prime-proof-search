import Mathlib

-- RequestProject/REAL1B_20261122/QuarterRough.lean
/-! REAL 1B. Gold 4.50-B §10, (19)–(20), retained in Gold 4.53-B.
    The upper twin is n. The range begins at 2 since the prime-only
    weight at n - 2 vanishes for both n = 0 and n = 1. -/
namespace REAL1B

open ArithmeticFunction
noncomputable section
open Classical

def Rough (n : ℕ) : Prop := n < n.minFac ^ 4

theorem rough_iff (n : ℕ) (hn : 1 < n) :
    Rough n ↔ ∀ p : ℕ, p.Prime → p ∣ n → n < p ^ 4 := by
  constructor
  · intro h p hp hd
    exact lt_of_lt_of_le h (Nat.pow_le_pow_left (Nat.minFac_le_of_dvd hp.two_le hd) 4)
  · intro h
    exact h _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)

private theorem pow_length_le_prod (p : ℕ) (l : List ℕ)
    (h : ∀ q ∈ l, p ≤ q) : p ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa [pow_succ, Nat.mul_comm] using
      Nat.mul_le_mul (h a (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem rough_rank (n : ℕ) (hn : 1 < n) (hr : Rough n) :
    cardFactors n = 1 ∨ cardFactors n = 2 ∨ cardFactors n = 3 := by
  have hb := pow_length_le_prod n.minFac n.primeFactorsList (fun q hq =>
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hq).two_le
      (Nat.dvd_of_mem_primeFactorsList hq))
  rw [Nat.prod_primeFactorsList (by omega)] at hb
  have hpos := cardFactors_pos_iff_one_lt.mpr hn
  have hlt : cardFactors n < 4 := by
    by_contra! h
    exact (not_le_of_gt hr) ((Nat.pow_le_pow_right (Nat.minFac_pos n) h).trans hb)
  omega

def mu (n : ℕ) : ℝ := (moebius n : ℤ)
def primeMask (n : ℕ) : ℝ := if n.Prime then 1 else 0
def roughMask (n : ℕ) : ℝ := if Rough n then 1 else 0
def classMask (k n : ℕ) : ℝ :=
  if Rough n ∧ Squarefree n ∧ cardFactors n = k then 1 else 0

private theorem prime_rough {n : ℕ} (hp : n.Prime) : Rough n := by
  unfold Rough
  rw [hp.minFac_eq]
  simpa using (Nat.pow_lt_pow_right hp.one_lt (by decide : 1 < 4))

/-- Pointwise unsigned and signed classifications on the entire input. -/
theorem parity_masks (n : ℕ) (hn : 1 < n) :
    (mu n ^ 2 * roughMask n = primeMask n + classMask 2 n + classMask 3 n) ∧
    (mu n * roughMask n = -primeMask n + classMask 2 n - classMask 3 n) := by
  by_cases hr : Rough n
  · by_cases hs : Squarefree n
    · rcases rough_rank n hn hr with h | h | h
      · have hp := cardFactors_eq_one_iff_prime.mp h
        norm_num [mu, moebius_apply_prime hp, primeMask, roughMask, classMask, hr, hs, hp, h]
      · have hp : ¬n.Prime := fun hp => by have := cardFactors_apply_prime hp; omega
        norm_num [mu, moebius_apply_of_squarefree hs, primeMask, roughMask, classMask, hr, hs, hp, h]
      · have hp : ¬n.Prime := fun hp => by have := cardFactors_apply_prime hp; omega
        norm_num [mu, moebius_apply_of_squarefree hs, primeMask, roughMask, classMask, hr, hs, hp, h]
    · have hp : ¬n.Prime := fun hp => hs hp.squarefree
      simp [mu, moebius_eq_zero_of_not_squarefree hs, primeMask, roughMask, classMask, hs, hp]
  · have hp : ¬n.Prime := fun hp => hr (prime_rough hp)
    simp [primeMask, roughMask, classMask, hr, hp]

def mass (X : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊2 * X⌋₊,
    (if X < (n : ℝ) ∧ (n - 2).Prime then Real.log (n - 2 : ℕ) else 0) * f n

theorem source_parity (X : ℝ) :
    mass X (fun n => mu n ^ 2 * roughMask n) =
      mass X primeMask + mass X (classMask 2) + mass X (classMask 3) ∧
    mass X (fun n => mu n * roughMask n) =
      -mass X primeMask + mass X (classMask 2) - mass X (classMask 3) := by
  constructor
  · unfold mass
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only
    rw [(parity_masks n (Finset.mem_Icc.mp hn).1).1]
    ring
  · unfold mass
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only
    rw [(parity_masks n (Finset.mem_Icc.mp hn).1).2]
    ring

theorem h2_identity (X : ℝ) :
    2 * mass X primeMask =
      mass X (fun n => mu n ^ 2 * roughMask n) - 2 * mass X (classMask 3) -
      mass X (fun n => mu n * roughMask n) := by
  obtain ⟨hu, hs⟩ := source_parity X
  linarith

/-- The two error terms can be controlled separately. The signed bound is a hypothesis. -/
theorem h2_lower (X h₀ ρ e N E₁ E₂ : ℝ)
    (hu : (h₀ - e) * N - E₁ ≤ mass X (fun n => mu n ^ 2 * roughMask n) -
      2 * mass X (classMask 3))
    (hs : mass X (fun n => mu n * roughMask n) + ρ * N ≤ N / 8 + E₂) :
    (h₀ + ρ - e - 1 / 8) * N - E₁ - E₂ ≤ 2 * mass X primeMask := by
  linarith only [h2_identity X, hu, hs]

/-- A positive mass forces a pair at the original open lower endpoint. -/
theorem pair_of_mass_pos {X : ℝ} (h : 0 < mass X primeMask) :
    ∃ n : ℕ, X < n ∧ n ≤ ⌊2 * X⌋₊ ∧ n.Prime ∧ (n - 2).Prime := by
  by_contra! he
  have hz : mass X primeMask = 0 := by
    unfold mass
    apply Finset.sum_eq_zero
    intro n hn
    by_cases hm : X < (n : ℝ) ∧ (n - 2).Prime
    · have hnp : ¬ n.Prime := fun hp =>
        he n hm.1 (Finset.mem_Icc.mp hn).2 hp hm.2
      simp [primeMask, hnp]
    · simp [hm]
  linarith

/-- Conditional endpoint: positive source mass at arbitrarily large scales. -/
theorem infinite_of_unbounded_mass
    (h : ∀ B : ℕ, ∃ X : ℝ, (B : ℝ) < X ∧ 0 < mass X primeMask) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p + 2).Prime} := by
  intro hf
  obtain ⟨b, hb⟩ := hf.bddAbove
  obtain ⟨X, hX, hpos⟩ := h (b + 2)
  obtain ⟨n, hn, _, hp, hm⟩ := pair_of_mass_pos hpos
  have hbn : b + 2 < n := by exact_mod_cast hX.trans hn
  have hshift : n - 2 + 2 = n := by omega
  have hmem : n - 2 ∈ {p : ℕ | p.Prime ∧ (p + 2).Prime} :=
    ⟨hm, hshift.symm ▸ hp⟩
  have := hb hmem
  omega

end
end REAL1B

#print axioms REAL1B.rough_iff
#print axioms REAL1B.rough_rank
#print axioms REAL1B.parity_masks
#print axioms REAL1B.source_parity
#print axioms REAL1B.h2_identity
#print axioms REAL1B.h2_lower
#print axioms REAL1B.pair_of_mass_pos
#print axioms REAL1B.infinite_of_unbounded_mass

-- RequestProject/REAL1B_20261122/FMResidual.lean
namespace REAL1B.FM

/-- Gold 4.53-FM §1: the stronger historical residual target. -/
theorem historical_margin (T S Pneg R E₁ E₂ : ℝ)
    (lower : (0.361755018 - (10 : ℝ)⁻¹ ^ 58) * S + Pneg - R - E₁ ≤ T)
    (residual : R - Pneg ≤ (0.359892818 - (10 : ℝ)⁻¹ ^ 58) * S + E₂) :
    0.0018622 * S - E₁ - E₂ ≤ T := by
  linarith only [lower, residual]

/-- Gold 4.53-FM target (T) omits the tiny subtraction on the residual side. -/
theorem current_margin (T S Pneg R E₁ E₂ : ℝ)
    (lower : (0.361755018 - (10 : ℝ)⁻¹ ^ 58) * S + Pneg - R - E₁ ≤ T)
    (residual : R - Pneg ≤ 0.359892818 * S + E₂) :
    (0.0018622 - (10 : ℝ)⁻¹ ^ 58) * S - E₁ - E₂ ≤ T := by
  linarith only [lower, residual]

end REAL1B.FM

#print axioms REAL1B.FM.historical_margin
#print axioms REAL1B.FM.current_margin

-- RequestProject/TwinPrimeDefinitions.lean
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

-- RequestProject/WeightedTwinCount.lean
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

-- RequestProject/REAL1B_20261122/WeightedDecomposition.lean
open scoped BigOperators

namespace TwinPrimeProject

/-- Construct the finite decomposition input in the historical GitHub bank. -/
theorem weighted_decomposition_input : Nonempty WeightedTwinPrimeCountDecompositionInput := by
  classical
  refine ⟨⟨?_⟩⟩
  intro x _
  unfold dyadicTwinPrimes primePowerError primePowerContamination
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hi := (Finset.mem_filter.mp hp).2.2
  unfold TwinPrimeWeightedDetector intervalIndicator
  rw [if_pos hi, one_mul]
  by_cases h : (p + 2).Prime
  · simp [h, ArithmeticFunction.vonMangoldt_apply_prime h]
  · by_cases hpow : IsPrimePow (p + 2)
    · simp [h, hpow]
    · simp [h, hpow, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]

/-- No proof-carrying input record is required of callers. -/
theorem weighted_decomposition {x : ℝ} (hx : 1 < x) :
    ∑ p ∈ dyadicPrimes x, TwinPrimeWeightedDetector x p =
      (∑ p ∈ dyadicTwinPrimes x, Real.log (p + 2) / Real.log x) + primePowerError x := by
  obtain ⟨I⟩ := weighted_decomposition_input
  exact WeightedTwinPrimeCountDecomposition I hx

end TwinPrimeProject

#print axioms TwinPrimeProject.weighted_decomposition_input
#print axioms TwinPrimeProject.weighted_decomposition

-- RequestProject/REAL1B_20261122/Vaughan.lean
/-! Gold 4.53-B, part II §9. The sums use the larger input n=t+2.
Arithmetic-function multiplication is Dirichlet convolution. -/
namespace REAL1B.Vaughan
open ArithmeticFunction
noncomputable section
open Classical

abbrev AF := ArithmeticFunction ℝ
def zetaR : AF := ArithmeticFunction.zeta
def mob : AF := ArithmeticFunction.moebius
def lam : AF := ArithmeticFunction.vonMangoldt

def low (u : ℝ) (a : AF) : AF :=
  ⟨fun n => if (n : ℝ) ≤ u then a n else 0, by simp⟩
def high (u : ℝ) (a : AF) := a - low u a
def cV (v : ℝ) := high v lam * zetaR
def coeffI (u v : ℝ) : AF := low u mob * ArithmeticFunction.log - low u mob * (low v lam * zetaR)
def coeffII (u v : ℝ) : AF := high u mob * cV v

theorem high_apply (u : ℝ) (a : AF) (n : ℕ) :
    high u a n = if u < n then a n else 0 := by
  change a n - (if (n : ℝ) ≤ u then a n else 0) = _
  by_cases h : (n : ℝ) ≤ u
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

theorem vaughan_identity (u v : ℝ) : lam = low v lam + coeffI u v + coeffII u v := by
  have hz : mob * zetaR = 1 := coe_moebius_mul_coe_zeta
  have hl : lam * zetaR = ArithmeticFunction.log := vonMangoldt_mul_zeta
  unfold coeffI coeffII cV high
  rw [← hl]
  linear_combination (low v lam - lam) * hz

def Sifted (z : ℝ) (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → z < p
def sieve (z : ℝ) (n : ℕ) : ℝ := if Sifted z n then 1 else 0

theorem sieve_mul (z : ℝ) (m r : ℕ) : sieve z (m*r) = sieve z m * sieve z r := by
  have iff : Sifted z (m*r) ↔ Sifted z m ∧ Sifted z r := by
    constructor
    · intro h
      exact ⟨fun p hp hd => h p hp (dvd_mul_of_dvd_left hd r),
             fun p hp hd => h p hp (dvd_mul_of_dvd_right hd m)⟩
    · rintro ⟨hm,hr⟩ p hp hd
      rcases hp.dvd_mul.mp hd with h | h
      · exact hm p hp h
      · exact hr p hp h
  by_cases hm : Sifted z m <;> by_cases hr : Sifted z r <;> simp [sieve, iff, hm, hr]

/-- Exact positive companion, summing Λ over the divisors strictly above v. -/
theorem cV_divisors (v : ℝ) (r : ℕ) :
    cV v r = ∑ l ∈ r.divisors, if v < (l : ℝ) then lam l else 0 := by
  simpa [cV, zetaR, high_apply] using
    (ArithmeticFunction.coe_mul_zeta_apply (f := high v lam) (x := r))

theorem cV_zero_below {v : ℝ} {r : ℕ} (hr : (r:ℝ) ≤ v) : cV v r = 0 := by
  rw [cV_divisors]
  apply Finset.sum_eq_zero
  intro l hl
  have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hl).2) (Nat.mem_divisors.mp hl).1
  have hd' : (l:ℝ) ≤ r := by exact_mod_cast hd
  simp [not_lt.mpr (hd'.trans hr)]

theorem typeII_factors (u v z : ℝ) (t : ℕ) :
    sieve z t * coeffII u v t =
    ∑ a ∈ t.divisorsAntidiagonal,
      (if u < (a.1 : ℝ) then mob a.1 else 0) * sieve z a.1 *
        (cV v a.2 * sieve z a.2) := by
  rw [coeffII, ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← (Nat.mem_divisorsAntidiagonal.mp ha).1, sieve_mul, high_apply]
  ring

def theta (t : ℕ) : ℝ := if t.Prime then Real.log t else 0
def interval (X : ℝ) : Finset ℕ := (Finset.Icc 2 ⌊2*X⌋₊).filter (fun n : ℕ => X < (n : ℝ))
def total (X : ℝ) (f : ℕ → ℝ) := ∑ n ∈ interval X, f n

theorem mass_as_sum (X : ℝ) (f : ℕ → ℝ) :
    mass X f = total X (fun n => theta (n-2) * f n) := by
  unfold mass total interval
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : X < (n : ℝ) <;> by_cases hp : (n-2).Prime <;> simp [h,hp,theta]

/-- Reindex n = p+2 with the exact translated window and smaller-member weight. -/
theorem twin_mass_reindex (X : ℝ) :
    mass X primeMask = ∑ p ∈ (interval X).image (fun n => n-2),
      theta p * primeMask (p+2) := by
  rw [mass_as_sum, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    simp [Nat.sub_add_cancel h]
  · intro a ha b hb he
    have hlo (k : ℕ) (hk : k ∈ interval X) : 2 ≤ k :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have h₁ := hlo a ha
    have h₂ := hlo b hb
    change a - 2 = b - 2 at he
    omega

theorem theta_prime_power_correction (t : ℕ) :
    lam t = theta t + (if IsPrimePow t ∧ ¬ t.Prime then lam t else 0) := by
  by_cases hp : t.Prime
  · simp [lam, theta, hp, vonMangoldt_apply_prime hp]
  · by_cases h : IsPrimePow t
    · simp [theta, hp, h]
    · simp [lam, theta, hp, h, vonMangoldt_eq_zero_iff.mpr h]

def U (X : ℝ) := X ^ (1/5 : ℝ)
def Z (X : ℝ) := Real.exp (Real.log X ^ (0.24 : ℝ))
def fixed (X : ℝ) (n : ℕ) : ℝ := if X < (n.minFac : ℝ)^4 then mu n else 0
def native (n : ℕ) := mu n * roughMask n
def op (X : ℝ) (a : AF) := total X (fun n =>
  fixed X n * (sieve (Z X) (n-2) * a (n-2)))
def typeI (X : ℝ) := op X (coeffI (U X) (U X))
def typeII (X : ℝ) := op X (coeffII (U X) (U X))
def lowOutput (X : ℝ) := op X (low (U X) lam)
def primeCorrection (X : ℝ) := total X (fun n => fixed X n *
  (theta (n-2) - sieve (Z X) (n-2) * lam (n-2)))
def collar (X : ℝ) := total X (fun n => theta (n-2) * (native n - fixed X n))

theorem fourth_root_iff {X : ℝ} (hx : 0 ≤ X) (p : ℕ) :
    X ^ (1/4:ℝ) < (p:ℝ) ↔ X < (p:ℝ)^4 := by
  simpa [one_div] using (Real.rpow_inv_lt_iff_of_pos hx (Nat.cast_nonneg p) (by norm_num : (0:ℝ)<4))

/-- Fully expanded (9.1), retaining the positive divisor companion and both presieves. -/
theorem typeII_expanded (X : ℝ) :
    typeII X = ∑ n ∈ interval X, fixed X n *
      ∑ a ∈ (n-2).divisorsAntidiagonal,
        (if U X < (a.1:ℝ) then mob a.1 else 0) * sieve (Z X) a.1 *
          ((∑ l ∈ a.2.divisors, if U X < (l:ℝ) then lam l else 0) * sieve (Z X) a.2) := by
  unfold typeII op total
  simp_rw [typeII_factors, cV_divisors]

theorem collar_support {X : ℝ} {n : ℕ} (hn : X < (n : ℝ)) (hh : (n : ℝ) ≤ 2*X)
    (hd : native n ≠ fixed X n) :
    X < (n.minFac : ℝ)^4 ∧ (n.minFac : ℝ)^4 ≤ 2*X := by
  by_cases h : Rough n
  · have hl : (n : ℝ) < (n.minFac : ℝ)^4 := by exact_mod_cast h
    simp [native, roughMask, h, fixed, hn.trans hl] at hd
  · have hn' : n.minFac ^ 4 ≤ n := le_of_not_gt h
    have hh' : (n.minFac : ℝ)^4 ≤ (n : ℝ) := by exact_mod_cast hn'
    by_cases hf : X < (n.minFac : ℝ)^4
    · exact ⟨hf,hh'.trans hh⟩
    · simp [native,roughMask,h,fixed,hf] at hd

/-- Exact identity before any Type-I, collar or prime-power asymptotic. -/
theorem native_vaughan (X : ℝ) :
    mass X native = typeI X + typeII X + lowOutput X + primeCorrection X + collar X := by
  rw [mass_as_sum]
  unfold typeI typeII lowOutput primeCorrection collar op total
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hv := congrArg (fun a : AF => a (n-2)) (vaughan_identity (U X) (U X))
  simp only [ArithmeticFunction.add_apply] at hv
  linear_combination fixed X n * sieve (Z X) (n-2) * hv

end
end REAL1B.Vaughan

#print axioms REAL1B.Vaughan.high_apply
#print axioms REAL1B.Vaughan.vaughan_identity
#print axioms REAL1B.Vaughan.sieve_mul
#print axioms REAL1B.Vaughan.cV_divisors
#print axioms REAL1B.Vaughan.typeII_factors
#print axioms REAL1B.Vaughan.mass_as_sum
#print axioms REAL1B.Vaughan.twin_mass_reindex
#print axioms REAL1B.Vaughan.theta_prime_power_correction
#print axioms REAL1B.Vaughan.collar_support
#print axioms REAL1B.Vaughan.native_vaughan

#print axioms REAL1B.Vaughan.cV_zero_below
#print axioms REAL1B.Vaughan.fourth_root_iff
#print axioms REAL1B.Vaughan.typeII_expanded

-- RequestProject/REAL1B_20261122/SourceBridge.lean
namespace REAL1B.Bridge
open TwinPrimeProject Vaughan
noncomputable section
open Classical

def shiftedPairs (X : ℝ) := ((interval X).image (fun n : ℕ => n-2)).filter
  (fun p => p.Prime ∧ (p+2).Prime)

theorem shiftedPairs_iff (X : ℝ) (p : ℕ) :
    p ∈ shiftedPairs X ↔ X < ((p+2:ℕ):ℝ) ∧ p+2 ≤ ⌊2*X⌋₊ ∧ p.Prime ∧ (p+2).Prime := by
  simp only [shiftedPairs, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨n,hn,rfl⟩,hp⟩
    have h := Finset.mem_filter.mp hn
    have hl := Finset.mem_Icc.mp h.1
    rw [Nat.sub_add_cancel hl.1] at *
    exact ⟨h.2,hl.2,hp⟩
  · rintro ⟨hl,hh,hp,hq⟩
    exact ⟨⟨p+2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hh⟩,hl⟩, by omega⟩,hp,hq⟩

theorem mass_eq_log_sum (X : ℝ) :
    mass X primeMask = ∑ p ∈ shiftedPairs X, Real.log p := by
  rw [twin_mass_reindex,shiftedPairs,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.Prime <;> by_cases k : (p+2).Prime <;> simp [theta,primeMask,h,k]

/-- Historical x=2X. Remove its proper-prime-power error before conversion.
On common pairs log(p+2) and log p differ; the two window differences are signed. -/
theorem historical_conversion (X : ℝ) (hX : 1 < 2*X) :
    ((∑ p ∈ dyadicPrimes (2*X), TwinPrimeWeightedDetector (2*X) p) -
      primePowerError (2*X)) * Real.log (2*X) - mass X primeMask =
    (∑ p ∈ dyadicTwinPrimes (2*X), (Real.log ((p:ℝ)+2) - Real.log p)) +
    (∑ p ∈ dyadicTwinPrimes (2*X) \ shiftedPairs X, Real.log p) -
    ∑ p ∈ shiftedPairs X \ dyadicTwinPrimes (2*X), Real.log p := by
  rw [weighted_decomposition hX, add_sub_cancel_right, Finset.sum_mul, mass_eq_log_sum]
  simp only [div_mul_cancel₀ _ (Real.log_pos hX).ne', Finset.sum_sub_distrib]
  let a := dyadicTwinPrimes (2*X)
  let b := shiftedPairs X
  have ha := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) (Finset.inter_subset_left : a ∩ b ⊆ a)
  have hb := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) (Finset.inter_subset_right : a ∩ b ⊆ b)
  have da : a \ (a ∩ b) = a \ b := by ext p; simp
  have db : b \ (a ∩ b) = b \ a := by ext p; simp
  rw [da] at ha
  rw [db] at hb
  dsimp [a,b] at ha hb
  linarith

end
end REAL1B.Bridge

#print axioms REAL1B.Bridge.shiftedPairs_iff
#print axioms REAL1B.Bridge.mass_eq_log_sum
#print axioms REAL1B.Bridge.historical_conversion

-- RequestProject/REAL1B_20261122/H2Source.lean
namespace REAL1B.H2
open Filter Vaughan MeasureTheory
noncomputable section
open Classical

/-- k indexes the possible odd-prime factors p=k+3 of the Euler product. -/
def offset (k : ℕ) : ℝ := if (k+3).Prime then -(1 / ((k:ℝ)+2)^2) else 0
def series : ℝ := 2 * ∏' k : ℕ, (1 + offset k)

private theorem summable_offset : Summable offset := by
  have hs := (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  apply hs.of_norm_bounded
  intro k
  by_cases h : (k+3).Prime <;> (simp [offset, h, Nat.cast_add, Real.norm_eq_abs]; first | positivity | done)

theorem euler_converges : Multipliable (fun k : ℕ => 1 + offset k) :=
  Real.multipliable_one_add_of_summable summable_offset

theorem series_pos : 0 < series := by
  have hpos (k : ℕ) : 0 < 1 + offset k := by
    by_cases h : (k+3).Prime
    · have hk : 1 < ((k:ℝ)+2)^2 := by nlinarith [sq_nonneg (k:ℝ), (Nat.cast_nonneg k : 0 ≤ (k:ℝ))]
      have := (div_lt_one (by positivity : 0 < ((k:ℝ)+2)^2)).mpr hk
      simp only [offset, if_pos h]
      linarith
    · simp [offset,h]
  unfold series
  rw [← Real.rexp_tsum_eq_tprod hpos (Real.summable_log_one_add_of_summable summable_offset)]
  positivity

def N0 (X : ℝ) := series * X / Real.log X
theorem scale_pos {X : ℝ} (hx : 1 < X) : 0 < N0 X :=
  div_pos (mul_pos series_pos (by linarith)) (Real.log_pos hx)

/-- The ordered simplex has t₃=1-t₁-t₂, t₁>1/4, t₁<t₂<t₃. -/
def I3 : ℝ := ∫ t : ℝ in Set.Ioo (1/4 : ℝ) (1/3),
  ∫ u : ℝ in Set.Ioo t ((1-t)/2), 1 / (t*u*(1-t-u))
def cB : ℝ := 7/2 * Real.log 3 - 4 * Real.log 2
def rho3 : ℝ := 1 - Real.log 3 + I3
def tripleCoeff : ℝ := 10/3 * I3
def margin : ℝ := cB - 2*tripleCoeff + rho3 - 1/8
def unsigned (X : ℝ) := mass X (fun n => mu n ^ 2 * roughMask n)
def triple (X : ℝ) := mass X (classMask 3)
def gammaQ (X : ℝ) := mass X native + rho3 * N0 X

/-- All epsilons are fixed before X tends to infinity. -/
def negligible (f : ℝ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, |f X| ≤ ε * N0 X
def H1Consequence : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, (cB - ε) * N0 X ≤ unsigned X
def TripleCap : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, triple X ≤ (tripleCoeff + ε) * N0 X
def TypeICalibration := negligible (fun X => typeI X + rho3 * N0 X)
def FinalTypeII : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, typeII X ≤ (1/8 + ε) * N0 X
def GammaBound : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, gammaQ X ≤ (1/8 + ε) * N0 X

theorem gamma_split (X : ℝ) :
    gammaQ X - typeII X = (typeI X + rho3*N0 X) +
      lowOutput X + primeCorrection X + collar X := by
  unfold gammaQ
  rw [native_vaughan]
  ring

theorem gamma_approx (hi : TypeICalibration) (hl : negligible lowOutput)
    (hp : negligible primeCorrection) (hc : negligible collar) :
    negligible (fun X => gammaQ X - typeII X) := by
  intro ε he
  have hd : 0 < ε/4 := by linarith
  filter_upwards [hi _ hd, hl _ hd, hp _ hd, hc _ hd] with X h₁ h₂ h₃ h₄
  rw [gamma_split, abs_le]
  have a := abs_le.mp h₁
  have b := abs_le.mp h₂
  have c := abs_le.mp h₃
  have d := abs_le.mp h₄
  constructor <;> linarith

theorem gamma_of_typeII (h : negligible (fun X => gammaQ X - typeII X))
    (hs : FinalTypeII) : GammaBound := by
  intro ε he
  have hd : 0 < ε/2 := by linarith
  filter_upwards [h _ hd, hs _ hd] with X ha hb
  have := (abs_le.mp ha).2
  linarith

theorem infinite_of_gamma (hm : 0 < margin) (h₁ : H1Consequence)
    (h₃ : TripleCap) (hs : GammaBound) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  apply infinite_of_unbounded_mass
  intro B
  let δ := margin/8
  have hd : 0 < δ := by dsimp [δ]; linarith
  have ev : ∀ᶠ X : ℝ in atTop, (B : ℝ) < X ∧ 0 < mass X primeMask := by
    filter_upwards [eventually_gt_atTop (B:ℝ), eventually_gt_atTop (1:ℝ),
      h₁ _ hd, h₃ _ hd, hs _ hd] with X hb hx ha ht hg
    refine ⟨hb, ?_⟩
    have hn := mul_pos hm (scale_pos hx)
    have hi := h2_identity X
    change mass X (fun n => mu n * roughMask n) + rho3 * N0 X ≤ _ at hg
    unfold unsigned at ha
    unfold triple at ht
    dsimp [δ, margin] at hn ha ht hg
    linarith
  exact ev.exists

/-- Native Gold 4.53-B route with each analytic obligation displayed separately. -/
theorem infinite_of_vaughan (hm : 0 < margin) (h₁ : H1Consequence)
    (h₃ : TripleCap) (hi : TypeICalibration) (hl : negligible lowOutput)
    (hp : negligible primeCorrection) (hc : negligible collar) (hs : FinalTypeII) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_gamma hm h₁ h₃ (gamma_of_typeII (gamma_approx hi hl hp hc) hs)

end
end REAL1B.H2

#print axioms REAL1B.H2.euler_converges
#print axioms REAL1B.H2.series_pos
#print axioms REAL1B.H2.scale_pos
#print axioms REAL1B.H2.gamma_split
#print axioms REAL1B.H2.gamma_approx
#print axioms REAL1B.H2.gamma_of_typeII
#print axioms REAL1B.H2.infinite_of_gamma
#print axioms REAL1B.H2.infinite_of_vaughan

-- RequestProject/REAL1B_20261122/Margin.lean
/-! A rational upper bound on the ordered triple integral is sufficient to
certify strict positivity. No decimal approximation to that integral is used. -/
namespace REAL1B.H2
open MeasureTheory Filter Set
noncomputable section

private def poly (t u : ℝ) := 208*t^2 + 208*t*u - 208*t + 208*u^2 - 208*u + 97
private def outer (t : ℝ) := -468*t^3 + 468*t^2 - 395*t/2 + 187/6

private theorem reciprocal_simplex {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x+y+z=1) :
    64 / ((1+x)*(1+y)*(1+z)) ≤ 32 - 13*(x*y+y*z+x*z) := by
  let s := x*y+y*z+x*z
  let q := x*y*z
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hsq : s ≤ 1/3 := by
    dsimp [s]
    nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (x-z),
      congrArg (fun t : ℝ => t^2) hs]
  have hq : 3*q ≤ s := by
    dsimp [q,s]
    nlinarith [mul_nonneg (mul_nonneg hx hy) (show 0 ≤ 1-z by linarith),
      mul_nonneg (mul_nonneg hx hz) (show 0 ≤ 1-y by linarith),
      mul_nonneg (mul_nonneg hy hz) (show 0 ≤ 1-x by linarith)]
  have hfac : (1+x)*(1+y)*(1+z) = 2+s+q := by dsimp [s,q]; linarith only [hs]
  apply (div_le_iff₀ (by positivity)).mpr
  change 64 ≤ (32-13*s) * _
  rw [hfac]
  nlinarith [mul_nonneg hs0 (show 0 ≤ 32-13*(2+s+q) by linarith)]

private theorem reciprocal_le (t u : ℝ) (ht : 1/4 ≤ t) (hu : t ≤ u) (hv : u ≤ (1-t)/2) :
    1 / (t*u*(1-t-u)) ≤ poly t u := by
  have h := reciprocal_simplex (x := 4*t-1) (y := 4*u-1) (z := 4*(1-t-u)-1)
    (by linarith) (by linarith) (by linarith) (by ring)
  have he : (1+(4*t-1))*(1+(4*u-1))*(1+(4*(1-t-u)-1)) = 64*(t*u*(1-t-u)) := by ring
  rw [he] at h
  have hden : 0 < t*u*(1-t-u) := by
    have : 0 < 1-t-u := by linarith
    have : 0 < t := by linarith
    have : 0 < u := by linarith
    positivity
  apply (div_le_iff₀ hden).mpr
  have h' := (div_le_iff₀ (by positivity : 0 < 64*(t*u*(1-t-u)))).mp h
  unfold poly
  linarith only [h']

private theorem eval_inner (t : ℝ) :
    (∫ u in t..(1-t)/2, poly t u) = outer t := by
  let A := fun u : ℝ => (208*t^2-208*t+97)*u + (104*t-104)*u^2 + (208/3)*u^3
  have hd (u : ℝ) : HasDerivAt A (poly t u) u := by
    unfold A poly
    convert (((hasDerivAt_id u).const_mul (208*t^2-208*t+97)).add
      (((hasDerivAt_id u).pow 2).const_mul (104*t-104))).add
      (((hasDerivAt_id u).pow 3).const_mul (208/3)) using 1
    simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := A) (fun u _ => hd u)
    (by unfold poly; exact Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold A outer
  ring

private theorem eval_outer : (∫ t in (1/4:ℝ)..(1/3), outer t) = 115/768 := by
  let A := fun t : ℝ => (-117)*t^4 + 156*t^3 + (-395/4)*t^2 + (187/6)*t
  have hd (t : ℝ) : HasDerivAt A (outer t) t := by
    unfold A outer
    convert (((((hasDerivAt_id t).pow 4).const_mul (-117)).add
      (((hasDerivAt_id t).pow 3).const_mul 156)).add
      (((hasDerivAt_id t).pow 2).const_mul (-395/4))).add
      ((hasDerivAt_id t).const_mul (187/6)) using 1
    simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := A) (fun t _ => hd t)
    (by unfold outer; exact Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num [A]

def tripleSlice (t : ℝ) := ∫ u : ℝ in Ioo t ((1-t)/2), 1 / (t*u*(1-t-u))

private theorem inner_bounds {t : ℝ} (ht : t ∈ Ioo (1/4:ℝ) (1/3)) :
    0 ≤ tripleSlice t ∧ tripleSlice t ≤ outer t := by
  have hb : t ≤ (1-t)/2 := by linarith [ht.2]
  have hpos (u : ℝ) (h : u ∈ Ioo t ((1-t)/2)) : 0 ≤ 1 / (t*u*(1-t-u)) := by
    have : 0 < t := by linarith [ht.1]
    have : 0 < u := by linarith [h.1]
    have : 0 < 1-t-u := by linarith [h.2,ht.2]
    positivity
  unfold tripleSlice
  constructor
  · exact integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall hpos))
  · rw [← eval_inner, intervalIntegral.integral_of_le hb, integral_Ioc_eq_integral_Ioo]
    apply integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall hpos))
    · exact ((show Continuous (poly t) by unfold poly; fun_prop).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun u hu =>
        reciprocal_le t u ht.1.le hu.1.le hu.2.le))

/-- Both bounded simplex integrals exist as ordinary Lebesgue integrals. -/
theorem triple_integrability :
    (∀ t ∈ Ioo (1/4:ℝ) (1/3), IntegrableOn (fun u : ℝ => 1/(t*u*(1-t-u))) (Ioo t ((1-t)/2))) ∧
    IntegrableOn tripleSlice (Ioo (1/4:ℝ) (1/3)) := by
  constructor
  · intro t ht
    have hc : ContinuousOn (fun u : ℝ => 1/(t*u*(1-t-u))) (Icc t ((1-t)/2)) := by
      apply continuousOn_const.div (by fun_prop)
      intro u hu
      have : 0 < t := by linarith [ht.1]
      have : 0 < u := by linarith [hu.1]
      have : 0 < 1-t-u := by linarith [hu.2,ht.2]
      positivity
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  · have hm : Measurable tripleSlice := by
      unfold tripleSlice
      simp_rw [← integral_indicator measurableSet_Ioo]
      apply StronglyMeasurable.measurable
      apply StronglyMeasurable.integral_prod_right
      apply Measurable.stronglyMeasurable
      classical
      simp only [Function.uncurry_def, Set.indicator_apply]
      apply Measurable.ite _ (by fun_prop) (by fun_prop)
      exact (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd (show Measurable (fun p : ℝ × ℝ => (1-p.1)/2) by fun_prop))
    have ho : IntegrableOn outer (Ioo (1/4:ℝ) (1/3)) volume := ((show Continuous outer by unfold outer; fun_prop).continuousOn.integrableOn_compact
      (isCompact_Icc (α := ℝ) (a := 1/4) (b := 1/3))).mono_set Ioo_subset_Icc_self
    apply ho.mono' hm.aestronglyMeasurable
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    apply Eventually.of_forall
    intro t ht
    simpa [Real.norm_eq_abs, abs_of_nonneg (inner_bounds ht).1] using (inner_bounds ht).2

theorem triple_integral_upper : I3 ≤ 115/768 := by
  rw [← eval_outer, intervalIntegral.integral_of_le (by norm_num : (1/4:ℝ) ≤ 1/3),
    integral_Ioc_eq_integral_Ioo]
  change (∫ t in Ioo (1/4:ℝ) (1/3), tripleSlice t) ≤ _
  apply integral_mono_of_nonneg
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun _ h => (inner_bounds h).1))
  · exact ((show Continuous outer by unfold outer; fun_prop).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun _ h => (inner_bounds h).2))

theorem margin_floor : 1/4000 < margin := by
  have h : (2:ℝ)^84 < 3^53 := by norm_num
  have hl := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num1 at hl
  unfold margin cB rho3 tripleCoeff
  linarith only [hl, Real.log_two_lt_d9, triple_integral_upper]

theorem margin_positive : 0 < margin :=
  lt_trans (by norm_num : (0:ℝ) < 1/4000) margin_floor

end
end REAL1B.H2

#print axioms REAL1B.H2.triple_integrability
#print axioms REAL1B.H2.triple_integral_upper
#print axioms REAL1B.H2.margin_floor
#print axioms REAL1B.H2.margin_positive

-- RequestProject/REAL1B_20261122/OutputErrors.lean
namespace REAL1B.H2
open ArithmeticFunction Filter Vaughan
noncomputable section
open Classical

private theorem sqrt_half {X : ℝ} (hx : 4 ≤ X) : Real.sqrt X ≤ X/2 := by
  apply (Real.sqrt_le_iff).2
  constructor
  · linarith
  · nlinarith [mul_nonneg (show 0 ≤ X by linarith) (show 0 ≤ X-4 by linarith)]

private theorem t_above {X : ℝ} {n : ℕ} (hx : 4 ≤ X) (hn : n ∈ interval X) :
    X/2 < ((n-2:ℕ):ℝ) := by
  have h := (Finset.mem_filter.mp hn).2
  have hk : 2 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  rw [Nat.cast_sub hk]
  norm_num at *
  linarith

theorem lowOutput_zero {X : ℝ} (hx : 4 ≤ X) : lowOutput X = 0 := by
  have hu : U X ≤ X/2 := calc
    X ^ (1/5:ℝ) ≤ X ^ (1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ X/2 := by rw [← Real.sqrt_eq_rpow]; exact sqrt_half hx
  unfold lowOutput op total
  apply Finset.sum_eq_zero
  intro n hn
  have ht := hu.trans_lt (t_above hx hn)
  simp [low,not_le.mpr ht]

theorem low_negligible : negligible lowOutput := by
  intro ε he
  filter_upwards [eventually_ge_atTop (4:ℝ)] with X hx
  rw [lowOutput_zero hx,abs_zero]
  exact mul_nonneg he.le (scale_pos (by linarith)).le

private theorem Z_small {X : ℝ} (hx : 4 ≤ X) (hl : 4 ≤ Real.log X) : Z X ≤ X/2 := by
  calc
    Z X ≤ Real.exp (Real.log X / 2) := by
      apply Real.exp_le_exp.mpr
      calc
        Real.log X ^ (0.24:ℝ) ≤ Real.log X ^ (1/2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ ≤ _ := by rw [← Real.sqrt_eq_rpow]; exact sqrt_half hl
    _ = Real.sqrt X := by rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by linarith : 0<X)]; congr 1; ring
    _ ≤ X/2 := sqrt_half hx

private theorem fixed_abs (X : ℝ) (n : ℕ) : |fixed X n| ≤ 1 := by
  unfold fixed
  split_ifs
  · unfold mu
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  · norm_num

/-- Absolute correction on the actual dyadic source, dominated by all proper
prime powers through 2X. The presieve may only delete nonnegative Λ mass. -/
theorem correction_bound {X : ℝ} (hx : 4 ≤ X) (hl : 4 ≤ Real.log X) :
    |primeCorrection X| ≤ 2 * Real.sqrt (2*X) * Real.log (2*X) := by
  let s := interval X
  let g := fun t : ℕ => if t.Prime then 0 else lam t
  have hg (t : ℕ) : 0 ≤ g t := by dsimp [g]; split_ifs <;> first | rfl | exact vonMangoldt_nonneg
  have hb (n : ℕ) (hn : n ∈ s) :
      |fixed X n * (theta (n-2) - sieve (Z X) (n-2) * lam (n-2))| ≤ g (n-2) := by
    rw [abs_mul]
    by_cases h : (n-2).Prime
    · have hz := (Z_small hx hl).trans_lt (t_above hx hn)
      have hs : Sifted (Z X) (n-2) := by
        intro p hp hd
        rcases (Nat.dvd_prime h).mp hd with rfl | rfl
        · exact (hp.ne_one rfl).elim
        · exact hz
      simp [g,theta,h,sieve,hs,lam,vonMangoldt_apply_prime h]
    · have hΛ : 0 ≤ lam (n-2) := vonMangoldt_nonneg
      by_cases hR : Sifted (Z X) (n-2)
      · simpa [g,theta,h,sieve,hR,abs_of_nonneg hΛ] using
          (mul_le_mul_of_nonneg_right (fixed_abs X n) hΛ)
      · simp [g,theta,h,sieve,hR,hΛ]
  have hinj : Set.InjOn (fun n : ℕ => n-2) (↑s : Set ℕ) := by
    intro a ha b hb he
    have hlo (k : ℕ) (hk : k ∈ s) : 2 ≤ k :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have := hlo a ha
    have := hlo b hb
    change a-2=b-2 at he
    omega
  have hsub : s.image (fun n : ℕ => n-2) ⊆ Finset.Ioc 0 ⌊2*X⌋₊ := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    have hk := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have ht := t_above hx hn
    have hp : 0 < ((n-2:ℕ):ℝ) := by linarith
    exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hp, by omega⟩
  calc
    |primeCorrection X| ≤ _ := by unfold primeCorrection total; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ s, g (n-2) := Finset.sum_le_sum hb
    _ = ∑ t ∈ s.image (fun n : ℕ => n-2), g t := (Finset.sum_image hinj).symm
    _ ≤ ∑ t ∈ Finset.Ioc 0 ⌊2*X⌋₊, g t := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hg i)
    _ = Chebyshev.psi (2*X) - Chebyshev.theta (2*X) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : t.Prime <;> simp [g,h,lam]
    _ ≤ _ := (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith))

private theorem error_small (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, 2 * Real.sqrt (2*X) * Real.log (2*X) ≤ ε * N0 X := by
  have hc := mul_pos he series_pos
  have ht : Tendsto (fun X : ℝ => (2*X)^(1/8:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
      (Filter.tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  filter_upwards [ht.eventually_ge_atTop (max 1 (256/(ε*series))), eventually_gt_atTop (1:ℝ)]
    with X hbig hx
  let s := (2*X)^(1/8:ℝ)
  have h1 : 1 ≤ s := (le_max_left _ _).trans hbig
  have hh : 256 ≤ ε*series*s := by
    have h := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hbig)
    linarith
  have hsq : Real.sqrt (2*X) = s^4 := by
    dsimp [s]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by linarith : 0 ≤ 2*X)]
    norm_num
  have h8 : s^8 = 2*X := by
    dsimp [s]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 2*X)]
    norm_num
  have hlog : Real.log (2*X) ≤ 8*s := by
    have h := Real.log_le_rpow_div (x := 2*X) (ε := 1/8) (by linarith) (by norm_num)
    linarith
  have hlogX := Real.log_le_log (by linarith : 0<X) (by linarith : X ≤ 2*X)
  have hlog0 := Real.log_pos hx
  rw [N0, ← mul_div_assoc, le_div_iff₀ hlog0, hsq]
  have hXs : Real.log X ≤ 8*s := hlogX.trans hlog
  have hprod := mul_le_mul hlog hXs hlog0.le (by positivity : 0 ≤ 8*s)
  have hc' : 256 ≤ (ε*series)*s^2 := by
    nlinarith [mul_nonneg (show 0 ≤ ε*series*s by positivity) (sub_nonneg.mpr h1)]
  calc
    2*s^4*Real.log (2*X)*Real.log X ≤ 2*s^4*((8*s)*(8*s)) := by
      rw [mul_assoc (2*s^4)]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ ε*(series*X) := by
      have hh := mul_le_mul_of_nonneg_right hc' (show 0 ≤ s^6 by positivity)
      linear_combination hh/2 + (ε*series/2)*h8

theorem correction_negligible : negligible primeCorrection := by
  intro ε he
  filter_upwards [eventually_ge_atTop (4:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 4,
    error_small ε he] with X hx hl h
  exact (correction_bound hx hl).trans h

end
end REAL1B.H2

#print axioms REAL1B.H2.lowOutput_zero
#print axioms REAL1B.H2.low_negligible
#print axioms REAL1B.H2.correction_bound
#print axioms REAL1B.H2.correction_negligible

-- RequestProject/REAL1B_20261122/SieveInputs.lean
namespace REAL1B.H2
open Filter Vaughan
noncomputable section
open Classical

/-- A fixed choice of centers and signed, finitely supported remainder
coefficients at a scale. In the paper they come from lower/upper linear sieves. -/
structure CenteredRow where
  center : ℝ
  coeff : ℕ →₀ ℝ
def CenteredRow.eval (r : CenteredRow) (n : ℕ) := r.center +
  r.coeff.sum (fun d w => w * ((if d ∣ n then 1 else 0) - (Nat.totient d : ℝ)⁻¹))

structure H1Rows where
  lower : ℝ → CenteredRow
  upper : ℝ → ℕ → CenteredRow

def markers (X : ℝ) (n : ℕ) := n.primeFactors.filter
  (fun p : ℕ => X < (p:ℝ)^7 ∧ (p:ℝ)^4 ≤ 2*X)
def lowerKernel (r : H1Rows) (X : ℝ) (n : ℕ) := if Odd n then
  (r.lower X).eval n - ∑ p ∈ markers X n, (r.upper X p).eval (n/p) else 0
def squarefreeLower (r : H1Rows) (X : ℝ) := mass X (fun n => mu n ^ 2 * lowerKernel r X n)

/-- Singleton consequences needed of the particular fixed rows. The least marker
requires a unit upper weight; all other markers require nonnegative upper weights. -/
def SingletonBounds (r : H1Rows) (X : ℝ) := ∀ n ∈ interval X, Odd n →
  (r.lower X).eval n ≤ (if X < (n.minFac:ℝ)^7 then 1 else 0) ∧
  (∀ p ∈ markers X n, 0 ≤ (r.upper X p).eval (n/p)) ∧
  (n.minFac ∈ markers X n → 1 ≤ (r.upper X n.minFac).eval (n/n.minFac))

theorem minorant {r : H1Rows} {X : ℝ} (hx : 1 ≤ X) (hs : SingletonBounds r X)
    {n : ℕ} (hn : n ∈ interval X) : lowerKernel r X n ≤ roughMask n := by
  by_cases ho : Odd n
  · obtain ⟨hl,hu,hm⟩ := hs n hn ho
    rw [lowerKernel, if_pos ho]
    have hsum := Finset.sum_nonneg hu
    by_cases hr : Rough n
    · rw [roughMask, if_pos hr]
      split_ifs at hl <;> linarith
    · rw [roughMask, if_neg hr]
      by_cases h7 : X < (n.minFac:ℝ)^7
      · have h4 : n.minFac^4 ≤ n := le_of_not_gt hr
        have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hbig := (Nat.le_floor_iff (by linarith : 0 ≤ 2*X)).mp hi.2
        have hp : n.minFac ∈ markers X n := by
          apply Finset.mem_filter.mpr
          refine ⟨Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd n,by omega⟩,h7,?_⟩
          exact (show (n.minFac:ℝ)^4 ≤ (n:ℝ) by exact_mod_cast h4).trans hbig
        have hb := Finset.single_le_sum (f := fun p => (r.upper X p).eval (n/p)) hu hp
        rw [if_pos h7] at hl
        linarith [hm hp]
      · rw [if_neg h7] at hl
        linarith
  · simp [lowerKernel,ho,roughMask]; split_ifs <;> norm_num

theorem squarefreeLower_le {r : H1Rows} {X : ℝ} (hx : 1 ≤ X) (hs : SingletonBounds r X) :
    squarefreeLower r X ≤ unsigned X := by
  unfold squarefreeLower unsigned
  rw [mass_as_sum, mass_as_sum]
  unfold total
  apply Finset.sum_le_sum
  intro n hn
  have hθ : 0 ≤ theta (n-2) := by
    unfold theta
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · rfl
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (minorant hx hs hn) (sq_nonneg _)) hθ

/-- One row family per fixed tolerance, chosen before the eventual quantifier.
H1's mean estimate and the validity of the constructed sieve rows are inputs. -/
def H1PaperInput : Prop := ∀ ε : ℝ, 0 < ε → ∃ r : H1Rows,
  ∀ᶠ X : ℝ in atTop, SingletonBounds r X ∧ (cB-ε)*N0 X ≤ squarefreeLower r X

theorem h1_consequence (hp : H1PaperInput) : H1Consequence := by
  intro ε he
  obtain ⟨r,hr⟩ := hp ε he
  filter_upwards [hr,eventually_ge_atTop (1:ℝ)] with X h hx
  exact h.2.trans (squarefreeLower_le hx h.1)

/-- Positive population of the fixed-to-relative cutoff collar. -/
def collarMass (X : ℝ) := mass X (fun n =>
  if X < (n.minFac:ℝ)^4 ∧ ¬ Rough n then 1 else 0)

theorem abs_collar_le (X : ℝ) : |collar X| ≤ collarMass X := by
  rw [collarMass, mass_as_sum]
  unfold collar total
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro n hn
  have hx := (Finset.mem_filter.mp hn).2
  have hm : |mu n| ≤ 1 := by unfold mu; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have ht : 0 ≤ theta (n-2) := by
    unfold theta
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · rfl
  simp only [abs_mul, abs_of_nonneg ht]
  apply mul_le_mul_of_nonneg_left _ ht
  by_cases hr : Rough n
  · have h4 : (n:ℝ) < (n.minFac:ℝ)^4 := by exact_mod_cast hr
    simp [native, roughMask, hr, fixed, hx.trans h4]
  · by_cases hf : X < (n.minFac:ℝ)^4 <;> simp [native, roughMask, hr, fixed, hf, hm]

theorem collar_negligible (h : negligible collarMass) : negligible collar := by
  intro ε he
  filter_upwards [h ε he] with X hx
  exact (abs_collar_le X).trans ((le_abs_self _).trans hx)

/-- An explicit conservative conditional reserve using the certified simplex bound. -/
theorem eventual_mass_lower (h₁ : H1Consequence) (h₃ : TripleCap) (hs : GammaBound) :
    ∀ᶠ X : ℝ in atTop, N0 X / 16000 < mass X primeMask := by
  have hd : (0:ℝ) < 1/32000 := by norm_num
  filter_upwards [h₁ _ hd, h₃ _ hd, hs _ hd, eventually_gt_atTop (1:ℝ)] with X ha ht hg hx
  have hm := mul_lt_mul_of_pos_right margin_floor (scale_pos hx)
  have hi := h2_identity X
  change mass X (fun n => mu n * roughMask n) + rho3 * N0 X ≤ _ at hg
  unfold unsigned at ha
  unfold triple at ht
  unfold margin at hm
  linarith

theorem infinite_of_paper_inputs (h₁ : H1PaperInput) (h₃ : TripleCap)
    (hI : TypeICalibration) (hc : negligible collarMass) (hII : FinalTypeII) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_vaughan margin_positive (h1_consequence h₁) h₃ hI low_negligible
    correction_negligible (collar_negligible hc) hII

end
end REAL1B.H2

#print axioms REAL1B.H2.minorant
#print axioms REAL1B.H2.squarefreeLower_le
#print axioms REAL1B.H2.h1_consequence
#print axioms REAL1B.H2.abs_collar_le
#print axioms REAL1B.H2.collar_negligible
#print axioms REAL1B.H2.eventual_mass_lower
#print axioms REAL1B.H2.infinite_of_paper_inputs

-- RequestProject/REAL1B_20261122/FMSource.lean
/-! Gold 4.53-FM §1 and the literal Gold 4.48-FM Appendix H divisor kernels. -/
namespace REAL1B.FM.Source
open ArithmeticFunction Filter Vaughan
noncomputable section
open Classical

def ε : ℝ := 1 / 10^9
def ν : ℝ := 1/5 - 2*ε
def β : ℝ := 1/2 - 2*ε
def γ : ℝ := 1/2 - ε
def y (x : ℝ) := Real.exp ((Real.log x) ^ (1/20 : ℝ))
def z (x : ℝ) := x ^ (1/400000000000 : ℝ)
def markCut (X : ℝ) := Real.exp (Real.log X / (Real.log (Real.log X))^10)
def density (x : ℝ) := ∏ p ∈ (Finset.range (⌊y x⌋₊+1)).filter Nat.Prime, (1 - (1:ℝ)/p)
def actual (x : ℝ) (n : ℕ) := sieve (y x) n * theta (n-2)
def compare (x : ℝ) (n : ℕ) := sieve (y x) n * sieve (y x) (n-2) / density x

def profile (n : ℕ) (ps : List ℕ) := ps.map (fun p => Real.log p / Real.log n)
def g0 : List ℝ → ℝ
  | [] => 1
  | [t] => if 1/5 < t ∧ t ≤ 1/2 then -1 else 0
  | [t,u] => if 1/5 < t ∧ 1/5 < u ∧ t+u < 1/2 then 1 else 0
  | _ => 0

def divisorCoefficient (n d : ℕ) : ℝ :=
  let small := d.primeFactorsList.filter (fun p : ℕ => decide ((p:ℝ) < (n:ℝ)^ν))
  let big := d.primeFactorsList.filter (fun p : ℕ => decide ((n:ℝ)^ν ≤ (p:ℝ)))
  let ts := profile n big
  if (d:ℝ) ≤ (n:ℝ)^γ ∧ ts.sum ≤ β then mu small.prod * g0 ts else 0
def kernelH (n : ℕ) := ∑ d ∈ n.divisors, divisorCoefficient n d

/-- Coagulation groups coordinates of a fundamental vector into nonempty blocks.
The forbidden closed interval applies to every nonempty proper subsum. -/
def fundamental (v : List ℝ) : Prop :=
  v.sum = 1 ∧ (∀ t ∈ v, 0 < t ∧ t < 1 - γ) ∧
  ∀ u : List ℝ, u.Sublist v → u ≠ [] → u.length < v.length →
    u.sum < ε ∨ ε + ν < u.sum
def good (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∃ blocks : List (List ℝ),
    (∀ b ∈ blocks, b ≠ []) ∧ fundamental blocks.flatten ∧
    (blocks.map List.sum).Perm (profile n n.primeFactorsList)

def inBank (X a b : ℝ) (k : ℕ) : Prop := X^a < (k:ℝ) ∧ (k:ℝ) ≤ X^b
def labels (X : ℝ) (d : ℕ) : ℕ :=
  ∑ u ∈ d.divisors, ∑ v ∈ (d/u).divisors, ∑ w ∈ (d/u/v).divisors,
    if u.Prime ∧ v.Prime ∧ w.Prime ∧ inBank X 0.0265 0.028 u ∧
      inBank X 0.0105 0.0115 v ∧ inBank X 0.0115 0.0125 w ∧
      inBank X 0.463 0.465 (d/u/v/w) then 1 else 0
def kernelK (X : ℝ) (n : ℕ) :=
  mu n ^ 2 * sieve (markCut X) n *
    ∑ d ∈ n.divisors, mu d * ((labels X d : ℝ) / 64^3) *
      (1 - (Real.log d)^2 / (Real.log n)^2)

def retained (n : ℕ) : Prop := cardFactors n = 3 ∨
  (5 ≤ cardFactors n ∧ cardFactors n ≤ 255)
def residual (x : ℝ) := total (x/2) (fun n =>
  if Squarefree n ∧ ¬ good n ∧ Sifted (z x) n ∧ retained n then
    (actual x n - compare x n) * (kernelH n - kernelK (x/2) n) else 0)
def companion (x : ℝ) := total (x/2) (fun n =>
  if Squarefree n ∧ good n then actual x n * max (-kernelH n) 0 else 0)
def T (x : ℝ) := total (x/2) (fun n => actual x n * primeMask n)
def Sb (x : ℝ) := total (x/2) (fun n => compare x n * primeMask n)

private theorem theta_nonneg (t : ℕ) : 0 ≤ theta t := by
  unfold theta
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · rfl

theorem companion_nonneg (x : ℝ) : 0 ≤ companion x := by
  unfold companion total
  apply Finset.sum_nonneg
  intro n _
  unfold actual sieve
  have ht := theta_nonneg (n-2)
  split_ifs <;> positivity

theorem T_le_native (x : ℝ) : T x ≤ mass (x/2) primeMask := by
  rw [mass_as_sum]
  unfold T total
  apply Finset.sum_le_sum
  intro n _
  simp only [actual, sieve]
  by_cases h : Sifted (y x) n
  · simp [h]
  · simp [h, primeMask]
    split_ifs <;> simp [theta_nonneg]

/-- Quantified one-sided comparison and residual hypotheses from 4.53-FM §1. -/
def Lower : Prop := ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
  (0.361755018 - (10:ℝ)⁻¹^58) * Sb x + companion x - residual x - η * Sb x ≤ T x
def ResidualBound : Prop := ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
  residual x - companion x ≤ (0.359892818 + η) * Sb x

theorem infinite_of_source_residual (hL : Lower) (hR : ResidualBound)
    (hS : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  apply infinite_of_unbounded_mass
  intro B
  have he : (0:ℝ) < 0.0001 := by norm_num
  obtain ⟨x,hb,hl,hr,hs⟩ := (Filter.Eventually.and (eventually_gt_atTop (2*(B:ℝ)))
    ((hL _ he).and ((hR _ he).and hS))).exists
  refine ⟨x/2, by linarith, ?_⟩
  have h := REAL1B.FM.current_margin (T x) (Sb x) (companion x) (residual x)
    (0.0001 * Sb x) (0.0001 * Sb x) hl (by linarith)
  have hc : (0:ℝ) < 0.0018622 - (10:ℝ)⁻¹^58 - 2*0.0001 := by norm_num
  linarith only [mul_pos hc hs, h, T_le_native x]

end
end REAL1B.FM.Source

#print axioms REAL1B.FM.Source.companion_nonneg
#print axioms REAL1B.FM.Source.T_le_native
#print axioms REAL1B.FM.Source.infinite_of_source_residual

-- RequestProject/REAL1B_20261122/FMClosing.lean
/-! Gold 4.57–4.60, joint signed route. All finite sums use the larger member
in the physical window (x/2,x]. The FM twin mass uses that same window. -/
namespace REAL1B.FM.Closing
open Filter Vaughan Source
noncomputable section
open Classical

def F (x : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ ¬ good n ∧ Sifted (z x) n ∧ retained n
  then kernelH n - kernelK (x/2) n else 0
def G (n : ℕ) : ℝ := if Squarefree n ∧ good n then max (-kernelH n) 0 else 0
def phi (x : ℝ) (n : ℕ) := F x n - G n

/-- Gold 4.58 (U1), after exact owner counting. -/
def covariance (x : ℝ) :=
  total (x/2) (fun n =>
    (sieve (x ^ (1/800000000000 : ℝ)) (n-2) * lam (n-2) - H2.series) * phi x n)

def primeRow (u d : ℝ) (k l : ℕ) : ℝ :=
  Real.log l * ∑ m ∈ (k/l).divisors,
    if u < (m:ℝ) ∧ d < (m*l:ℕ) then mu m else 0

def coeff (u d : ℝ) (k : ℕ) :=
  ∑ l ∈ k.divisors, if l.Prime ∧ u < (l:ℝ) then primeRow u d k l else 0

/-- Only the distinguished prime can survive the outer sum. -/
theorem one_large_switch {u d : ℝ} {k p : ℕ} (hpk : p ∈ k.divisors)
    (hp : p.Prime) (hu : u < (p:ℝ))
    (honly : ∀ l ∈ k.divisors, l.Prime → u < (l:ℝ) → l = p) :
    coeff u d k = primeRow u d k p := by
  unfold coeff
  rw [Finset.sum_eq_single p]
  · simp [hp, hu]
  · intro l hl hne
    apply if_neg
    rintro ⟨hlp,hlu⟩
    exact hne (honly l hl hlp hlu)
  · simp [hpk]

theorem coeff_prime {u d : ℝ} {p : ℕ} (hp : p.Prime) (hu : 1 ≤ u) :
    coeff u d p = 0 := by
  unfold coeff
  rw [Nat.Prime.divisors hp]
  simp [hp, primeRow, Nat.div_self hp.pos, not_lt.mpr hu]

private theorem semiprime_row {u d : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hu : 1 ≤ u) (hq' : u < (q:ℝ)) (hd : d < (p*q:ℕ)) :
    primeRow u d (p*q) p = - Real.log p := by
  have hd' : d < (q:ℝ)*p := by simpa [Nat.cast_mul, mul_comm] using hd
  have h1 : (1:ℕ) ≠ q := Ne.symm hq.ne_one
  simp [primeRow, Nat.mul_div_cancel_left _ hp.pos, hq.divisors, h1,
    not_lt.mpr hu, hq', hd', mu, ArithmeticFunction.moebius_apply_prime hq]

/-- When both prime divisors survive the cutoffs, their full signed
coefficient is exactly minus log k. Every cofactor choice is retained. -/
theorem coeff_semiprime {u d : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hu : 1 ≤ u) (hup : u < (p:ℝ)) (huq : u < (q:ℝ))
    (hd : d < (p*q:ℕ)) : coeff u d (p*q) = - Real.log (p*q:ℕ) := by
  have hdiv : (p*q).divisors.filter (fun l : ℕ => l.Prime ∧ u < (l:ℝ)) = {p,q} := by
    ext l
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h,_⟩, hl,_⟩
      exact (hl.dvd_mul.mp h).imp (Nat.prime_dvd_prime_iff_eq hl hp).mp
        (Nat.prime_dvd_prime_iff_eq hl hq).mp
    · rintro (rfl | rfl)
      · exact ⟨⟨dvd_mul_right .., Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩,hp,hup⟩
      · exact ⟨⟨dvd_mul_left .., Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩,hq,huq⟩
  have hr := semiprime_row hp hq hu huq hd
  have hd' : d < (q*p:ℕ) := by simpa [Nat.mul_comm] using hd
  have hs := semiprime_row hq hp hu hup hd'
  rw [Nat.mul_comm q p] at hs
  rw [coeff, ← Finset.sum_filter, hdiv, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton, hr, hs, Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  ring

def cutU (x : ℝ) := x ^ (0.24 : ℝ)
def cutD (x : ℝ) := x ^ (0.49 : ℝ)
def roughW (a x : ℝ) := Real.exp (Real.log x ^ a)

def term (a x : ℝ) (n : ℕ) :=
  let k := n-2
  sieve (roughW a x) k * mu k ^ 2 * coeff (cutU x) (cutD x) k * phi x n
def largeProduct (a x : ℝ) := total (x/2) (term a x)

/-- Gold 4.59 Joint Signed, Part A (2.1). The last four comparisons
are written additively to avoid truncated natural subtraction. -/
def admissible (i j k l : ℕ) : Prop :=
  let s := i+j+k+l
  3 ≤ i ∧ i < j ∧ j < k ∧ k < l ∧ l ≤ 48 ∧ i+1 ≤ 19 ∧
    (i+1 ≤ 19 ∨ 21 ≤ i) ∧ (j+1 ≤ 19 ∨ 21 ≤ j) ∧
    (k+1 ≤ 19 ∨ 21 ≤ k) ∧ (l+1 ≤ 19 ∨ 21 ≤ l) ∧
    l+1+s ≤ 96 ∧ s+21 ≤ 96 ∧ 100 ≤ 49+s ∧
    51 ≤ i+k+l ∧ k+l+2 ≤ 49

theorem first_index_lower {i j k l : ℕ} (h : admissible i j k l) : 4 ≤ i := by
  unfold admissible at h
  omega

def inCell (n p i : ℕ) : Prop :=
  (i:ℝ)/100 < Real.log p / Real.log n ∧ Real.log p / Real.log n < ((i:ℝ)+1)/100

/-- The total supplies the physical window. primeFactorsList is ordered with
multiplicity; the fifth coordinate is determined by the full factorization. -/
def boxes (n : ℕ) : Prop := Squarefree n ∧
  ∃ p q r s t i j k l : ℕ, n.primeFactorsList = [p,q,r,s,t] ∧ admissible i j k l ∧
    inCell n p i ∧ inCell n q j ∧ inCell n r k ∧ inCell n s l

/-- The two input-side conditions apply to k=n-2. -/
def inE (x : ℝ) (n : ℕ) :=
  boxes n ∧ Squarefree (n-2) ∧ Sifted (cutU x) (n-2)
def selected (a x : ℝ) :=
  total (x/2) (fun n => if inE x n then term a x n else 0)
def complement (a x : ℝ) :=
  total (x/2) (fun n => if inE x n then 0 else term a x n)
def primeCompanion (x : ℝ) :=
  total (x/2) (fun n => actual x n * (if boxes n then phi x n else 0))
def QE (a x : ℝ) :=
  complement a x + 0.02 * primeCompanion x

theorem source_split (a x : ℝ) :
    largeProduct a x = selected a x + complement a x := by
  unfold largeProduct selected complement total
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : inE x n <;> simp [h]

theorem signed_identity (a x : ℝ) :
    largeProduct a x - QE a x = selected a x - 0.02 * primeCompanion x := by
  rw [source_split a x]
  unfold QE
  ring

/-- Split the literal complement at semiprime inputs with both primes above
U and product above D. The output masks and presieve are evaluated at their
original arguments on both sides of the split. -/
def pairSector (x : ℝ) (n : ℕ) : Prop :=
  ¬ inE x n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n-2 = p*q ∧
    cutU x < (p:ℝ) ∧ cutU x < (q:ℝ) ∧ cutD x < (p*q:ℕ)
def otherComplement (a x : ℝ) := total (x/2) (fun n =>
  if ¬ inE x n ∧ ¬ pairSector x n then term a x n else 0)
def pairWeight (a x : ℝ) (n : ℕ) :=
  sieve (roughW a x) (n-2) * mu (n-2)^2 * Real.log (n-2 : ℕ)
def pairMass (part : ℝ → ℝ) (a x : ℝ) := total (x/2) (fun n =>
  if pairSector x n then pairWeight a x n * part (phi x n) else 0)

theorem pair_weight_nonneg {a x : ℝ} {n : ℕ} (h : pairSector x n) :
    0 ≤ pairWeight a x n := by
  obtain ⟨_, p,q,hp,hq,_,heq,_⟩ := h
  have hpos : 1 ≤ n-2 := by rw [heq]; exact Nat.mul_pos hp.pos hq.pos
  have hg := Real.log_nonneg (by exact_mod_cast hpos : (1:ℝ) ≤ (n-2:ℕ))
  unfold pairWeight sieve
  split_ifs <;> positivity

theorem pair_mass_nonneg (part : ℝ → ℝ) (hpart : ∀ y, 0 ≤ part y) (a x : ℝ) :
    0 ≤ pairMass part a x := by
  unfold pairMass total
  apply Finset.sum_nonneg
  intro n _
  by_cases h : pairSector x n
  · simpa [h] using mul_nonneg (pair_weight_nonneg (a:=a) h) (hpart (phi x n))
  · simp [h]

/-- Negative Phi contributes positively on this semiprime sector. Both pieces
appear with their actual signs before any asymptotic bound is used. -/
theorem complement_pair_balance (a x : ℝ) (hu : 1 ≤ cutU x) :
    QE a x = otherComplement a x + pairMass (fun y => max (-y) 0) a x -
      pairMass (fun y => max y 0) a x + 0.02 * primeCompanion x := by
  unfold QE
  congr 1
  unfold complement otherComplement pairMass total
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : pairSector x n
  · have hkeep := h
    obtain ⟨hn,p,q,hp,hq,hne,hk,hup,huq,hd⟩ := h
    have cf := coeff_semiprime hp hq hne hu hup huq hd
    rw [← hk] at cf
    simp [hkeep, hn, term, cf, pairWeight]
    rcases le_total (phi x n) 0 with hn' | hn'
    · rw [max_eq_left (by linarith), max_eq_right hn']
      ring
    · rw [max_eq_right (by linarith), max_eq_left hn']
      ring
  · by_cases hn : inE x n <;> simp [h, hn]

theorem margin_certificate :
    (0.00048 : ℝ) < 7558755113252227 / 15547490081739244800 ∧
    (0.999892775499 : ℝ) + 0.00048 = 1.000372775499 := by norm_num

/-- Fixed tolerance, then sufficiently large physical scales. -/
def LowerLedger : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  (0.999892775499 - e) * Sb x ≤ covariance x + T x
def Reduction (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  |covariance x - largeProduct a x| ≤ e * Sb x
def Joint (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  selected a x - 0.02 * primeCompanion x ≤ (-0.00048 + e) * Sb x
def ComplementBound (a κ : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, QE a x ≤ (1.000372775499 - κ + e) * Sb x

/-- Equivalent arithmetic target after separating the signed semiprime source.
Both nonnegative semiprime masses occur with their full weights. -/
theorem complement_bound_iff_pair_budget (a κ : ℝ) :
    ComplementBound a κ ↔ ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
      otherComplement a x + pairMass (fun y => max (-y) 0) a x + 0.02 * primeCompanion x ≤
        (1.000372775499 - κ + e) * Sb x + pairMass (fun y => max y 0) a x := by
  have hu : ∀ᶠ x : ℝ in atTop, 1 ≤ cutU x := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact Real.one_le_rpow hx (by norm_num)
  constructor
  · intro h e he
    filter_upwards [hu, h e he] with x hx hq
    rw [complement_pair_balance a x hx] at hq
    linarith
  · intro h e he
    filter_upwards [hu, h e he] with x hx hq
    rw [complement_pair_balance a x hx]
    linarith

theorem eventual_reserve {a κ : ℝ}
    (hl : LowerLedger) (hr : Reduction a) (hj : Joint a) (hq : ComplementBound a κ) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (κ-e) * Sb x ≤ T x := by
  intro e he
  have h : 0 < e/4 := by linarith
  filter_upwards [hl _ h, hr _ h, hj _ h, hq _ h] with x hL hR hJ hQ
  rw [← signed_identity] at hJ
  have hR' := (abs_le.mp hR).2
  linarith only [hL, hR', hJ, hQ]

theorem infinite_of_joint_complement {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hκ : 0 < κ)
    (hl : LowerLedger) (hr : Reduction a) (hj : Joint a) (hq : ComplementBound a κ)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  have h := eventual_reserve hl hr hj hq (κ/2) (by linarith)
  apply infinite_of_unbounded_mass
  intro M
  obtain ⟨x,hx,hT,hS⟩ := ((eventually_gt_atTop (2*(M:ℝ))).and (h.and hs)).exists
  refine ⟨x/2, by linarith, ?_⟩
  exact (mul_pos (by linarith : 0 < κ - κ/2) hS).trans_le (hT.trans (T_le_native x))

end
end REAL1B.FM.Closing

#print axioms REAL1B.FM.Closing.one_large_switch
#print axioms REAL1B.FM.Closing.coeff_prime
#print axioms REAL1B.FM.Closing.coeff_semiprime
#print axioms REAL1B.FM.Closing.first_index_lower
#print axioms REAL1B.FM.Closing.source_split
#print axioms REAL1B.FM.Closing.signed_identity
#print axioms REAL1B.FM.Closing.pair_weight_nonneg
#print axioms REAL1B.FM.Closing.pair_mass_nonneg
#print axioms REAL1B.FM.Closing.complement_pair_balance
#print axioms REAL1B.FM.Closing.margin_certificate
#print axioms REAL1B.FM.Closing.complement_bound_iff_pair_budget
#print axioms REAL1B.FM.Closing.eventual_reserve
#print axioms REAL1B.FM.Closing.infinite_of_joint_complement

-- RequestProject/REAL1B_20261122.lean
/-! Aggregate entry point for the finite REAL 1B proof bank of 22 November 2026.
The fully specified endpoints are H2.infinite_of_paper_inputs and
FM.Source.infinite_of_source_residual. The earlier scalar H2 route below needs the two source estimates on the same unbounded
sequence of scales, with aggregate error small enough to leave a positive margin.
The Ford–Maynard and historical decomposition results are independent modules. -/

namespace REAL1B

/-- Combine the per-scale H2 lower bound with the dyadic infinitude criterion. -/
theorem infinite_of_h2_bounds (h₀ ρ e : ℝ) (N E₁ E₂ : ℝ → ℝ)
    (bounds : ∀ B : ℕ, ∃ X : ℝ, (B : ℝ) < X ∧
      (h₀ - e) * N X - E₁ X ≤
        mass X (fun n => mu n ^ 2 * roughMask n) - 2 * mass X (classMask 3) ∧
      mass X (fun n => mu n * roughMask n) + ρ * N X ≤ N X / 8 + E₂ X ∧
      0 < (h₀ + ρ - e - 1 / 8) * N X - E₁ X - E₂ X) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p + 2).Prime} := by
  apply infinite_of_unbounded_mass
  intro B
  obtain ⟨X, hX, hu, hs, hm⟩ := bounds B
  refine ⟨X, hX, ?_⟩
  have lower := h2_lower X h₀ ρ e (N X) (E₁ X) (E₂ X) hu hs
  linarith

end REAL1B

#print axioms REAL1B.infinite_of_h2_bounds
