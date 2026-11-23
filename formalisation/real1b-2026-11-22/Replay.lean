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

/-- Gold 4.59 Joint Signed, Part A (2.1). Bounds involving 96-s or
100-s are written additively to avoid truncated natural subtraction. -/
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

/-- A subpower input presieve lies below every fixed positive power. -/
theorem log_power_lt_linear {a b : ℝ} (ha : a < 1) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ a < b * Real.log x := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr ha)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually_gt_atTop (1/b), eventually_gt_atTop (1:ℝ)] with x hx hx1
  change 1/b < Real.log x ^ (1-a) at hx
  have hL := Real.log_pos hx1
  have h1 := (div_lt_iff₀ hb).mp hx
  have hsum : Real.log x ^ a * Real.log x ^ (1-a) = Real.log x := by
    rw [← Real.rpow_add hL, show a + (1-a) = 1 by ring, Real.rpow_one]
  nlinarith only [mul_lt_mul_of_pos_left h1 (Real.rpow_pos_of_pos hL a), hsum,
    congrArg (fun t : ℝ => b*t) hsum]

theorem boxes_prime_size {n p : ℕ} (hn : 1 < (n:ℝ)) (hB : boxes n)
    (hp : p.Prime) (hd : p ∣ n) : 0.04 * Real.log n < Real.log p := by
  obtain ⟨_, u,v,r,s,t,i,j,k,l,hf,hidx,hu,_⟩ := hB
  have hmem : p ∈ n.primeFactorsList := (Nat.mem_primeFactorsList_iff_dvd (by
    intro h; norm_num [h] at hn) hp).mpr hd
  have hsort := (Nat.primeFactorsList_sorted n).pairwise
  rw [hf] at hmem hsort
  have hup : u ≤ p := by
    rcases List.mem_cons.mp hmem with he | ht
    · omega
    · exact (List.pairwise_cons.mp hsort).1 p ht
  have huprime : u.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hf]; simp)
  have hlog : Real.log u ≤ Real.log p := Real.log_le_log (by exact_mod_cast huprime.pos) (by exact_mod_cast hup)
  have hfirst : (4:ℝ) ≤ i := by exact_mod_cast first_index_lower hidx
  have hcell := (lt_div_iff₀ (Real.log_pos hn)).mp hu.1
  nlinarith only [hcell, hlog, mul_le_mul_of_nonneg_right hfirst (Real.log_pos hn).le]

/-- On the joint boxes the output presieve in the original prime source
is eventually automatic throughout the physical window. -/
theorem boxes_sifted : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), boxes n → Sifted (y x) n := by
  filter_upwards [log_power_lt_linear (a:=(1/20:ℝ)) (b:=0.01) (by norm_num) (by norm_num),
    eventually_ge_atTop (4:ℝ)] with x hy hx n hn hB p hp hd
  have hn' : x/2 < (n:ℝ) := (Finset.mem_filter.mp hn).2
  have hn1 : (1:ℝ) < n := by linarith
  have hlog := boxes_prime_size hn1 hB hp hd
  have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2 ≤ (n:ℝ))
  have h3 := Real.log_le_log (by linarith : 0 < x) (by linarith : x ≤ 2*(n:ℝ))
  rw [Real.log_mul (by norm_num) (by linarith)] at h3
  unfold y
  rw [← Real.exp_log (by exact_mod_cast hp.pos : (0:ℝ) < p), Real.exp_lt_exp]
  linarith [Real.log_pos hn1]

def rawPrimeCompanion (x : ℝ) :=
  total (x/2) (fun n => theta (n-2) * (if boxes n then phi x n else 0))
theorem prime_companion_eq_raw : ∀ᶠ x : ℝ in atTop, primeCompanion x = rawPrimeCompanion x := by
  filter_upwards [boxes_sifted] with x hx
  unfold primeCompanion rawPrimeCompanion total
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hb : boxes n
  · simp [hb, actual, sieve, hx n hn hb]
  · simp [hb]

/-- The inherited subpower presieve is redundant on the selected input mask. -/
theorem selected_without_presieve {a : ℝ} (ha : a < 1) :
    ∀ᶠ x : ℝ in atTop, selected a x = total (x/2) (fun n => if inE x n then
      mu (n-2)^2 * coeff (cutU x) (cutD x) (n-2) * phi x n else 0) := by
  filter_upwards [log_power_lt_linear (b:=0.24) ha (by norm_num),
    eventually_gt_atTop (1:ℝ)] with x hlog hx
  have hz : roughW a x < cutU x := by
    unfold roughW cutU
    rw [Real.rpow_def_of_pos (show 0 < x by linarith) (0.24:ℝ), Real.exp_lt_exp]
    linarith
  unfold selected total
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : inE x n
  · have hw : Sifted (roughW a x) (n-2) := fun p hp hd => hz.trans (h.2.2 p hp hd)
    simp [h, term, sieve, hw]
  · simp [h]

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

private theorem infinite_of_reserve {κ : ℝ} (hκ : 0 < κ)
    (hR : ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (κ-e) * Sb x ≤ T x)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  have h := hR (κ/2) (by linarith)
  apply infinite_of_unbounded_mass
  intro M
  obtain ⟨x,hx,hT,hS⟩ := ((eventually_gt_atTop (2*(M:ℝ))).and (h.and hs)).exists
  refine ⟨x/2, by linarith, ?_⟩
  exact (mul_pos (by linarith : 0 < κ - κ/2) hS).trans_le (hT.trans (T_le_native x))

theorem infinite_of_joint_complement {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hκ : 0 < κ)
    (hl : LowerLedger) (hr : Reduction a) (hj : Joint a) (hq : ComplementBound a κ)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_reserve hκ (eventual_reserve hl hr hj hq) hs

/-! Gold 4.60 Fouvry boxwise variant, §§B–E. The three analytic inputs below
keep the lower-sieve population, all three short pairs in the positive
exception, and the genuine prime companion on the same source. -/
def triangle (x : ℝ) (k : ℕ) : Prop :=
  ∃ p q r s : ℕ, k.primeFactorsList = [p,q,r,s] ∧
    (p*q:ℕ) ≤ cutD x ∧ (p*r:ℕ) ≤ cutD x ∧ (q*r:ℕ) ≤ cutD x

def inputPopulation (x : ℝ) :=
  total (x/2) (fun n => if inE x n then mu (n-2)^2 * phi x n else 0)
def trianglePopulation (x : ℝ) :=
  total (x/2) (fun n => if inE x n ∧ triangle x (n-2) then mu (n-2)^2 * phi x n else 0)

def SupplyAt (c : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  (c-e) * Sb x ≤ 0.02 * Real.log x * inputPopulation x
def RoughSupply : Prop := SupplyAt 0.0026942415488
def RoughSupply59 : Prop := SupplyAt (68853556/62497500025)
def TriangleCost : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  0.49 * Real.log x * trianglePopulation x ≤ (153125/248769792+e) * Sb x
def CoefficientAssembly (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  selected a x - 0.02 * rawPrimeCompanion x ≤
    0.49 * Real.log x * trianglePopulation x - 0.02 * Real.log x * inputPopulation x + e * Sb x
def Joint60 (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  selected a x - 0.02 * primeCompanion x ≤ (-0.00207+e) * Sb x
def Complement60 (a κ : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  QE a x ≤ (1.001962775499-κ+e) * Sb x

/-- The rational cubic used by the box verifier always rounds the true
logarithmic factor down. The next positive series term makes this strict. -/
theorem cubic_log_lower {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    2 * (z+z^3/3) < Real.log ((1+z)/(1-z)) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one ((abs_of_pos hz).trans_lt hz1)
  have hs := sum_le_hasSum (Finset.range 3) (fun k _ => by positivity) h
  norm_num [Finset.sum_range_succ] at hs
  rw [Real.log_div (by linarith) (by linarith)]
  linarith only [hs, pow_pos hz 5]

theorem boxwise_rounding :
    (0.00207:ℝ) < 0.0026942415488 - 153125/248769792 ∧
    (0.999892775499:ℝ)+0.00207 = 1.001962775499 := by norm_num

/-- Gold 4.59 fixed sieve levels in Part A §7.1, equation (7.5). -/
theorem fixed_level_certificate :
    (68853556/62497500025 : ℝ) - 153125/248769792 =
      7558755113252227/15547490081739244800 := by norm_num

private theorem joint_from_costs {a c margin : ℝ} (hc : margin < c - 153125/248769792)
    (hN : SupplyAt c) (hM : TriangleCost) (hA : CoefficientAssembly a)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
      selected a x - 0.02 * primeCompanion x ≤ (-margin+e) * Sb x := by
  intro e he
  have h : 0 < e/3 := by linarith
  filter_upwards [hN _ h, hM _ h, hA _ h, hs, prime_companion_eq_raw] with x h1 h2 h3 h4 h5
  rw [h5]
  linarith only [h1, h2, h3, mul_lt_mul_of_pos_right hc h4]

theorem joint59_of_source_estimates {a : ℝ} (hN : RoughSupply59) (hM : TriangleCost)
    (hA : CoefficientAssembly a) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) : Joint a :=
  joint_from_costs (fixed_level_certificate.symm ▸ margin_certificate.1) hN hM hA hs

theorem joint60_of_source_estimates {a : ℝ} (hN : RoughSupply) (hM : TriangleCost)
    (hA : CoefficientAssembly a) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) : Joint60 a :=
  joint_from_costs boxwise_rounding.1 hN hM hA hs

theorem gold60_lower {a : ℝ} (hl : LowerLedger) (hr : Reduction a) (hj : Joint60 a) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (1.001962775499-e)*Sb x ≤ QE a x + T x := by
  intro e he
  have h : 0 < e/3 := by linarith
  filter_upwards [hl _ h, hr _ h, hj _ h] with x hL hR hJ
  rw [← signed_identity] at hJ
  linarith only [hL, (abs_le.mp hR).2, hJ]

theorem reserve60 {a κ : ℝ} (hl : LowerLedger) (hr : Reduction a) (hj : Joint60 a)
    (hq : Complement60 a κ) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (κ-e) * Sb x ≤ T x := by
  intro e he
  have h : 0 < e/2 := by linarith
  filter_upwards [gold60_lower hl hr hj _ h, hq _ h] with x hL hQ
  linarith only [hL,hQ]

theorem infinite_of_boxwise_complement {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hκ : 0 < κ)
    (hl : LowerLedger) (hr : Reduction a) (hN : RoughSupply) (hM : TriangleCost)
    (hA : CoefficientAssembly a) (hq : Complement60 a κ) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_reserve hκ (reserve60 hl hr (joint60_of_source_estimates hN hM hA hs) hq) hs


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
#print axioms REAL1B.FM.Closing.log_power_lt_linear
#print axioms REAL1B.FM.Closing.boxes_prime_size
#print axioms REAL1B.FM.Closing.boxes_sifted
#print axioms REAL1B.FM.Closing.prime_companion_eq_raw
#print axioms REAL1B.FM.Closing.selected_without_presieve
#print axioms REAL1B.FM.Closing.margin_certificate
#print axioms REAL1B.FM.Closing.complement_bound_iff_pair_budget
#print axioms REAL1B.FM.Closing.eventual_reserve
#print axioms REAL1B.FM.Closing.infinite_of_joint_complement

#print axioms REAL1B.FM.Closing.boxwise_rounding
#print axioms REAL1B.FM.Closing.joint60_of_source_estimates
#print axioms REAL1B.FM.Closing.gold60_lower
#print axioms REAL1B.FM.Closing.reserve60
#print axioms REAL1B.FM.Closing.infinite_of_boxwise_complement
#print axioms REAL1B.FM.Closing.cubic_log_lower
#print axioms REAL1B.FM.Closing.fixed_level_certificate
#print axioms REAL1B.FM.Closing.joint59_of_source_estimates

-- RequestProject/REAL1B_20261122/FMDirect.lean
/-! Gold 4.65 Parts I–II and Gold 4.66 Part I. Fixed parameters precede the limit.
The good set is the paper's strict assignment on actual ordered prime factors. -/
namespace REAL1B.FM.Direct
open Filter Vaughan Source
noncomputable section
open Classical

def lowerEdge : ℝ := 1/5 - ε
def upperEdge : ℝ := 1/2 + ε

def tinyCost (t : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then t else max (t - r * upperEdge) 0

def rankTest {N : ℕ} (t : Fin N → ℝ) : Prop :=
  ∃ r : Fin N → ℕ, ∑ i, r i ≤ 5 ∧
    (∀ i, 0 < r i → r i * lowerEdge < t i) ∧ ∑ i, tinyCost (t i) (r i) < ε

def good (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime ∧
  rankTest (fun i : Fin n.primeFactorsList.length =>
    Real.log (n.primeFactorsList.get i) / Real.log n)

def F (x : ℝ) (n : ℕ) : ℝ :=
  if n ∈ interval (x/2) ∧ Squarefree n ∧ ¬ Direct.good n ∧ Sifted (z x) n ∧ retained n
  then kernelH n - kernelK (x/2) n else 0
def G (x : ℝ) (n : ℕ) : ℝ :=
  if n ∈ interval (x/2) ∧ Squarefree n ∧ Direct.good n then max (-kernelH n) 0 else 0
def phi (x : ℝ) (n : ℕ) := F x n - G x n
def psi (x : ℝ) (n : ℕ) := if Closing.boxes n then phi x n else 0
def outsideProfile (x : ℝ) (n : ℕ) := phi x n - psi x n

def largeSum (a x : ℝ) (f : ℕ → ℝ) := total (x/2) (fun n =>
  sieve (Closing.roughW a x) (n-2) * mu (n-2)^2 *
    Closing.coeff (Closing.cutU x) (Closing.cutD x) (n-2) * f n)
def whole (a x : ℝ) := largeSum a x (phi x)
def box (a x : ℝ) := largeSum a x (psi x)
def outside (a x : ℝ) := largeSum a x (outsideProfile x)
def primeBox (x : ℝ) := total (x/2) (fun n => actual x n * psi x n)

theorem source_split (a x : ℝ) : whole a x = box a x + outside a x := by
  unfold whole box outside largeSum total outsideProfile
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem outside_eq_mask (x : ℝ) (n : ℕ) :
    outsideProfile x n = if Closing.boxes n then 0 else phi x n := by
  by_cases h : Closing.boxes n <;> simp [outsideProfile, psi, h]

/- Ordered four-dimensional integral of (B7); the fifth coordinate is dependent. -/
def boxDomain (t : Fin 4 → ℝ) : Prop :=
  ∃ b : Fin 4 → ℕ, Closing.admissible (b 0) (b 1) (b 2) (b 3) ∧
    ∀ i, (b i : ℝ)/100 < t i ∧ t i < ((b i : ℝ)+1)/100

def face (t s : ℝ) : ℝ :=
  (if 1/2 + (if 1/5 < t then 2 else 1) * ε ≤ s then 1 else 0) +
    (if 1/2 - ε < s then 1 else 0)

def profileH (t : Fin 4 → ℝ) : ℝ :=
  2 + face (t 2) (t 0 + t 1 + t 3) + face (t 3) (t 0 + t 1 + t 2)

def J : ℝ := ∫ t : Fin 4 → ℝ, if boxDomain t then
  profileH t / ((∏ i, t i) * (1 - ∑ i, t i)) else 0

def cStar : ℝ := 17/5 * 1.000081
def enclosure : ℝ := 28449989344325252602 / 10^20

theorem splice_arithmetic :
    cStar = 3.4002754 ∧ (cStar-1)*enclosure = 0.682878095534460334193665908 ∧
    (0.682878095534460334193665908 : ℝ) < 0.682878095535 ∧
    (0.999892775499 : ℝ) - 0.682878095535 = 0.317014679964 := by
  norm_num [cStar, enclosure]

theorem five_factor_rounding (h : J ≤ enclosure) :
    (cStar-1)*J ≤ 0.682878095534460334193665908 := by
  rw [← splice_arithmetic.2.1]
  exact mul_le_mul_of_nonneg_left h (by norm_num [cStar])

def Calibration (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  |box a x - (primeBox x - J * Sb x)| ≤ e * Sb x
def ProfileUpper : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  primeBox x ≤ (cStar*J + e) * Sb x
def BoxPayment (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  box a x ≤ (0.682878095535 + e) * Sb x
def LowerLedger (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  (0.999892775499-e) * Sb x ≤ whole a x + T x
def OutsideBound (a κ : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  outside a x ≤ (0.317014679964-κ+e) * Sb x

theorem box_payment {a : ℝ} (hc : Calibration a) (hp : ProfileUpper)
    (hj : J ≤ enclosure) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) : BoxPayment a := by
  intro e he
  have h : 0 < e/2 := by linarith
  filter_upwards [hc _ h, hp _ h, hs] with x hC hP hS
  have hbound := mul_le_mul_of_nonneg_right
    ((five_factor_rounding hj).trans splice_arithmetic.2.2.1.le) hS.le
  linarith only [(abs_le.mp hC).2, hP, hbound]

theorem reserve {a κ : ℝ} (hl : LowerLedger a) (hb : BoxPayment a)
    (ho : OutsideBound a κ) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (κ-e)*Sb x ≤ T x := by
  intro e he
  have h : 0 < e/3 := by linarith
  filter_upwards [hl _ h, hb _ h, ho _ h] with x hL hB hO
  rw [source_split] at hL
  linarith only [hL, hB, hO]

theorem eventual_positive {a κ : ℝ} (hk : 0 < κ) (hl : LowerLedger a)
    (hb : BoxPayment a) (ho : OutsideBound a κ) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    ∀ᶠ x : ℝ in atTop, 0 < T x := by
  filter_upwards [reserve hl hb ho (κ/2) (by linarith), hs] with x ht hS
  exact (mul_pos (by linarith : 0 < κ-κ/2) hS).trans_le ht

theorem infinite_of_direct {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hk : 0 < κ)
    (hl : LowerLedger a) (hb : BoxPayment a) (ho : OutsideBound a κ)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  apply infinite_of_unbounded_mass
  intro M
  obtain ⟨x,hx,hT⟩ := ((eventually_gt_atTop (2*(M:ℝ))).and
    (eventual_positive hk hl hb ho hs)).exists
  exact ⟨x/2, by linarith, hT.trans_le (T_le_native x)⟩

end
end REAL1B.FM.Direct

#print axioms REAL1B.FM.Direct.source_split
#print axioms REAL1B.FM.Direct.outside_eq_mask
#print axioms REAL1B.FM.Direct.splice_arithmetic
#print axioms REAL1B.FM.Direct.five_factor_rounding
#print axioms REAL1B.FM.Direct.box_payment
#print axioms REAL1B.FM.Direct.reserve
#print axioms REAL1B.FM.Direct.eventual_positive
#print axioms REAL1B.FM.Direct.infinite_of_direct

-- RequestProject/REAL1B_20261122/FMOwners.lean
/-! Gold 4.66. Complete the Möbius sum before regrouping prime owners. -/
namespace REAL1B.FM.Owners
open ArithmeticFunction Vaughan Closing
noncomputable section
open Classical

theorem total_mu (r : ℕ) : ∑ m ∈ r.divisors, mu m = if r = 1 then 1 else 0 := by
  calc
    _ = (mob * zetaR) r := (coe_mul_zeta_apply (f := mob) (x := r)).symm
    _ = _ := by rw [show mob * zetaR = 1 from coe_moebius_mul_coe_zeta, one_apply]

def truncated (E : ℝ) (r : ℕ) := ∑ m ∈ r.divisors, if (m:ℝ) ≤ E then mu m else 0

theorem divisor_complement (r : ℕ) (E : ℝ) :
    (∑ m ∈ r.divisors, if E < (m:ℝ) then mu m else 0) =
      (if r = 1 then 1 else 0) - truncated E r := by
  rw [eq_sub_iff_add_eq, ← total_mu, truncated, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by
    by_cases h : E < (m:ℝ) <;> simp [h, le_of_not_gt, not_le.mpr])

def edge (u d : ℝ) (l : ℕ) := max u (d/l)
def boundary (u : ℝ) (k : ℕ) : ℝ := if k.Prime ∧ u < (k:ℝ) then Real.log k else 0
def debt (u d : ℝ) (k : ℕ) := ∑ l ∈ k.primeFactors,
  if u < (l:ℝ) then Real.log l * truncated (edge u d l) (k/l) else 0

theorem owner_row {u d : ℝ} {k l : ℕ} (hl : l.Prime) :
    primeRow u d k l = Real.log l *
      ((if k/l = 1 then 1 else 0) - truncated (edge u d l) (k/l)) := by
  rw [← divisor_complement]
  unfold primeRow
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have hpos : (0:ℝ) < l := by exact_mod_cast hl.pos
  simp [edge, div_lt_iff₀ hpos, Nat.cast_mul]

private theorem coeff_over_factors (u d : ℝ) (k : ℕ) :
    coeff u d k = ∑ l ∈ k.primeFactors, if u < (l:ℝ) then primeRow u d k l else 0 := by
  have hf : k.divisors.filter Nat.Prime = k.primeFactors := by
    ext l
    simp [Nat.mem_divisors, and_comm, and_left_comm]
  rw [← hf, Finset.sum_filter]
  unfold coeff
  exact Finset.sum_congr rfl (fun l _ => by by_cases h : l.Prime <;> simp [h])

/-- The all-owner boundary occurs exactly at a genuine prime input. Strict
cutoffs are dual to the weak cutoff in each omitted truncated. -/
theorem coeff_complement (u d : ℝ) (k : ℕ) : coeff u d k = boundary u k - debt u d k := by
  have rowBoundary : (∑ l ∈ k.primeFactors, if l = k then boundary u k else 0) =
      boundary u k := by
    by_cases h : k.Prime
    · simp [h.mem_primeFactors (dvd_refl k) h.ne_zero]
    · simp [boundary, h]
  rw [eq_sub_iff_add_eq, coeff_over_factors, debt, ← Finset.sum_add_distrib, ← rowBoundary]
  apply Finset.sum_congr rfl
  intro l hl
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hl
  have he : k/l = 1 ↔ l = k := by
    constructor
    · intro h
      simpa [h] using Nat.div_mul_cancel hd
    · rintro rfl
      exact Nat.div_self hp.pos
  rw [owner_row hp]
  by_cases hk : l = k
  · subst k
    by_cases h : u < (l:ℝ) <;> simp [he, h, boundary, hp]
    ring
  · by_cases h : u < (l:ℝ) <;> simp [he, h, hk]

/-- Large extra factors cannot occur in a divisor at or below E. -/
private theorem truncated_large_factor {N r : ℕ} {E : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hlarge : ∀ p ∈ N.primeFactors, E < (p:ℝ)) :
    truncated E (N*r) = truncated E r := by
  have hsets : (N*r).divisors.filter (fun m : ℕ => (m:ℝ) ≤ E) =
      r.divisors.filter (fun m : ℕ => (m:ℝ) ≤ E) := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,_⟩, hcut⟩
      have hm := Nat.pos_of_dvd_of_pos hd (Nat.mul_pos hN hr)
      have hc : m.Coprime N := by
        by_contra hn
        obtain ⟨p,hp,hm',hN'⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
        have hpm : (p:ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd hm hm'
        exact (not_lt_of_ge (hpm.trans hcut)) (hlarge p (hp.mem_primeFactors hN' hN.ne'))
      exact ⟨⟨hc.dvd_of_dvd_mul_left hd, hr.ne'⟩, hcut⟩
    · rintro ⟨⟨hd,_⟩, hcut⟩
      exact ⟨⟨dvd_mul_of_dvd_right hd N, (Nat.mul_pos hN hr).ne'⟩, hcut⟩
  simpa only [truncated, ← Finset.sum_filter] using congrArg
    (fun s : Finset ℕ => ∑ m ∈ s, mu m) hsets

/-- Gold 4.66 Part V (2.2). M has at least one owner; M=P gives (2.1).
The quotient r need not be squarefree for this finite identity. -/
theorem large_owners {M r : ℕ} {u d : ℝ} (hu : 0 < u)
    (hM : 1 < M) (hr : 1 < r) (hs : Squarefree M) (hc : M.Coprime r)
    (hlarge : ∀ p ∈ M.primeFactors, max u (d/u) < (p:ℝ)) :
    coeff u d (M*r) = -Real.log M * truncated u r + coeff u d r - boundary u r := by
  have hMp : 0 < M := by omega
  have hrp : 0 < r := by omega
  have cuts (p : ℕ) (hp : p ∈ M.primeFactors) :
      u < (p:ℝ) ∧ d < (p:ℝ)*u := by
    obtain ⟨h₁,h₂⟩ := max_lt_iff.mp (hlarge p hp)
    exact ⟨h₁, (div_lt_iff₀ hu).mp h₂⟩
  let cost (k l : ℕ) : ℝ := if u < (l:ℝ) then Real.log l * truncated (edge u d l) (k/l) else 0
  have owner (l : ℕ) (hl : l ∈ M.primeFactors) :
      cost (M*r) l = Real.log l * truncated u r := by
    obtain ⟨hlp,hld,_⟩ := Nat.mem_primeFactors.mp hl
    obtain ⟨hlu,hldu⟩ := cuts l hl
    have hpos : (0:ℝ) < l := hu.trans hlu
    have he : edge u d l = u := max_eq_left ((div_le_iff₀ hpos).mpr (by linarith))
    have hq : (M*r)/l = (M/l)*r := by rw [Nat.mul_comm M r, Nat.mul_div_assoc _ hld, Nat.mul_comm]
    have hdiv : M/l ∣ M := Nat.div_dvd_of_dvd hld
    have hqpos := Nat.div_pos (Nat.le_of_dvd hMp hld) hlp.pos
    simp only [cost, if_pos hlu, he, hq]
    rw [truncated_large_factor hqpos hrp (fun p hp =>
      (cuts p (Nat.primeFactors_mono hdiv hMp.ne' hp)).1)]
  have cofactor (l : ℕ) (hl : l ∈ r.primeFactors) : cost (M*r) l = cost r l := by
    obtain ⟨hlp,hld,_⟩ := Nat.mem_primeFactors.mp hl
    by_cases h : u < (l:ℝ)
    · simp only [cost, if_pos h, Nat.mul_div_assoc M hld]
      congr 1
      apply truncated_large_factor hMp (Nat.div_pos (Nat.le_of_dvd hrp hld) hlp.pos)
      intro p hp
      obtain ⟨hpu,hpd⟩ := cuts p hp
      exact max_lt_iff.mpr ⟨hpu, (div_lt_iff₀ (hu.trans h)).mpr
        (hpd.trans (mul_lt_mul_of_pos_left h (hu.trans hpu)))⟩
    · simp [cost, h]
  have hlog : ∑ p ∈ M.primeFactors, Real.log p = Real.log M := by
    rw [← Real.log_prod (s := M.primeFactors) (f := fun p : ℕ => (p:ℝ)) (fun p hp => (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero :
      (p : ℝ) ≠ 0)), ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hs]
  have debt_eq : debt u d (M*r) = Real.log M * truncated u r + debt u d r := by
    change ∑ l ∈ (M*r).primeFactors, cost (M*r) l = _ + ∑ l ∈ r.primeFactors, cost r l
    rw [hc.primeFactors_mul, Finset.sum_union hc.disjoint_primeFactors,
      Finset.sum_congr rfl owner, Finset.sum_congr rfl cofactor, ← Finset.sum_mul, hlog]
  have hb : boundary u (M*r) = 0 := by simp [boundary, Nat.not_prime_mul hM.ne' hr.ne']
  rw [coeff_complement u d (M*r), hb, debt_eq, coeff_complement u d r]
  ring

end
end REAL1B.FM.Owners

#print axioms REAL1B.FM.Owners.total_mu
#print axioms REAL1B.FM.Owners.divisor_complement
#print axioms REAL1B.FM.Owners.owner_row
#print axioms REAL1B.FM.Owners.coeff_complement
#print axioms REAL1B.FM.Owners.large_owners

-- RequestProject/REAL1B_20261122/FMSemantics.lean
/-! Compare the fundamental-vector and strict rank-assignment presentations. -/
namespace REAL1B.FM.Direct
open Source Filter
noncomputable section
open Classical

private def tiny (v : List ℝ) := (v.map (fun t => if t < ε then t else 0)).sum
private def countBig (v : List ℝ) := (v.map (fun t => if t < ε then (0:ℕ) else 1)).sum

private theorem edges : 0 < ε ∧ 2*ε < lowerEdge ∧ lowerEdge < upperEdge ∧
    upperEdge < 1 ∧ 1 < 6*lowerEdge := by norm_num [lowerEdge, upperEdge, ε]

private theorem tiny_mono {u v : List ℝ} (h : u.Sublist v) (hp : ∀ t ∈ v, 0 ≤ t) :
    tiny u ≤ tiny v := by
  induction h with
  | slnil => rfl
  | cons x h ih =>
    have h' := ih (fun t ht => hp t (by simp [ht]))
    have h0 := hp x (by simp)
    simp only [tiny, List.map_cons, List.sum_cons] at *
    split_ifs <;> linarith
  | cons₂ x h ih =>
    simpa [tiny] using ih (fun t ht => hp t (by simp [ht]))

private theorem fundamental_shape (v : List ℝ) :
    fundamental v ↔ v.sum = 1 ∧ (∀ t ∈ v, 0 < t ∧ t < upperEdge ∧ (t < ε ∨ lowerEdge < t)) ∧
      tiny v < ε := by
  have h₁ : ε + ν = lowerEdge := by unfold ν lowerEdge; ring
  have h₂ : 1-γ = upperEdge := by unfold γ upperEdge; ring
  constructor
  · rintro ⟨hs, ht, hsub⟩
    have gap (w : List ℝ) (hw : w.Sublist v) : w.sum < ε ∨ lowerEdge < w.sum := by
      by_cases he : w = []
      · simpa [he] using Or.inl edges.1
      by_cases hlt : w.length < v.length
      · simpa [h₁] using hsub w hw he hlt
      · rw [hw.eq_of_length_le (le_of_not_gt hlt), hs]
        exact Or.inr (edges.2.2.1.trans edges.2.2.2.1)
    refine ⟨hs, fun t h => ⟨(ht t h).1, h₂ ▸ (ht t h).2, ?_⟩, ?_⟩
    · simpa using gap [t] (List.singleton_sublist.mpr h)
    · have small (w : List ℝ) (hw : w.Sublist v) (htiny : ∀ t ∈ w, t < ε) : w.sum < ε := by
        induction w with
        | nil => simpa using edges.1
        | cons t w ih =>
          have hh := htiny t (by simp)
          have hsum := ih ((List.sublist_cons_self t w).trans hw) (fun q hq => htiny q (by simp [hq]))
          rcases gap (t::w) hw with h | h
          · exact h
          · simp only [List.sum_cons] at *
            linarith only [hh, hsum, h, edges.2.1]
      have eqv (w : List ℝ) : tiny w = (w.filter (fun t => decide (t < ε))).sum := by
        induction w with
        | nil => rfl
        | cons t w ih => by_cases h : t < ε <;> simp_all [tiny]
      rw [eqv]
      exact small _ List.filter_sublist (fun t h => of_decide_eq_true (List.mem_filter.mp h).2)
  · rintro ⟨hs, ht, hcost⟩
    refine ⟨hs, fun t h => ⟨(ht t h).1, h₂.symm ▸ (ht t h).2.1⟩, ?_⟩
    intro w hsub _ _
    rw [h₁]
    by_cases h : ∀ t ∈ w, t < ε
    · have he : tiny w = w.sum := by
        unfold tiny
        congr 1
        exact (List.map_congr_left (g := id) (fun t ht => if_pos (h t ht))).trans (List.map_id w)
      exact Or.inl (he ▸ (tiny_mono hsub (fun t h => (ht t h).1.le)).trans_lt hcost)
    · push_neg at h
      obtain ⟨t, htw, hte⟩ := h
      have hbig := ((ht t (hsub.subset htw)).2.2).resolve_left (not_lt.mpr hte)
      exact Or.inr (hbig.trans_le (List.single_le_sum (fun y hy => (ht y (hsub.subset hy)).1.le) _ htw))

/-- Explicit positive tiny allocations and strictly interior equal macro pieces.
This formulation makes the strict upper face of a fundamental coordinate visible. -/
def allocations {N : ℕ} (t : Fin N → ℝ) : Prop :=
  ∃ (r : Fin N → ℕ) (d : Fin N → ℝ), ∑ i, r i ≤ 5 ∧ ∑ i, d i < ε ∧
    ∀ i, 0 < d i ∧ (if r i = 0 then d i = t i else
      r i * lowerEdge < t i - d i ∧ t i - d i < r i * upperEdge)

theorem rank_iff_allocations {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i, 0 < t i) :
    rankTest t ↔ allocations t := by
  constructor
  · rintro ⟨r,hr,hl,hc⟩
    let c := fun i => tinyCost (t i) (r i)
    let η := (ε - ∑ i, c i) / ((N:ℝ)+1)
    have hden : 0 < (N:ℝ)+1 := by positivity
    have hη : 0 < η := div_pos (sub_pos.mpr hc) hden
    let bonus := fun i => if r i = 0 then 0 else min η ((t i - c i - r i * lowerEdge)/2)
    have room (i) (hi : r i ≠ 0) : r i * lowerEdge < t i - c i := by
      have h₁ := hl i (Nat.pos_of_ne_zero hi)
      have h₂ := mul_lt_mul_of_pos_left edges.2.2.1 (by exact_mod_cast Nat.pos_of_ne_zero hi : 0 < (r i:ℝ))
      simp only [c, tinyCost, if_neg hi]
      rcases le_total (t i - r i * upperEdge) 0 with h|h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    refine ⟨r, fun i => c i + bonus i, hr, ?_, ?_⟩
    · have hb : ∑ i, bonus i ≤ ∑ _ : Fin N, η := Finset.sum_le_sum (fun i _ => by
        by_cases h : r i = 0 <;> simp [bonus, h, hη.le])
      have heta : η*((N:ℝ)+1) = ε - ∑ i, c i := div_mul_cancel₀ _ hden.ne'
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
      rw [Finset.sum_add_distrib]
      linarith only [hb, heta, hη]
    · intro i
      by_cases hi : r i = 0
      · simp [bonus, c, tinyCost, hi, ht i]
      · have hroom := room i hi
        have hb : 0 < bonus i := by simp [bonus, hi, hη, show 0 < (t i-c i-r i*lowerEdge)/2 by linarith]
        have hb' : bonus i ≤ (t i-c i-r i*lowerEdge)/2 := by simp [bonus, hi]
        have hc₀ : 0 ≤ c i := by simp [c, tinyCost, hi]
        have hc₁ : t i - r i*upperEdge ≤ c i := by simp [c, tinyCost, hi]
        simp only [if_neg hi]
        exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨r,d,hr,hd,h⟩
    refine ⟨r, hr, fun i hi => ?_, lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => ?_)) hd⟩
    · have hh := (h i).2
      rw [if_neg (Nat.ne_of_gt hi)] at hh
      linarith only [(h i).1, hh.1]
    · have hh := (h i).2
      by_cases hi : r i = 0
      · rw [if_pos hi] at hh
        simpa [tinyCost, hi] using hh.symm.le
      · rw [if_neg hi] at hh
        simp only [tinyCost, if_neg hi, max_le_iff]
        exact ⟨by linarith only [hh.2], (h i).1.le⟩

private def Shape (v : List ℝ) : Prop := ∀ t ∈ v, 0 < t ∧ t < upperEdge ∧ (t < ε ∨ lowerEdge < t)

private theorem block_stats (v : List ℝ) (h : Shape v) :
    0 ≤ tiny v ∧ countBig v * lowerEdge ≤ v.sum - tiny v ∧
    (countBig v = 0 ∨ countBig v * lowerEdge < v.sum - tiny v) ∧
    v.sum - tiny v ≤ countBig v * upperEdge := by
  induction v with
  | nil => simp [tiny, countBig]
  | cons t v ih =>
    obtain ⟨hpos,hupper,hgap⟩ := h t (by simp)
    obtain ⟨ht,hl,hs,hu⟩ := ih (fun y hy => h y (by simp [hy]))
    by_cases he : t < ε
    · have a : tiny (t::v) = t + tiny v := by simp [tiny, he]
      have b : countBig (t::v) = countBig v := by simp [countBig, he]
      rw [a,b,List.sum_cons]
      exact ⟨by linarith, by linarith, hs.imp_right (by intro; linarith), by linarith⟩
    · have a : tiny (t::v) = tiny v := by simp [tiny, he]
      have b : countBig (t::v) = 1 + countBig v := by simp [countBig, he]
      have hg := hgap.resolve_left he
      rw [a,b,List.sum_cons,Nat.cast_add,Nat.cast_one]
      exact ⟨ht, by linarith, Or.inr (by linarith), by linarith⟩

private theorem tiny_flat (v : List (List ℝ)) : tiny v.flatten = (v.map tiny).sum := by
  induction v with
  | nil => rfl
  | cons b v ih => simpa [tiny, List.sum_append] using congrArg (fun s => tiny b + s) ih

private theorem sum_blocks {N : ℕ} (B : Fin N → List ℝ) :
    (List.ofFn B).flatten.sum = ∑ i, (B i).sum := by
  simp [List.sum_flatten, List.map_ofFn, Function.comp_def, List.sum_ofFn]

private theorem cost_blocks {N : ℕ} (B : Fin N → List ℝ) :
    tiny (List.ofFn B).flatten = ∑ i, tiny (B i) := by
  simp [tiny_flat, List.map_ofFn, Function.comp_def, List.sum_ofFn]

private theorem rank_of_blocks {N : ℕ} {t : Fin N → ℝ} (B : Fin N → List ℝ)
    (hB : fundamental (List.ofFn B).flatten) (he : ∀ i, (B i).sum = t i) : rankTest t := by
  obtain ⟨ht,hs,hc⟩ := (fundamental_shape _).mp hB
  have stats i := block_stats (B i) (fun y hy => hs y (List.mem_flatten.mpr
    ⟨B i, List.mem_ofFn.mpr ⟨i,rfl⟩, hy⟩))
  have hbudget : (∑ i, (countBig (B i):ℝ)) * lowerEdge ≤ 1 := by
    rw [← ht, sum_blocks, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    linarith only [(stats i).2.1, (stats i).1]
  refine ⟨fun i => countBig (B i), ?_, ?_, ?_⟩
  · by_contra! h
    have h6 : 6 ≤ ∑ i, (countBig (B i):ℝ) := by exact_mod_cast h
    have hpos : 0 < lowerEdge := by linarith only [edges.1, edges.2.1]
    linarith only [mul_le_mul_of_nonneg_right h6 hpos.le, edges.2.2.2.2, hbudget]
  · intro i hi
    rw [← he i]
    linarith only [((stats i).2.2.1.resolve_left hi.ne'), (stats i).1]
  · rw [cost_blocks] at hc
    refine lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => ?_)) hc
    rw [← he i]
    by_cases h : countBig (B i) = 0
    · have h' := (stats i).2.2.2
      simpa [tinyCost, h] using (show (B i).sum ≤ tiny (B i) by simpa [h] using h')
    · simpa [tinyCost, h] using And.intro
        (show (B i).sum - (countBig (B i):ℝ)*upperEdge ≤ tiny (B i) by linarith only [(stats i).2.2.2])
        (stats i).1

private theorem blocks_of_rank {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i, 0 < t i)
    (htot : ∑ i, t i = 1) (h : rankTest t) :
    ∃ B : Fin N → List ℝ, (∀ i, B i ≠ []) ∧ fundamental (List.ofFn B).flatten ∧
      ∀ i, (B i).sum = t i := by
  obtain ⟨r, d, _, hd, hw⟩ := (rank_iff_allocations ht).mp h
  let v := fun i => (t i - d i) / r i
  let B := fun i => List.replicate (r i) (v i) ++ [d i]
  have hsmall i : d i < ε :=
    (Finset.single_le_sum (fun j _ => (hw j).1.le) (Finset.mem_univ i)).trans_lt hd
  have hmacro i (hi : r i ≠ 0) : lowerEdge < v i ∧ v i < upperEdge := by
    have hp : (0:ℝ) < r i := by exact_mod_cast Nat.pos_of_ne_zero hi
    have hh := (hw i).2
    rw [if_neg hi] at hh
    exact ⟨(lt_div_iff₀ hp).mpr (by linarith only [hh.1]), (div_lt_iff₀ hp).mpr (by linarith only [hh.2])⟩
  have hsum i : (B i).sum = t i := by
    by_cases hi : r i = 0
    · simpa [B, hi] using (show d i = t i by simpa [hi] using (hw i).2)
    · simp [B, v, List.sum_replicate, nsmul_eq_mul, mul_div_cancel₀, hi]
  have hshape i : Shape (B i) := by
    intro y hy
    simp only [B, List.mem_append, List.mem_replicate, List.mem_singleton] at hy
    rcases hy with ⟨hi,rfl⟩ | rfl
    · have hh := hmacro i hi
      exact ⟨by linarith only [edges.1, edges.2.1, hh.1], hh.2, Or.inr hh.1⟩
    · exact ⟨(hw i).1, by linarith only [hsmall i, edges.1, edges.2.1, edges.2.2.1], Or.inl (hsmall i)⟩
  have hcost i : tiny (B i) = d i := by
    by_cases hi : r i = 0
    · simp [B, tiny, hi, hsmall]
    · have hm : ¬ v i < ε := by linarith only [(hmacro i hi).1, edges.1, edges.2.1]
      simp [B, tiny, List.sum_replicate, hm, hsmall]
  refine ⟨B, fun i => by simp [B], (fundamental_shape _).mpr ⟨?_, ?_, ?_⟩, hsum⟩
  · simpa only [sum_blocks, hsum] using htot
  · intro y hy
    obtain ⟨b, hb, hy⟩ := List.mem_flatten.mp hy
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact hshape i y hy
  · simpa only [cost_blocks, hcost] using hd

/-- For a positive normalized vector, the older existential block test is
equivalent to the strict per-coordinate rank test, including both endpoints. -/
theorem coagulation_iff_rank {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i, 0 < t i)
    (hsum : ∑ i, t i = 1) :
    (∃ b : List (List ℝ), (∀ w ∈ b, w ≠ []) ∧ fundamental b.flatten ∧
      (b.map List.sum).Perm (List.ofFn t)) ↔ rankTest t := by
  constructor
  · rintro ⟨b, _, hf, hp⟩
    have order : ∃ w : List (List ℝ), List.ofFn t = w.map List.sum ∧ w.Perm b := by
      change Relation.Comp (fun x y => x = List.map List.sum y) List.Perm (List.ofFn t) b
      rw [List.eq_map_comp_perm]
      exact hp.symm
    obtain ⟨w, hw, hp'⟩ := order
    have hflat : w.flatten.Perm b.flatten := by simpa only [List.flatMap_id] using hp'.flatMap_right id
    obtain ⟨hs, hshape, hc⟩ := (fundamental_shape _).mp hf
    have hwf : fundamental w.flatten := (fundamental_shape _).mpr
      ⟨hflat.sum_eq.trans hs, fun x hx => hshape x (hflat.mem_iff.mp hx),
        (hflat.map (fun y => if y < ε then y else 0)).sum_eq.trans_lt hc⟩
    obtain ⟨K, B, rfl⟩ : ∃ K, ∃ B : Fin K → List ℝ, List.ofFn B = w :=
      ⟨w.length, w.get, List.ofFn_get w⟩
    have hn : N = K := by simpa using congrArg List.length hw
    subst K
    apply rank_of_blocks B hwf
    intro i
    have hmap : List.ofFn t = List.ofFn (fun j => (B j).sum) := by simpa [List.map_ofFn, Function.comp_def] using hw
    exact (congrFun (List.ofFn_injective hmap) i).symm
  · intro h
    obtain ⟨B, hn, hf, he⟩ := blocks_of_rank ht hsum h
    refine ⟨List.ofFn B, ?_, hf, ?_⟩
    · exact List.forall_mem_ofFn_iff.mpr hn
    · simp [List.map_ofFn, Function.comp_def, he]

private theorem normalized {n : ℕ} (hn : 1 < n) :
    ∑ i : Fin n.primeFactorsList.length, Real.log (n.primeFactorsList.get i) / Real.log n = 1 := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rw [← Finset.sum_div, div_eq_one_iff_eq hlog.ne']
  have h : ∀ x ∈ n.primeFactorsList.map (fun p : ℕ => (p:ℝ)), x ≠ 0 := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).ne_zero
  have hh := Real.log_list_prod h
  rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList (by omega)] at hh
  rw [← List.sum_ofFn, hh, List.map_map]
  exact congrArg List.sum ((List.map_ofFn n.primeFactorsList.get (fun p : ℕ => Real.log p)).symm.trans
    (by rw [List.ofFn_get]; rfl))

theorem good_iff_rank_good (n : ℕ) : Source.good n ↔ Direct.good n := by
  unfold Source.good Direct.good
  refine and_congr_right (fun hn => and_congr_right (fun _ => ?_))
  let t := fun i : Fin n.primeFactorsList.length => Real.log (n.primeFactorsList.get i) / Real.log n
  have hp i : 0 < t i := div_pos (Real.log_pos (by exact_mod_cast
    (Nat.prime_of_mem_primeFactorsList (List.get_mem n.primeFactorsList i)).one_lt))
    (Real.log_pos (by exact_mod_cast hn))
  have hd : List.ofFn t = profile n n.primeFactorsList := by
    unfold profile
    change List.ofFn t = (n.primeFactorsList.flatMap (fun p : ℕ => [(p:ℝ)])).map _
    rw [← List.map_eq_flatMap, List.map_map]
    exact (List.map_ofFn n.primeFactorsList.get (fun p : ℕ => Real.log p / Real.log n)).symm.trans
      (by rw [List.ofFn_get]; rfl)
  rw [← hd]
  exact coagulation_iff_rank hp (normalized hn)

theorem phi_eq_legacy {n : ℕ} {x : ℝ} (hn : n ∈ Vaughan.interval (x/2)) :
    phi x n = Closing.phi x n := by
  simp [phi, Closing.phi, F, G, Closing.F, Closing.G, hn, good_iff_rank_good]

theorem whole_eq_legacy (a x : ℝ) : whole a x = Closing.largeProduct a x := by
  unfold whole largeSum Closing.largeProduct Vaughan.total
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Closing.term, phi_eq_legacy hn]

theorem lower_of_covariance {a : ℝ} (hl : Closing.LowerLedger) (hr : Closing.Reduction a) :
    LowerLedger a := by
  intro e he
  have h : 0 < e/2 := by linarith
  filter_upwards [hl _ h, hr _ h] with x hL hR
  rw [whole_eq_legacy]
  linarith only [hL, (abs_le.mp hR).2]

theorem infinite_of_profile_and_outside {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hk : 0 < κ)
    (hl : Closing.LowerLedger) (hr : Closing.Reduction a)
    (hc : Calibration a) (hp : ProfileUpper) (hj : J ≤ enclosure)
    (ho : OutsideBound a κ) (hs : ∀ᶠ x : ℝ in Filter.atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_direct hk (lower_of_covariance hl hr) (box_payment hc hp hj hs) ho hs

end
end REAL1B.FM.Direct
#print axioms REAL1B.FM.Direct.rank_iff_allocations
#print axioms REAL1B.FM.Direct.coagulation_iff_rank
#print axioms REAL1B.FM.Direct.good_iff_rank_good
#print axioms REAL1B.FM.Direct.phi_eq_legacy
#print axioms REAL1B.FM.Direct.whole_eq_legacy
#print axioms REAL1B.FM.Direct.lower_of_covariance
#print axioms REAL1B.FM.Direct.infinite_of_profile_and_outside

-- RequestProject/REAL1B_20261122/FMCompleteLabel.lean
/-! Gold 4.66 Part III, (2), (4), (15). Keep the native outside profile on
both label ranges so that no pointwise output theorem is silently assumed. -/
namespace REAL1B.FM.Direct
open Filter Vaughan Source Closing
noncomputable section
open Classical

def clean (x : ℝ) (n : ℕ) : Prop :=
  n ∈ interval (x/2) ∧ ∃ q h s : ℕ, n = q*h*s ∧ q.Prime ∧ h.Prime ∧ Squarefree s ∧
    inBank x 0.4899 0.490 q ∧ inBank x 0.0199 0.020 h ∧ inBank x 0.4901 0.4902 s ∧
    Sifted (x^(0.031:ℝ)) s ∧ ∀ p : ℕ, p.Prime → p ∣ s →
      (p:ℝ) < x^(0.19999:ℝ) ∨ x^(0.20001:ℝ) < (p:ℝ)

def labelSum (x : ℝ) (k : ℕ) (pick : ℕ → Prop) : ℝ := ∑ l ∈ k.divisors,
  if l.Prime ∧ cutU x < (l:ℝ) ∧ pick l then primeRow (cutU x) (cutD x) k l else 0

def cleanSum (a x : ℝ) (pick : ℕ → Prop) := total (x/2) (fun n =>
  if clean x n then sieve (roughW a x) (n-2) * mu (n-2)^2 * labelSum x (n-2) pick *
    outsideProfile x n else 0)
def lowLabel (a x : ℝ) := cleanSum a x (fun l => (l:ℝ) ≤ x^(0.2697:ℝ))
def unpaid (a x : ℝ) := largeSum a x (fun n => if clean x n then 0 else outsideProfile x n) +
  cleanSum a x (fun l => x^(0.2697:ℝ) < (l:ℝ))

theorem outside_label_split (a x : ℝ) : outside a x = unpaid a x + lowLabel a x := by
  have split (k : ℕ) : coeff (cutU x) (cutD x) k =
      labelSum x k (fun l => x^(0.2697:ℝ) < (l:ℝ)) +
      labelSum x k (fun l => (l:ℝ) ≤ x^(0.2697:ℝ)) := by
    unfold coeff labelSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hp : l.Prime <;> by_cases hu : cutU x < (l:ℝ) <;>
      by_cases h : x^(0.2697:ℝ) < (l:ℝ) <;> simp [hp, hu, h, not_le.mpr, le_of_not_gt]
  unfold outside unpaid lowLabel cleanSum largeSum total
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : clean x n
  · simp only [if_pos h, mul_zero, zero_add, split]
    ring
  · simp [h]

def LowLabelEstimate (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  |lowLabel a x| ≤ e * Sb x

theorem outside_iff_unpaid {a κ : ℝ} (hlo : LowLabelEstimate a) :
    OutsideBound a κ ↔ ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
      unpaid a x ≤ (0.317014679964-κ+e)*Sb x := by
  constructor <;> intro h e he
  · have hε : 0 < e/2 := by linarith
    filter_upwards [h _ hε, hlo _ hε] with x hO hL
    rw [outside_label_split] at hO
    linarith only [hO,(abs_le.mp hL).1]
  · have hε : 0 < e/2 := by linarith
    filter_upwards [h _ hε, hlo _ hε] with x hU hL
    rw [outside_label_split]
    linarith only [hU,(abs_le.mp hL).2]

end
end REAL1B.FM.Direct
#print axioms REAL1B.FM.Direct.outside_label_split
#print axioms REAL1B.FM.Direct.outside_iff_unpaid

-- RequestProject/REAL1B_20261122.lean
/-! Entry point for the REAL 1B proofs of 22–23 November 2026.
The Gold 4.66 endpoint is Direct.infinite_of_direct. The joint FM endpoints are Closing.infinite_of_joint_complement and
Closing.infinite_of_boxwise_complement inside REAL1B.FM.
The earlier FM residual and H2 reductions remain separately callable.
The scalar theorem below consumes both H2 source estimates on one unbounded
sequence of scales, with enough aggregate margin to produce a twin pair. -/
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
