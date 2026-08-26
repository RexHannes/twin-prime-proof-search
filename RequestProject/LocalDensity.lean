import RequestProject.ResidueAwareComparison

open scoped BigOperators

namespace TwinPrimeProject

/-- Exact finite density identity.  The parity factor `1/2` remains visible on
both sides through `V0`. -/
theorem FiniteLocalDensityIdentity (z m : ℕ) :
    (1 / 2 : ℝ) *
        ∏ p ∈ (oddPrimesUpTo z).filter (fun p => ¬ p ∣ m), (1 - (1 : ℝ) / p) =
      V0 z * ResidueAwareDensityFactor z m := by
  rw [V0, ResidueAwareDensityFactor]
  rw [← Finset.prod_filter_mul_prod_filter_not (oddPrimesUpTo z) (fun p => p ∣ m)]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  -- Need to show the product with inverses equals 1
  have h_cancel : (∏ p ∈ oddPrimesUpTo z with p ∣ m, (1 - 1 / (p : ℝ))) *
                  (∏ p ∈ oddPrimesUpTo z with p ∣ m, (1 - 1 / (p : ℝ))⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    rw [mul_inv_cancel₀]
    have hp' : p ∈ oddPrimesUpTo z := Finset.mem_filter.mp hp |>.1
    have hp2 : p > 2 := (Finset.mem_filter.mp hp').2 |>.2
    have hp_ge_3 : (p : ℝ) ≥ 3 := by norm_cast
    have hp_pos : 0 < (p : ℝ) := by linarith
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one hp_pos]; linarith
    linarith
  -- Rearrange RHS
  have h2 : ((∏ p ∈ oddPrimesUpTo z with p ∣ m, (1 - 1 / (p : ℝ))) *
             ((∏ p ∈ oddPrimesUpTo z with ¬p ∣ m, (1 - 1 / (p : ℝ))) *
              ∏ p ∈ oddPrimesUpTo z with p ∣ m, (1 - 1 / (p : ℝ))⁻¹)) =
            ∏ p ∈ oddPrimesUpTo z with ¬p ∣ m, (1 - 1 / (p : ℝ)) := by
    rw [mul_left_comm]
    congr 1
    rw [← mul_assoc, mul_assoc, h_cancel, mul_one]
  rw [h2]

/-- The local factor at `m=1` is one. -/
theorem LocalDensityOne (z : ℕ) : ResidueAwareDensityFactor z 1 = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  simp only [Finset.mem_filter] at hp
  have : p = 1 := Nat.dvd_one.mp hp.2
  have hmem := hp.1
  simp [oddPrimesUpTo, this] at hmem

/-- An odd prime contributes its single inverse Euler factor when it lies in the
sieving range, and contributes `1` otherwise. -/
theorem LocalDensityPrime {z p : ℕ} (hp : Nat.Prime p) (hpodd : 2 < p) :
    ResidueAwareDensityFactor z p =
      if p ≤ z then (1 - (1 : ℝ) / p)⁻¹ else 1 := by
  unfold ResidueAwareDensityFactor
  split_ifs with hle
  · -- Case p ≤ z: the filter contains exactly {p}
    have hp_in : p ∈ oddPrimesUpTo z := by
      simp only [oddPrimesUpTo, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hle, hp, hpodd⟩
    have hfilter : (oddPrimesUpTo z).filter (fun q => q ∣ p) = {p} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hqmem, hqdiv⟩
        have hqprime : Nat.Prime q := (Finset.mem_filter.mp hqmem).2.1
        have := hp.eq_one_or_self_of_dvd q hqdiv
        rcases this with hq1 | hqp
        · linarith [hqprime.two_le]
        · exact hqp
      · intro rfl; exact ⟨hp_in, Nat.dvd_refl _⟩
    rw [hfilter, Finset.prod_singleton]
  · -- Case p > z: the filter is empty
    apply Finset.prod_eq_one
    intro q hq
    have hqmem : q ∈ oddPrimesUpTo z := Finset.mem_filter.mp hq |>.1
    have hqdiv : q ∣ p := Finset.mem_filter.mp hq |>.2
    have := hp.eq_one_or_self_of_dvd q hqdiv
    rcases this with hq1 | hqp
    · have := (Finset.mem_filter.mp hqmem).2.1.two_le; linarith
    · have hqz := (Finset.mem_filter.mp hqmem).1
      simp only [Finset.mem_range] at hqz
      linarith [hqp ▸ hqz]

/-- Positive prime powers have exactly the same local density factor. -/
theorem LocalDensityPrimePower {z p a : ℕ} (ha : 1 ≤ a) :
    ResidueAwareDensityFactor z (p ^ a) = ResidueAwareDensityFactor z p := by
  unfold ResidueAwareDensityFactor
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hqmem, hqpow⟩
    have hprime : Nat.Prime q := (Finset.mem_filter.mp hqmem).2.1
    exact ⟨hqmem, hprime.dvd_of_dvd_pow hqpow⟩
  · rintro ⟨hqmem, hqp⟩
    exact ⟨hqmem, dvd_pow hqp (by omega)⟩

/-- The local density only sees the radical of `m`. -/
theorem LocalDensityDependsOnRadical (z m : ℕ) (hm : Odd m) :
    ResidueAwareDensityFactor z m = ResidueAwareDensityFactor z (radical m) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hrad0 : radical m ≠ 0 := by
    unfold radical
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.ne_zero
  have hpf : (radical m).primeFactors = m.primeFactors := by
    unfold radical
    apply Nat.primeFactors_prod
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  unfold ResidueAwareDensityFactor
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hqm⟩
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hmem).2.1
    have hqmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hqprime, hqm, hm0⟩
    have : q ∈ (radical m).primeFactors := hpf.symm ▸ hqmem
    exact ⟨hmem, (Nat.mem_primeFactors.mp this).2.1⟩
  · rintro ⟨hmem, hqrad⟩
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hmem).2.1
    have hqmem : q ∈ (radical m).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqprime, hqrad, hrad0⟩
    have : q ∈ m.primeFactors := hpf ▸ hqmem
    exact ⟨hmem, (Nat.mem_primeFactors.mp this).2.1⟩

/-- The requested `m=2` hostile case is parity vanishing. -/
theorem LocalDensityEvenZero {x : ℝ} (z n : ℕ) :
    ResidueAwareComparisonCandidate x z (2 * n) = 0 :=
  ResidueAwareEvenVanishing (dvd_mul_right 2 n)

end TwinPrimeProject
