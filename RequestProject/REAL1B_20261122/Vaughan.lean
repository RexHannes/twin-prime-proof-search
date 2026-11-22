import RequestProject.REAL1B_20261122.QuarterRough

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
