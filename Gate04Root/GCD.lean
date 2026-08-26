/-
# Gate04Root.GCD

Unit / coprimality lemmas for the affine numerators.

From `r α ≡ 2 (mod m)` with `m` odd we get `gcd(α, m) = 1`, and likewise
`gcd(β, m') = 1` from `r β ≡ 2 (mod m')` with `m'` odd.

The only inputs are: the congruence and the oddness of the modulus.  In
particular we do **not** use any assumption relating `|k|` to the prime factors
of the modulus.
-/
import Gate04Root.Affine

namespace Gate04Root

/-- Core divisibility lemma: a common divisor of `x` and an odd `n` with
`n ∣ r x - 2` must be a unit. -/
theorem gcd_eq_one_of_odd_of_dvd {r x n : ℤ} (hodd : Odd n) (h : n ∣ r * x - 2) :
    Int.gcd x n = 1 := by
  set d : ℕ := Int.gcd x n with hd
  have hdx : (d : ℤ) ∣ x := Int.gcd_dvd_left x n
  have hdn : (d : ℤ) ∣ n := Int.gcd_dvd_right x n
  have hd2 : (d : ℤ) ∣ 2 := by
    have h1 : (d : ℤ) ∣ r * x := hdx.mul_left r
    have h2 : (d : ℤ) ∣ r * x - 2 := hdn.trans h
    have := h1.sub h2
    simpa using this
  have hd2' : d ∣ 2 := by
    have : ((d : ℤ)) ∣ ((2 : ℕ) : ℤ) := by simpa using hd2
    exact_mod_cast this
  have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd2'
  interval_cases d
  · simp at hd2'
  · rfl
  · exfalso
    have : (2 : ℤ) ∣ n := by exact_mod_cast hdn
    rcases hodd with ⟨t, ht⟩
    omega

/-- `α` is coprime to `m`, given `m` odd and the affine congruence
`r α ≡ 2 (mod m)`. -/
theorem alpha_coprime_m_of_odd {r alpha m : ℤ} (hodd : Odd m)
    (h : m ∣ r * alpha - 2) : Int.gcd alpha m = 1 :=
  gcd_eq_one_of_odd_of_dvd hodd h

/-- `β` is coprime to `m'`, given `m'` odd and the shifted affine congruence
`r β ≡ 2 (mod m')`. -/
theorem beta_coprime_mPrime_of_odd {r beta mPrime : ℤ} (hodd : Odd mPrime)
    (h : mPrime ∣ r * beta - 2) : Int.gcd beta mPrime = 1 :=
  gcd_eq_one_of_odd_of_dvd hodd h

/-- Bézout form of the previous lemma. -/
theorem isCoprime_alpha_m_of_odd {r alpha m : ℤ} (hodd : Odd m)
    (h : m ∣ r * alpha - 2) : IsCoprime alpha m :=
  Int.isCoprime_iff_gcd_eq_one.mpr (alpha_coprime_m_of_odd hodd h)

theorem isCoprime_beta_mPrime_of_odd {r beta mPrime : ℤ} (hodd : Odd mPrime)
    (h : mPrime ∣ r * beta - 2) : IsCoprime beta mPrime :=
  Int.isCoprime_iff_gcd_eq_one.mpr (beta_coprime_mPrime_of_odd hodd h)

namespace AffineEdgeData

variable (e : AffineEdgeData)

/-- Specialisation to an affine edge: if `m` is odd then `gcd(α, m) = 1`. -/
theorem gcd_alpha_m_eq_one (hodd : Odd e.m) : Int.gcd e.alpha e.m = 1 :=
  alpha_coprime_m_of_odd hodd e.m_dvd_r_alpha_sub_two

/-- Specialisation to an affine edge: if `m'` is odd then `gcd(β, m') = 1`. -/
theorem gcd_beta_mPrime_eq_one (hodd : Odd e.mPrime) : Int.gcd e.beta e.mPrime = 1 :=
  beta_coprime_mPrime_of_odd hodd e.mPrime_dvd_r_beta_sub_two

end AffineEdgeData

end Gate04Root
