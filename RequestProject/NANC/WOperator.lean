import Mathlib

namespace TwinPrimeProject.NANC.WOperator

/-! # Corrected W-operator algebra

This file banks only finite CRT, injectivity, and rational-exponent algebra.
It contains no graph-energy or analytic cancellation theorem.
-/

/-- Fixed coprime CRT moduli for the `W`-operator. -/
structure Moduli where
  p : ℕ
  mPrime : ℕ
  p_ne_zero : p ≠ 0
  mPrime_ne_zero : mPrime ≠ 0
  coprime : p.Coprime mPrime
  p_prime : p.Prime
  mPrime_prime : mPrime.Prime

attribute [instance] Moduli.p_ne_zero Moduli.mPrime_ne_zero

/-- The corrected `W` numerator, characterized by
`W = 2k/m (mod p)` and `W = -2/r (mod m')`. -/
noncomputable def wOperator (d : Moduli) (r k m : ℤ) : ZMod (d.p * d.mPrime) :=
  (ZMod.chineseRemainder d.coprime).symm
    (2 * (k : ZMod d.p) * (m : ZMod d.p)⁻¹,
      -2 * (r : ZMod d.mPrime)⁻¹)

/-- The corrected `W'` numerator for the `h'` block. -/
noncomputable def wPrimeOperator (d : Moduli) (r k m : ℤ) : ZMod (d.p * d.mPrime) :=
  (ZMod.chineseRemainder d.coprime).symm
    (-2 * (k : ZMod d.p) * (m : ZMod d.p)⁻¹,
      2 * (r : ZMod d.mPrime)⁻¹)

/-- The global CRT numerator `Gamma = W / q`, specified componentwise.
This avoids imposing a prime-modulus field structure on the composite ring. -/
noncomputable def gamma (d : Moduli) (r k m q : ℤ) : ZMod (d.p * d.mPrime) :=
  (ZMod.chineseRemainder d.coprime).symm
    (2 * (k : ZMod d.p) * (m : ZMod d.p)⁻¹ * (q : ZMod d.p)⁻¹,
      -2 * (r : ZMod d.mPrime)⁻¹ * (q : ZMod d.mPrime)⁻¹)

/-- The componentwise global numerator `Gamma' = W' / q'`. -/
noncomputable def gammaPrime (d : Moduli) (r k m qPrime : ℤ) : ZMod (d.p * d.mPrime) :=
  (ZMod.chineseRemainder d.coprime).symm
    (-2 * (k : ZMod d.p) * (m : ZMod d.p)⁻¹ * (qPrime : ZMod d.p)⁻¹,
      2 * (r : ZMod d.mPrime)⁻¹ * (qPrime : ZMod d.mPrime)⁻¹)

/-- The local `p` coefficient after CRT projection has no extra `p'` factor. -/
theorem h_local_coeff_mod_p (d : Moduli) (r k m : ℤ) :
    (ZMod.chineseRemainder d.coprime (wOperator d r k m)).1 =
      2 * (k : ZMod d.p) * (m : ZMod d.p)⁻¹ := by
  simp [wOperator]

/-- The local `m'` coefficient of `W` is `-2/r`. -/
theorem h_local_coeff_mod_mprime (d : Moduli) (r k m : ℤ) :
    (ZMod.chineseRemainder d.coprime (wOperator d r k m)).2 =
      -2 * (r : ZMod d.mPrime)⁻¹ := by
  simp [wOperator]

/-- Corrected global CRT numerator: modulo `p` it is `2k/(qm)`, and
modulo `m'` it is `-2/(qr)`. -/
theorem h_global_crt_numerator (d : Moduli) (r k m q : ℤ) :
    ZMod.chineseRemainder d.coprime (gamma d r k m q) =
      (2 * (k : ZMod d.p) * (m : ZMod d.p)⁻¹ * (q : ZMod d.p)⁻¹,
       -2 * (r : ZMod d.mPrime)⁻¹ * (q : ZMod d.mPrime)⁻¹) := by
  simp [gamma]

/-- CRT-component form of the corrected `h`-block character identity.  The
first component includes the CRT projection factor `m'⁻¹`, and the second
includes `p⁻¹`; applying the standard additive characters gives exactly
`e_p(2hk/(qmm')) e_{m'}(-2h/(pqr)) = e_{pm'}(hW/q)`. -/
theorem w_operator_h_block (d : Moduli) (r k m q h : ℤ) :
    let G := ZMod.chineseRemainder d.coprime (h * gamma d r k m q)
    (G.1 * (d.mPrime : ZMod d.p)⁻¹,
     G.2 * (d.p : ZMod d.mPrime)⁻¹) =
    (2 * (h : ZMod d.p) * k * (q : ZMod d.p)⁻¹ *
        (m : ZMod d.p)⁻¹ * (d.mPrime : ZMod d.p)⁻¹,
     -2 * (h : ZMod d.mPrime) * (d.p : ZMod d.mPrime)⁻¹ *
        (q : ZMod d.mPrime)⁻¹ * (r : ZMod d.mPrime)⁻¹) := by
  dsimp
  simp [gamma]
  constructor <;> ring

/-- The corrected local `p'` coefficient for the `h'` block. -/
theorem hprime_local_coeff_mod_pprime (d : Moduli) (r k m : ℤ) :
    (ZMod.chineseRemainder d.coprime (wPrimeOperator d r k m)).1 =
      -2 * (k : ZMod d.p) * (m : ZMod d.p)⁻¹ := by
  simp [wPrimeOperator]

/-- The corrected local `m'` coefficient for the `h'` block. -/
theorem hprime_local_coeff_mod_mprime (d : Moduli) (r k m : ℤ) :
    (ZMod.chineseRemainder d.coprime (wPrimeOperator d r k m)).2 =
      2 * (r : ZMod d.mPrime)⁻¹ := by
  simp [wPrimeOperator]

/-- CRT-component form of the corrected `h'`-block character identity. -/
theorem w_operator_hprime_block (d : Moduli) (r k m qPrime hPrime : ℤ) :
    let G := ZMod.chineseRemainder d.coprime
      (hPrime * gammaPrime d r k m qPrime)
    (G.1 * (d.mPrime : ZMod d.p)⁻¹,
     G.2 * (d.p : ZMod d.mPrime)⁻¹) =
    (-2 * (hPrime : ZMod d.p) * k * (qPrime : ZMod d.p)⁻¹ *
        (m : ZMod d.p)⁻¹ * (d.mPrime : ZMod d.p)⁻¹,
     2 * (hPrime : ZMod d.mPrime) * (d.p : ZMod d.mPrime)⁻¹ *
        (qPrime : ZMod d.mPrime)⁻¹ * (r : ZMod d.mPrime)⁻¹) := by
  dsimp
  simp [gammaPrime]
  constructor <;> ring

/-- Two natural representatives strictly between zero and the modulus are equal
when their residue classes agree. -/
lemma nat_representatives_eq_of_zmod_eq (n r₁ r₂ : ℕ)
    (hr₁lt : r₁ < n) (hr₂lt : r₂ < n)
    (heq : (r₁ : ZMod n) = r₂) : r₁ = r₂ := by
  have hval := congrArg ZMod.val heq
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hr₁lt,
    Nat.mod_eq_of_lt hr₂lt] using hval

/-- Centered signed representatives of a residue class are unique. -/
lemma centered_int_representatives_eq_of_zmod_eq (p : ℕ) (k₁ k₂ : ℤ)
    (hk₁ : |k₁| < (p : ℤ) / 2) (hk₂ : |k₂| < (p : ℤ) / 2)
    (heq : (k₁ : ZMod p) = k₂) : k₁ = k₂ := by
  have hdiv : (p : ℤ) ∣ (k₁ - k₂) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [heq]
  have habs : |k₁ - k₂| < p := by
    calc |k₁ - k₂| ≤ |k₁| + |k₂| := abs_sub k₁ k₂
         _ < (p : ℤ) / 2 + (p : ℤ) / 2 := add_lt_add hk₁ hk₂
         _ ≤ p := by omega
  have hzero : k₁ - k₂ = 0 := by
    obtain ⟨c, hc⟩ := hdiv
    rw [hc] at habs
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p)] at habs
    by_cases hc_zero : c = 0
    · rw [hc, hc_zero, mul_zero]
    · have : p ≤ p * |c| := by
        have : 1 ≤ |c| := abs_pos.mpr hc_zero
        nlinarith
      linarith
  linarith

/-- Injectivity of the corrected `W` map in the clean centered signed ranges. -/
theorem w_map_injective_fixed_p_mprime
    (d : Moduli) (r₁ r₂ : ℕ) (k₁ k₂ : ℤ)
    (hr₁lt : r₁ < d.mPrime) (hr₂lt : r₂ < d.mPrime)
    (hk₁ : |k₁| < (d.p : ℤ) / 2)
    (hk₂ : |k₂| < (d.p : ℤ) / 2)
    (htwoMNe : (2 : ZMod d.mPrime) ≠ 0)
    (htwoPNe : (2 : ZMod d.p) ≠ 0)
    (hm₁ne : (((d.mPrime : ℤ) - k₁ * r₁ : ℤ) : ZMod d.p) ≠ 0)
    (hm₂ne : (((d.mPrime : ℤ) - k₂ * r₂ : ℤ) : ZMod d.p) ≠ 0)
    (hmPrimeNe : (d.mPrime : ZMod d.p) ≠ 0)
    (hW : wOperator d r₁ k₁ ((d.mPrime : ℤ) - k₁ * r₁) =
      wOperator d r₂ k₂ ((d.mPrime : ℤ) - k₂ * r₂)) :
    r₁ = r₂ ∧ k₁ = k₂ := by
  letI : Fact d.p.Prime := ⟨d.p_prime⟩
  letI : Fact d.mPrime.Prime := ⟨d.mPrime_prime⟩
  have hcomponents := congrArg (ZMod.chineseRemainder d.coprime) hW
  simp only [wOperator, RingEquiv.apply_symm_apply] at hcomponents
  have hrComponent := congrArg Prod.snd hcomponents
  have hrInv : (r₁ : ZMod d.mPrime)⁻¹ = (r₂ : ZMod d.mPrime)⁻¹ := by
    apply mul_left_cancel₀ (neg_ne_zero.mpr htwoMNe)
    simpa using hrComponent
  have hrCast : (r₁ : ZMod d.mPrime) = r₂ := inv_injective hrInv
  have hr : r₁ = r₂ :=
    nat_representatives_eq_of_zmod_eq d.mPrime r₁ r₂ hr₁lt hr₂lt hrCast
  subst r₂
  have hpComp := congrArg Prod.fst hcomponents
  push_cast at hpComp
  have hfrac :
      (k₁ : ZMod d.p) * ((d.mPrime : ZMod d.p) - k₁ * r₁)⁻¹ =
        (k₂ : ZMod d.p) * ((d.mPrime : ZMod d.p) - k₂ * r₁)⁻¹ := by
    apply mul_left_cancel₀ htwoPNe
    convert hpComp using 1 <;> ring
  have hcross :
      (k₁ : ZMod d.p) * ((d.mPrime : ZMod d.p) - k₂ * r₁) =
        (k₂ : ZMod d.p) * ((d.mPrime : ZMod d.p) - k₁ * r₁) := by
    have hx := (div_eq_div_iff hm₁ne hm₂ne).mp
      (by simpa [div_eq_mul_inv] using hfrac)
    push_cast at hx
    exact hx
  have halgebra :
      (k₁ : ZMod d.p) * (d.mPrime : ZMod d.p) =
        (k₂ : ZMod d.p) * (d.mPrime : ZMod d.p) := by
    linear_combination hcross
  have hkCast : (k₁ : ZMod d.p) = k₂ := by
    exact mul_right_cancel₀ hmPrimeNe halgebra
  exact ⟨rfl, centered_int_representatives_eq_of_zmod_eq d.p k₁ k₂ hk₁ hk₂ hkCast⟩

/-- Rational critical-length product: `RK=M` and row/column sizes `M,L`
give product equal to the composite scale `LM`. -/
theorem critical_length_product_banked (R K M L : ℚ) (hRK : R * K = M) :
    (R * K) * L = L * M := by
  rw [hRK]
  ring

/-- The missing exponent `1-a-2b` is at most the composite twelfth exponent
under the high-`b` corner constraints. -/
theorem missing_saving_le_composite_twelfth (a b : ℚ)
    (ha : 5 / 18 ≤ a) (hb : 1 / 3 ≤ b) :
    1 - a - 2 * b ≤ (b + 1 / 3) / 12 := by
  linarith

/-- At the worst corner the two exponents agree exactly. -/
theorem worst_corner_exact_match :
    1 - (5 / 18 : ℚ) - 2 * (1 / 3) = ((1 / 3 : ℚ) + 1 / 3) / 12 := by
  norm_num

end TwinPrimeProject.NANC.WOperator
