import Gate1B.CanonicalSwitchedAggregate

/-!
# Gate 1B · λ₃ / P₃ convolution typing and the finite switched divisor pairing

**Exact finite algebra only.  No analytic estimate is proved or assumed.**

This module is strictly append-only with respect to the existing bank.  It
reuses the Gate 1B library's own `λ₃` coefficient

`lambda3Sw U V q = ∑_{dℓ = q, U < d, V < ℓ} μ(d) Λ(ℓ)`

from `Gate1B.CanonicalSwitchedAggregate`.  **No second `λ₃` is defined here.**
(The real-valued twin of that formula also occurs in the top-level module
`VaughanPacketAlgebra`, which lies outside every library glob of this
repository and is therefore not importable; it is left untouched.)

## Contents

* §1 complex truncations `afTruncLEC`, `afTruncGTC`, the complex von Mangoldt
  function `vonMangoldtC`, and the two *different* objects

  - `highHighCoefficient U V = μ_{>U} * Λ_{>V}` (the modulus coefficient), and
  - `highHighP3 U V = highHighCoefficient U V * ζ` (the hard Vaughan `P₃`
    arithmetic function);

* §2 the identification `lambda3AF = highHighCoefficient` and the **BOXED**
  typing theorem

  `λ₃ * ζ = highHighP3`,

  together with an explicit firewall: `λ₃ = P₃` is **false**, with a concrete
  countermodel at `U = V = 1`, `n = 8` (values `−log 2` versus `−2 log 2`),
  plus a type-level counterguard (`HighHighModulusCoefficient` and
  `HardVaughanP3` are distinct one-field structures and no value-preserving
  bridge between them exists);

* §3 the exact switched residue-class pairing
  `C_g(q) = ∑_{2 ≤ q·r ≤ K+2} g(q·r − 2)` and the finite reindexing

  `∑_q λ₃(q) C_g(q) = ∑_N (λ₃ * ζ)(N) g(N−2) = ∑_N highHighP3(N) g(N−2)`,

  which is exactly the place where conflating `λ₃` with `P₃` produced the
  previously audited false formula.  The shift is the literal fixed `2`; no
  step averages over the shift.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTemplates

open Finset ArithmeticFunction
open scoped BigOperators

/-! ## 1. Complex truncations and the two high-high objects -/

/-- Cut a complex arithmetic function off at `Y` (`n ≤ Y` kept). -/
noncomputable def afTruncLEC (Y : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := if n ≤ Y then f n else 0
  map_zero' := by simp

/-- The complementary strict truncation (`n > Y` kept). -/
noncomputable def afTruncGTC (Y : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := if Y < n then f n else 0
  map_zero' := by simp

@[simp] theorem afTruncLEC_apply (Y : ℕ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    afTruncLEC Y f n = if n ≤ Y then f n else 0 := rfl

@[simp] theorem afTruncGTC_apply (Y : ℕ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    afTruncGTC Y f n = if Y < n then f n else 0 := rfl

theorem afC_truncation_decomposition (Y : ℕ) (f : ArithmeticFunction ℂ) :
    f = afTruncLEC Y f + afTruncGTC Y f := by
  ext n
  by_cases h : n ≤ Y
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

/-- The von Mangoldt function with complex values. -/
noncomputable def vonMangoldtC : ArithmeticFunction ℂ where
  toFun n := (Λ n : ℂ)
  map_zero' := by simp

@[simp] theorem vonMangoldtC_apply (n : ℕ) : vonMangoldtC n = (Λ n : ℂ) := rfl

/-- The **modulus coefficient** `μ_{>U} * Λ_{>V}`: this is the high-high
Vaughan *coefficient*, not the hard arithmetic function. -/
noncomputable def highHighCoefficient (U V : ℕ) : ArithmeticFunction ℂ :=
  afTruncGTC U (↑moebius : ArithmeticFunction ℂ) * afTruncGTC V vonMangoldtC

/-- The **hard Vaughan `P₃` arithmetic function**
`P₃ = (μ_{>U} * Λ_{>V}) * ζ`.  This is the object that actually appears on the
`N`-side of the switched pairing. -/
noncomputable def highHighP3 (U V : ℕ) : ArithmeticFunction ℂ :=
  highHighCoefficient U V * (↑zeta : ArithmeticFunction ℂ)

theorem highHighCoefficient_apply (U V n : ℕ) :
    highHighCoefficient U V n =
      ∑ p ∈ n.divisorsAntidiagonal,
        (if U < p.1 then (moebius p.1 : ℂ) else 0) *
          (if V < p.2 then ((Λ p.2 : ℝ) : ℂ) else 0) := by
  rw [highHighCoefficient, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : U < p.1 <;> by_cases h2 : V < p.2 <;> simp [h1, h2]

/-! ## 2. `λ₃` typing -/

/-- The Gate 1B `λ₃` coefficient packaged as an arithmetic function.  The
values are literally `CanonicalSwitched.lambda3Sw`; nothing is redefined. -/
noncomputable def lambda3AF (U V : ℕ) : ArithmeticFunction ℂ where
  toFun q := CanonicalSwitched.lambda3Sw U V q
  map_zero' := by simp [CanonicalSwitched.lambda3Sw]

@[simp] theorem lambda3AF_apply (U V q : ℕ) :
    lambda3AF U V q = CanonicalSwitched.lambda3Sw U V q := rfl

/-- `λ₃` **is** the high-high modulus coefficient `μ_{>U} * Λ_{>V}`. -/
theorem lambda3AF_eq_highHighCoefficient (U V : ℕ) :
    lambda3AF U V = highHighCoefficient U V := by
  ext q
  rw [lambda3AF_apply, CanonicalSwitched.lambda3Sw, highHighCoefficient_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : U < p.1 <;> by_cases h2 : V < p.2 <;> simp [h1, h2]

/-- **BOXED.**  The Vaughan convolution typing theorem:

`λ₃(U,V) * ζ = highHighP3(U,V)`.

The statement `λ₃ = P₃` is *not* formalised — it is false (see
`lambda3_ne_highHighP3`). -/
theorem lambda3_conv_zeta_eq_highHighP3 (U V : ℕ) :
    lambda3AF U V * (↑zeta : ArithmeticFunction ℂ) = highHighP3 U V := by
  rw [lambda3AF_eq_highHighCoefficient, highHighP3]

/-! ### The `λ₃ ≠ P₃` firewall -/

/-- Convolving with `ζ` is not the identity on arithmetic functions: a generic
counterguard forbidding the inference `f * ζ = g ⟹ f = g`. -/
theorem exists_af_conv_zeta_ne_self :
    ∃ f : ArithmeticFunction ℂ, f * (↑zeta : ArithmeticFunction ℂ) ≠ f := by
  refine ⟨1, ?_⟩
  intro h
  have h2 := congrArg (fun g => g 2) h
  simp at h2

private theorem vonMangoldt_four : Λ 4 = Real.log 2 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

private theorem vonMangoldt_eight : Λ 8 = Real.log 2 := by
  have h : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- `μ_{>1} * Λ_{>1}` vanishes at `1`. -/
theorem highHighCoefficient_one_one_one : highHighCoefficient 1 1 1 = 0 := by
  rw [highHighCoefficient_apply]; simp

/-- `μ_{>1} * Λ_{>1}` vanishes at `2`. -/
theorem highHighCoefficient_one_one_two : highHighCoefficient 1 1 2 = 0 := by
  have h : Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} := by decide
  rw [highHighCoefficient_apply, h]; simp

/-- A concrete evaluation: the modulus coefficient `μ_{>1} * Λ_{>1}` at `4`
equals `−log 2`. -/
theorem highHighCoefficient_one_one_four :
    highHighCoefficient 1 1 4 = -(Real.log 2 : ℂ) := by
  have h : Nat.divisorsAntidiagonal 4 = {(1, 4), (2, 2), (4, 1)} := by decide
  have hmu2 : moebius 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  rw [highHighCoefficient_apply, h]
  simp [hmu2, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- A concrete evaluation: the modulus coefficient `μ_{>1} * Λ_{>1}` at `8`
equals `−log 2`. -/
theorem highHighCoefficient_one_one_eight :
    highHighCoefficient 1 1 8 = -(Real.log 2 : ℂ) := by
  have h8 : Nat.divisorsAntidiagonal 8 = {(1, 8), (2, 4), (4, 2), (8, 1)} := by decide
  have hmu2 : moebius 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hmu4 : moebius 4 = 0 := by decide
  rw [highHighCoefficient_apply, h8]
  simp [hmu2, hmu4, vonMangoldt_four]

/-- A concrete evaluation: the hard `P₃` at `8` equals `−2 log 2`. -/
theorem highHighP3_one_one_eight :
    highHighP3 1 1 8 = -2 * (Real.log 2 : ℂ) := by
  have h8 : Nat.divisorsAntidiagonal 8 = {(1, 8), (2, 4), (4, 2), (8, 1)} := by decide
  rw [highHighP3, ArithmeticFunction.mul_apply, h8]
  simp [highHighCoefficient_one_one_one, highHighCoefficient_one_one_two,
    highHighCoefficient_one_one_four, highHighCoefficient_one_one_eight]
  ring

/-- **Firewall (value level).**  `λ₃ ≠ P₃`: the high-high modulus coefficient
is *not* the hard Vaughan arithmetic function.  Countermodel `U = V = 1`,
`n = 8`, where the two values are `−log 2` and `−2 log 2`. -/
theorem lambda3_ne_highHighP3 : lambda3AF 1 1 ≠ highHighP3 1 1 := by
  intro h
  have h8 := congrArg (fun f => f 8) h
  simp only [lambda3AF_eq_highHighCoefficient] at h8
  rw [highHighCoefficient_one_one_eight, highHighP3_one_one_eight] at h8
  have hlog : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num)).ne'
  exact hlog (by linear_combination h8)

/-! ### Type-level counterguard -/

/-- Wrapper type for the **modulus** coefficient `λ₃ = μ_{>U} * Λ_{>V}`. -/
structure HighHighModulusCoefficient where
  coeff : ArithmeticFunction ℂ

/-- Wrapper type for the **hard Vaughan `P₃`** arithmetic function. -/
structure HardVaughanP3 where
  hard : ArithmeticFunction ℂ

/-- The intended `λ₃`-side inhabitant. -/
noncomputable def modulusCoefficientOf (U V : ℕ) : HighHighModulusCoefficient :=
  ⟨lambda3AF U V⟩

/-- The intended `P₃`-side inhabitant. -/
noncomputable def hardP3Of (U V : ℕ) : HardVaughanP3 := ⟨highHighP3 U V⟩

/-- **Type-level counterguard.**  There is no map from the modulus side to the
hard side which is simultaneously value-preserving and sends the `λ₃` wrapper
to the `P₃` wrapper: the two names are not interchangeable. -/
theorem no_bridge_modulus_to_hard :
    ¬ ∃ F : HighHighModulusCoefficient → HardVaughanP3,
        (∀ c : HighHighModulusCoefficient, (F c).hard = c.coeff) ∧
          ∀ U V : ℕ, F (modulusCoefficientOf U V) = hardP3Of U V := by
  rintro ⟨F, hval, hmap⟩
  have h1 : (F (modulusCoefficientOf 1 1)).hard = lambda3AF 1 1 := hval _
  rw [hmap 1 1] at h1
  exact lambda3_ne_highHighP3 h1.symm

/-! ## 3. The exact finite switched divisor pairing -/

/-- The multiplier set `{r : 2 ≤ q·r ≤ K+2}` as an explicit `Finset`. -/
def switchedMultiplierSet (K q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (K + 2)).filter (fun r => 2 ≤ q * r ∧ q * r ≤ K + 2)

theorem mem_switchedMultiplierSet {K q r : ℕ} (hq : 0 < q) :
    r ∈ switchedMultiplierSet K q ↔ 1 ≤ r ∧ 2 ≤ q * r ∧ q * r ≤ K + 2 := by
  simp only [switchedMultiplierSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have : r ≤ q * r := Nat.le_mul_of_pos_left r hq
    exact ⟨⟨h1, by omega⟩, h2, h3⟩

/-- `C_g(q) = ∑_{2 ≤ q·r ≤ K+2} g(q·r − 2)`: the exact switched residue-class
pairing with the **fixed** shift `2` (never an average over shifts). -/
noncomputable def switchedClassPairing (K : ℕ) (g : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ r ∈ switchedMultiplierSet K q, g (q * r - 2)

/-- The pair index set of the switched pairing. -/
def switchedPairSet (K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (K + 2)) ×ˢ (Finset.Icc 1 (K + 2))).filter
    (fun p => 2 ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ K + 2)

theorem switched_sum_eq_pairSum (K : ℕ) (f : ArithmeticFunction ℂ) (g : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 (K + 2), f q * switchedClassPairing K g q =
      ∑ p ∈ switchedPairSet K, f p.1 * g (p.1 * p.2 - 2) := by
  classical
  rw [switchedPairSet, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [switchedClassPairing, Finset.mul_sum, switchedMultiplierSet, Finset.sum_filter]

/-- **The switched finite reindexing.**  For every finite cutoff `K`, every
arithmetic function `f` and every coefficient `g`,

`∑_q f(q) C_g(q) = ∑_N (f * ζ)(N) g(N − 2)`,

an exact identity obtained by reindexing the pair `(q, r)` by `N = q·r`. -/
theorem switched_pairing_reindex (K : ℕ) (f : ArithmeticFunction ℂ) (g : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 (K + 2), f q * switchedClassPairing K g q =
      ∑ N ∈ Finset.Icc 2 (K + 2),
        (f * (↑zeta : ArithmeticFunction ℂ)) N * g (N - 2) := by
  classical
  rw [switched_sum_eq_pairSum]
  have hRHS : ∀ N ∈ Finset.Icc 2 (K + 2),
      (f * (↑zeta : ArithmeticFunction ℂ)) N * g (N - 2) =
        ∑ p ∈ Nat.divisorsAntidiagonal N, f p.1 * g (N - 2) := by
    intro N _
    rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hprod, hN0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hp2 : p.2 ≠ 0 := by
      intro h
      apply hN0
      rw [← hprod, h, Nat.mul_zero]
    simp [hp2]
  rw [Finset.sum_congr rfl hRHS, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => (⟨p.1 * p.2, p⟩ : (_ : ℕ) × (ℕ × ℕ)))
    (fun s => s.2) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, r⟩ hp
    simp only [switchedPairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hq1, hqK⟩, hr1, hrK⟩, h2, hK⟩ := hp
    have hne : q * r ≠ 0 := by omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨h2, hK⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hne⟩⟩
  · rintro ⟨N, q, r⟩ hs
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hs
    obtain ⟨⟨hN2, hNK⟩, hprod, hN0⟩ := hs
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · exfalso; rw [h, Nat.zero_mul] at hprod; omega
      · exact h
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · exfalso; rw [h, Nat.mul_zero] at hprod; omega
      · exact h
    have hqN : q ≤ N := by
      have : q * 1 ≤ q * r := Nat.mul_le_mul_left q hr1
      omega
    have hrN : r ≤ N := by
      have : 1 * r ≤ q * r := Nat.mul_le_mul_right r hq1
      omega
    simp only [switchedPairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hq1, by omega⟩, hr1, by omega⟩, by omega, by omega⟩
  · rintro ⟨q, r⟩ _; rfl
  · rintro ⟨N, q, r⟩ hs
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hs
    obtain ⟨-, hprod, -⟩ := hs
    subst hprod
    rfl
  · rintro ⟨q, r⟩ _; rfl

/-- **The switched pairing with the actual `λ₃` coefficient.**  The `N`-side
carries the *hard* Vaughan object `highHighP3`, never `λ₃` itself.  This is the
exact statement whose `λ₃`-for-`P₃` substitution was the previously audited
false formula. -/
theorem switched_pairing_eq_highHighP3 (K U V : ℕ) (g : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 (K + 2),
        lambda3AF U V q * switchedClassPairing K g q =
      ∑ N ∈ Finset.Icc 2 (K + 2), highHighP3 U V N * g (N - 2) := by
  rw [switched_pairing_reindex, lambda3_conv_zeta_eq_highHighP3]

end HStarTemplates
end CurrentProgramme
end TwinPrimeProject
