import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RequestProject.Status

/-!
# Finite-depth Möbius algebra

This file banks the source-independent algebra behind the proposed finite-depth
repair.  Multiplication of `ArithmeticFunction ℤ` is finite Dirichlet
convolution.  No analytic convergence is involved.
-/

namespace HighP3

open ArithmeticFunction

abbrev AF := ArithmeticFunction ℤ

/-- The constant-one arithmetic function, coerced to integer values. -/
def arithOne : AF := ArithmeticFunction.zeta

/-- The Dirichlet-convolution identity. -/
def epsilonStar : AF := 1

/-- Möbius truncated to `n ≤ z`. -/
def mobiusCutoff (z : ℕ) : AF :=
  ⟨fun n => if n ≤ z then ArithmeticFunction.moebius n else 0,
   by simp⟩

/-- The finite-depth remainder `ε - μ_{≤z} * 1`. -/
def mobiusRemainder (z : ℕ) : AF :=
  epsilonStar - mobiusCutoff z * arithOne

/-- Explicit convolution model: multiplication is a finite divisor-pair sum. -/
theorem DIRICHLET_CONV_FINITE (f g : AF) (n : ℕ) :
    (f * g) n = ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2 := by
  exact ArithmeticFunction.mul_apply

/-- The factor rearrangement required in the finite-depth identity. -/
theorem MOBIUS_POWER_FACTOR_REARRANGEMENT (a : AF) (j : ℕ) (hj : 0 < j) :
    (a * arithOne) ^ j * ArithmeticFunction.moebius =
      a ^ j * arithOne ^ (j - 1) := by
  simp only [arithOne]
  ring_nf
  have key : zeta * moebius = 1 := by
    ext n
    simp
  have hj' : j = j - 1 + 1 := by omega
  rw [hj']
  simp [pow_succ, mul_assoc, key]

/-- Abstract commutative-ring binomial identity underlying the repair. -/
theorem FINITE_DEPTH_BINOMIAL_IDENTITY
    {A : Type*} [CommRing A] (a m : A) (K : ℕ) :
    (1 - a) ^ K * m +
        ∑ j ∈ Finset.Icc 1 K, (-1 : A) ^ (j - 1) * (K.choose j : ℕ) • a ^ j * m = m := by
  -- Factor out m from the left side
  have key : (1 - a) ^ K + ∑ j ∈ Finset.Icc 1 K, (-1 : A) ^ (j - 1) * (K.choose j : ℕ) • a ^ j = 1 := by
    rw [sub_eq_add_neg, add_comm (1 : A), add_pow]
    simp [mul_one]
    rw [Finset.sum_range_succ', add_comm]
    simp
    -- Now goal is: ∑ x ∈ Icc 1 K, (-1)^(x-1) * (K.choose x * a^x) + (∑ k ∈ range K, (-a)^(k+1) * K.choose(k+1) + 1) = 1
    -- Need to show the two sums are negatives
    have align : (∑ k ∈ Finset.range K, (-a) ^ (k + 1) * (K.choose (k + 1) : A)) =
                 ∑ x ∈ Finset.Icc 1 K, (-a) ^ x * (K.choose x : A) := by
      have h : (Finset.Icc 1 K : Finset ℕ) = Finset.Ico 1 (K + 1) := by
        ext; simp [Finset.mem_Icc, Finset.mem_Ico]
      rw [h, Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    rw [align]
    -- Now need to show: ∑ x ∈ Icc 1 K, (-1)^(x-1) * (K.choose x * a^x) + (∑ x ∈ Icc 1 K, (-a)^x * K.choose x + 1) = 1
    -- i.e., the two sums are negatives
    have cancel : ∑ x ∈ Finset.Icc 1 K, (-1 : A) ^ (x - 1) * (K.choose x : A) * a ^ x +
                  ∑ x ∈ Finset.Icc 1 K, (-a) ^ x * (K.choose x : A) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro x hx
      simp [Finset.mem_Icc] at hx
      have hx' : x = (x - 1) + 1 := by omega
      rw [hx']
      simp [pow_succ]
      ring
    have cancel' : ∑ x ∈ Finset.Icc 1 K, (-1 : A) ^ (x - 1) * ((K.choose x : A) * a ^ x) +
                    ∑ x ∈ Finset.Icc 1 K, (-a) ^ x * (K.choose x : A) = 0 := by
      simp_rw [mul_assoc] at cancel ⊢
      exact cancel
    rw [show (∑ x ∈ Finset.Icc 1 K, (-1 : A) ^ (x - 1) * (↑(K.choose x) * a ^ x)) +
            ((∑ x ∈ Finset.Icc 1 K, (-a) ^ x * ↑(K.choose x)) + 1) =
            (∑ x ∈ Finset.Icc 1 K, (-1 : A) ^ (x - 1) * (↑(K.choose x) * a ^ x) +
             ∑ x ∈ Finset.Icc 1 K, (-a) ^ x * ↑(K.choose x)) + 1 by ring,
        cancel', zero_add]
  calc (1 - a) ^ K * m + ∑ j ∈ Finset.Icc 1 K, (-1 : A) ^ (j - 1) * (K.choose j : ℕ) • a ^ j * m
      = ((1 - a) ^ K + ∑ j ∈ Finset.Icc 1 K, (-1 : A) ^ (j - 1) * (K.choose j : ℕ) • a ^ j) * m := by
        simp [add_mul, Finset.sum_mul]
    _ = 1 * m := by rw [key]
    _ = m := one_mul m

/-- `FINITE_DEPTH_MOBIUS_IDENTITY` (`LEAN_PROVED`).

For every finite cutoff and depth, the displayed identity holds in the
commutative Dirichlet-convolution ring. -/
theorem FINITE_DEPTH_MOBIUS_IDENTITY (z K : ℕ) :
    ArithmeticFunction.moebius =
      mobiusRemainder z ^ K * ArithmeticFunction.moebius +
        ∑ j ∈ Finset.Icc 1 K,
          (-1 : AF) ^ (j - 1) * (K.choose j : ℕ) •
            (mobiusCutoff z ^ j * arithOne ^ (j - 1)) := by
  let a : AF := mobiusCutoff z * arithOne
  have hrem : mobiusRemainder z = 1 - a := by rfl
  symm
  calc
    mobiusRemainder z ^ K * ArithmeticFunction.moebius +
          ∑ j ∈ Finset.Icc 1 K, (-1 : AF) ^ (j - 1) * (K.choose j : ℕ) •
            (mobiusCutoff z ^ j * arithOne ^ (j - 1)) =
        (1 - a) ^ K * ArithmeticFunction.moebius +
          ∑ j ∈ Finset.Icc 1 K,
            ((-1 : AF) ^ (j - 1) * (K.choose j : ℕ) • a ^ j) *
              ArithmeticFunction.moebius := by
      rw [hrem]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
      dsimp [a]
      have hf := MOBIUS_POWER_FACTOR_REARRANGEMENT (mobiusCutoff z) j hjpos
      simp only [nsmul_eq_mul]
      calc
        (-1) ^ (j - 1) * (↑(K.choose j) *
            (mobiusCutoff z ^ j * arithOne ^ (j - 1))) =
          ((-1) ^ (j - 1) * ↑(K.choose j)) *
            ((mobiusCutoff z * arithOne) ^ j * ArithmeticFunction.moebius) := by rw [hf]; ring
        _ = (-1) ^ (j - 1) * (↑(K.choose j) *
            (mobiusCutoff z * arithOne) ^ j) * ArithmeticFunction.moebius := by ring
    _ = ArithmeticFunction.moebius :=
      FINITE_DEPTH_BINOMIAL_IDENTITY a ArithmeticFunction.moebius K

end HighP3
