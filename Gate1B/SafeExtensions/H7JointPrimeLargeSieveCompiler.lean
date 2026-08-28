/-
# Gate 1B v8.5 — joint prime large-sieve compiler

**Status: PROVED_FINITE (deterministic compiler; all analytic inputs explicit).**

Given

* a weight family `w` with `|w p| ≤ wBound` (the `logWeight p / (p - 1)` weight,
  never hidden — see `one_div_pred_le_two_div` in `H7JointPrimePacket.lean`),
* a defect-side energy bound `∑_{p,c} ‖a p c‖² ≤ (P² + Y) * E_D`,
* a long-side energy bound `∑_{p,c} ‖b p c‖² ≤ (P² + Y⁸) * E_B`,

finite Cauchy–Schwarz gives the deterministic bound

    ‖∑_p w p ∑_c a p c b p c‖
      ≤ wBound * sqrt((P² + Y) E_D) * sqrt((P² + Y⁸) E_B).

The two energy bounds are exactly where the supplied `LargeSieveBound` data (an
`EXTERNAL_ANALYTIC_INTERFACE`) enters; nothing analytic is created here.
-/
import Mathlib
import Gate1B.SafeExtensions.MultiplicativeLargeSieveInterface

namespace Gate1B.SafeExtensions

open Finset

variable {Pi : Type*} [Fintype Pi]
variable {Ch : Type*} [Fintype Ch]

/-- The full `(p, chi)` energy of a two-index coefficient family. -/
noncomputable def jointEnergy (a : Pi → Ch → ℂ) : ℝ := ∑ p : Pi, ∑ c : Ch, ‖a p c‖ ^ 2

theorem jointEnergy_nonneg (a : Pi → Ch → ℂ) : 0 ≤ jointEnergy a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Finite Cauchy–Schwarz on the `(p, chi)` index set. -/
theorem sum_norm_mul_le_sqrt (a b : Pi → Ch → ℂ) :
    ∑ p : Pi, ∑ c : Ch, ‖a p c‖ * ‖b p c‖
      ≤ Real.sqrt (jointEnergy a) * Real.sqrt (jointEnergy b) := by
  classical
  have hsum : ∑ p : Pi, ∑ c : Ch, ‖a p c‖ * ‖b p c‖
      = ∑ x ∈ (univ : Finset (Pi × Ch)), ‖a x.1 x.2‖ * ‖b x.1 x.2‖ := by
    rw [Fintype.sum_prod_type]
  have hA : ∑ x ∈ (univ : Finset (Pi × Ch)), ‖a x.1 x.2‖ ^ 2 = jointEnergy a := by
    rw [Fintype.sum_prod_type]; rfl
  have hB : ∑ x ∈ (univ : Finset (Pi × Ch)), ‖b x.1 x.2‖ ^ 2 = jointEnergy b := by
    rw [Fintype.sum_prod_type]; rfl
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Pi × Ch))
    (fun x => ‖a x.1 x.2‖) (fun x => ‖b x.1 x.2‖)
  rw [hA, hB] at hCS
  have hnn : 0 ≤ ∑ x ∈ (univ : Finset (Pi × Ch)), ‖a x.1 x.2‖ * ‖b x.1 x.2‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [hsum]
  calc ∑ x ∈ (univ : Finset (Pi × Ch)), ‖a x.1 x.2‖ * ‖b x.1 x.2‖
      = Real.sqrt ((∑ x ∈ (univ : Finset (Pi × Ch)), ‖a x.1 x.2‖ * ‖b x.1 x.2‖) ^ 2) := by
        rw [Real.sqrt_sq hnn]
    _ ≤ Real.sqrt (jointEnergy a * jointEnergy b) := Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (jointEnergy a) * Real.sqrt (jointEnergy b) :=
        Real.sqrt_mul (jointEnergy_nonneg a) _

/-- **The joint prime large-sieve compiler.**

`wBound` is the supplied uniform bound for the per-prime weight; the two energy
hypotheses are the supplied large-sieve outputs.  The conclusion is a purely
deterministic consequence. -/
theorem h7JointPrime_largeSieve_bound
    (w : Pi → ℝ) (a b : Pi → Ch → ℂ) (wBound P Y E_D E_B : ℝ)
    (hw : ∀ p, |w p| ≤ wBound) (hwB : 0 ≤ wBound)
    (hD : jointEnergy a ≤ (P ^ 2 + Y) * E_D)
    (hB : jointEnergy b ≤ (P ^ 2 + Y ^ 8) * E_B) :
    ‖∑ p : Pi, (w p : ℂ) * ∑ c : Ch, a p c * b p c‖
      ≤ wBound * (Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B)) := by
  classical
  have step1 : ‖∑ p : Pi, (w p : ℂ) * ∑ c : Ch, a p c * b p c‖
      ≤ ∑ p : Pi, ∑ c : Ch, wBound * (‖a p c‖ * ‖b p c‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |w p| * ‖∑ c : Ch, a p c * b p c‖
        ≤ wBound * ‖∑ c : Ch, a p c * b p c‖ :=
          mul_le_mul_of_nonneg_right (hw p) (norm_nonneg _)
      _ ≤ wBound * ∑ c : Ch, ‖a p c‖ * ‖b p c‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hwB
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
          rw [norm_mul]
      _ = ∑ c : Ch, wBound * (‖a p c‖ * ‖b p c‖) := by rw [Finset.mul_sum]
  have step2 : ∑ p : Pi, ∑ c : Ch, wBound * (‖a p c‖ * ‖b p c‖)
      = wBound * ∑ p : Pi, ∑ c : Ch, ‖a p c‖ * ‖b p c‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
  have step3 : ∑ p : Pi, ∑ c : Ch, ‖a p c‖ * ‖b p c‖
      ≤ Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B) := by
    refine (sum_norm_mul_le_sqrt a b).trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hD) (Real.sqrt_le_sqrt hB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc ‖∑ p : Pi, (w p : ℂ) * ∑ c : Ch, a p c * b p c‖
      ≤ ∑ p : Pi, ∑ c : Ch, wBound * (‖a p c‖ * ‖b p c‖) := step1
    _ = wBound * ∑ p : Pi, ∑ c : Ch, ‖a p c‖ * ‖b p c‖ := step2
    _ ≤ wBound * (Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B)) :=
        mul_le_mul_of_nonneg_left step3 hwB

/-- The `1/P`-normalised form of the compiler: with `wBound = logWeight / P` the
conclusion is exactly

    |T(P)| ≤ (logWeight / P) sqrt((P²+Y) E_D) sqrt((P²+Y⁸) E_B). -/
theorem h7JointPrime_largeSieve_bound_normalized
    (w : Pi → ℝ) (a b : Pi → Ch → ℂ) (logWeight P Y E_D E_B : ℝ)
    (hP : 0 < P) (hlog : 0 ≤ logWeight)
    (hw : ∀ p, |w p| ≤ logWeight / P)
    (hD : jointEnergy a ≤ (P ^ 2 + Y) * E_D)
    (hB : jointEnergy b ≤ (P ^ 2 + Y ^ 8) * E_B) :
    ‖∑ p : Pi, (w p : ℂ) * ∑ c : Ch, a p c * b p c‖
      ≤ (logWeight / P)
          * (Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B)) :=
  h7JointPrime_largeSieve_bound w a b (logWeight / P) P Y E_D E_B hw
    (div_nonneg hlog hP.le) hD hB

end Gate1B.SafeExtensions
