/-
# Gate 1B v8.5 — H7 short-short conditional closure compiler

**Status: CONDITIONAL_FINITE.
Label: `H7_PHARD_SHORTSHORT_CONDITIONAL_COMPILER`.**

The principal public theorem of v8.5.  *Every* analytic and source input appears
explicitly in the argument list:

* `hScope`  — the H7 short-short scope lock (`alpha, beta < 4/9`);
* `lsD`, `lsB` — supplied `LargeSieveBound` data (EXTERNAL_ANALYTIC_INTERFACE,
  uninhabited in this bank);
* `hsrcD`, `hsrcB` — the supplied source energies `E_D ≤ Y·L1`, `E_B ≤ Y⁸·L2`;
* `hw` — the explicit per-prime weight bound `|w p| ≤ logWeight / P`;
* `hPY4` — the short-short capacity input `P ≤ Y⁴`, and `hYP2 : Y ≤ P²`.

Given these, the conclusion is a deterministic finite consequence.

**There is no theorem `H7_CLOSED` in this bank**: no version of this statement
exists with hidden assumptions, and nothing here says anything about the
complementary region `max(alpha, beta) ≥ 4/9`.
-/
import Mathlib
import Gate1B.SafeAlgebra.H7ScopeFirewall
import Gate1B.SafeAlgebra.H7JointPrimeCapacity
import Gate1B.SafeExtensions.H7SourceEnergy

namespace Gate1B.SafeExtensions

open Finset
open Gate1B.SafeAlgebra

variable {Pi : Type*} [Fintype Pi]
variable {Ch : Type*} [Fintype Ch]

/-- The H7 short-short target bound: the packet is at most
`2 · logWeight · Y⁸ · sqrt(Y·L1·L2)`, i.e. the capacity `Y^(17/2)` scale times
the supplied source constants. -/
def H7TargetBound (T : ℂ) (logWeight Y L1 L2 : ℝ) : Prop :=
  ‖T‖ ≤ 2 * logWeight * (Y ^ 8 * Real.sqrt (Y * L1 * L2))

/-- **`H7_PHARD_SHORTSHORT_CONDITIONAL_COMPILER`.**

Inside the locked short-short scope, and given the explicitly supplied
large-sieve data, source energies, weight bound and capacity relations, the joint
prime packet obeys the `Y^(17/2)` target bound. -/
theorem h7_shortShort_closed_of_inputs
    {iD iB : Type*} [Fintype iD] [Fintype iB]
    (hScope : H7ShortShortScope)
    (w : Pi → ℝ) (a b : Pi → Ch → ℂ)
    (lsD : LargeSieveBound iD) (lsB : LargeSieveBound iB)
    (aD : iD → ℂ) (aB : iB → ℂ)
    (P Y logWeight L1 L2 : ℝ)
    (hP : 0 < P) (hY : 0 ≤ Y) (hlog : 0 ≤ logWeight) (hL1 : 0 ≤ L1)
    (hw : ∀ p, |w p| ≤ logWeight / P)
    (hYP2 : Y ≤ P ^ 2) (hPY4 : P ≤ Y ^ 4)
    (hQD : lsD.Q = P) (hND : lsD.N = Y) (hQB : lsB.Q = P) (hNB : lsB.N = Y ^ 8)
    (hlossD : 0 ≤ lsD.analyticLoss) (hlossB : 0 ≤ lsB.analyticLoss)
    (hDlink : jointEnergy a ≤ lsD.characterEnergy aD)
    (hBlink : jointEnergy b ≤ lsB.characterEnergy aB)
    (hsrcD : l2Energy aD * lsD.analyticLoss ≤ Y * L1)
    (hsrcB : l2Energy aB * lsB.analyticLoss ≤ Y ^ 8 * L2) :
    regionOf hScope.beta = H7Region.H7ShortShort ∧
      H7TargetBound (∑ p : Pi, (w p : ℂ) * ∑ c : Ch, a p c * b p c)
        logWeight Y L1 L2 := by
  refine ⟨regionOf_scope hScope, ?_⟩
  -- the two supplied energies
  set E_D : ℝ := l2Energy aD * lsD.analyticLoss with hED_def
  set E_B : ℝ := l2Energy aB * lsB.analyticLoss with hEB_def
  have hED0 : 0 ≤ E_D := mul_nonneg (l2Energy_nonneg aD) hlossD
  have hEB0 : 0 ≤ E_B := mul_nonneg (l2Energy_nonneg aB) hlossB
  have hDE : jointEnergy a ≤ (P ^ 2 + Y) * E_D := by
    refine hDlink.trans ?_
    have := lsD.bound aD
    rw [hQD, hND] at this
    calc lsD.characterEnergy aD ≤ (P ^ 2 + Y) * l2Energy aD * lsD.analyticLoss := this
      _ = (P ^ 2 + Y) * E_D := by rw [hED_def]; ring
  have hBE : jointEnergy b ≤ (P ^ 2 + Y ^ 8) * E_B := by
    refine hBlink.trans ?_
    have := lsB.bound aB
    rw [hQB, hNB] at this
    calc lsB.characterEnergy aB ≤ (P ^ 2 + Y ^ 8) * l2Energy aB * lsB.analyticLoss := this
      _ = (P ^ 2 + Y ^ 8) * E_B := by rw [hEB_def]; ring
  -- capacity: `P ≤ Y⁴ ⟹ P² ≤ Y⁸`
  have hcap2 : P ^ 2 ≤ Y ^ 8 := by
    have h : P ^ 2 ≤ (Y ^ 4) ^ 2 := by nlinarith [hP.le, hPY4]
    calc P ^ 2 ≤ (Y ^ 4) ^ 2 := h
      _ = Y ^ 8 := by ring
  -- the deterministic compiler
  have hcomp := h7JointPrime_largeSieve_bound_normalized w a b logWeight P Y E_D E_B
    hP hlog hw hDE hBE
  have hsub := substituted_product (P := P) (Y := Y) (E_D := E_D) (E_B := E_B)
    (L1 := L1) (L2 := L2) hP hY hL1 hED0 hEB0 hYP2 hcap2 hsrcD hsrcB
  unfold H7TargetBound
  refine hcomp.trans ?_
  have hfac : logWeight / P
      * (Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B))
      = logWeight * ((1 / P)
        * (Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B))) := by
    field_simp
  rw [hfac]
  have := mul_le_mul_of_nonneg_left hsub hlog
  calc logWeight * ((1 / P)
        * (Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B)))
      ≤ logWeight * (2 * (Y ^ 8 * Real.sqrt (Y * L1 * L2))) := this
    _ = 2 * logWeight * (Y ^ 8 * Real.sqrt (Y * L1 * L2)) := by ring

/-- The exponent reading of the target bound: `Y⁸ · sqrt Y = Y⁹ / sqrt Y`, i.e.
the output sits a factor `Y^(-1/2)` below the natural scale `Y⁹`. -/
theorem h7_target_is_half_power_below (Y : ℝ) (hY : 0 < Y) :
    Y ^ 8 * Real.sqrt Y = Y ^ 9 / Real.sqrt Y := by
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hsq : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY.le
  field_simp
  nlinarith [hsq, sq_nonneg (Real.sqrt Y)]

end Gate1B.SafeExtensions
