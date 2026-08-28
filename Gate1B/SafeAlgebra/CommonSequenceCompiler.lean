/-
# Gate 1B v8.5 — the common-sequence nuclear compiler (finite linear algebra only)

**Status: PROVED_FINITE.**

Setting.  A weighted double sum

    T = ∑_p w p * ∑_c a p c * B p c

is given, where `a` is the (defect) dual coefficient family and `B` is the
`p`-dependent long-source transform.  Suppose an *exact* common-sequence
decomposition is supplied:

    B p c = ∑_ν lambda ν p * template ν c + err p c.

Then `T` splits deterministically into common-sequence packets plus an error
packet, and, given a nuclear cost bound and an error bound, `|T|` is bounded by
the nuclear sum.

**There is no Mellin theorem, no analytic input and no asymptotics here**: this
file is pure finite linear algebra.  Whether the *actual* H7 smooth weights admit
such a decomposition is a separate SOURCE_INTERFACE question
(`Gate1B/SafeExtensions/H7CommonSequenceInterface.lean`).
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

variable {Pi : Type*} [Fintype Pi]
variable {Ch : Type*} [Fintype Ch]
variable {Nu : Type*} [Fintype Nu]

/-- The weighted double sum attached to a coefficient family `a` and a
`p`-dependent sequence `B`. -/
noncomputable def weightedPacket (w : Pi → ℝ) (a B : Pi → Ch → ℂ) : ℂ :=
  ∑ p : Pi, (w p : ℂ) * ∑ c : Ch, a p c * B p c

/-- The pairing of the coefficient family at `p` with a fixed common template. -/
noncomputable def templatePairing (a : Pi → Ch → ℂ) (t : Ch → ℂ) (p : Pi) : ℂ :=
  ∑ c : Ch, a p c * t c

/-- The pairing of the coefficient family at `p` with the (`p`-dependent) error
family. -/
noncomputable def errPairing (a : Pi → Ch → ℂ) (err : Pi → Ch → ℂ) (p : Pi) : ℂ :=
  ∑ c : Ch, a p c * err p c

/-- **Common-sequence expansion.**  An exact decomposition of the `p`-dependent
sequence produces an exact decomposition of the packet: template packets plus the
error packet. -/
theorem commonSequence_expand
    (w : Pi → ℝ) (a B : Pi → Ch → ℂ)
    (lambda : Nu → Pi → ℂ) (template : Nu → Ch → ℂ) (err : Pi → Ch → ℂ)
    (hdec : ∀ p c, B p c = (∑ nu : Nu, lambda nu p * template nu c) + err p c) :
    weightedPacket w a B =
      (∑ nu : Nu, ∑ p : Pi, (w p : ℂ) * lambda nu p * templatePairing a (template nu) p)
        + ∑ p : Pi, (w p : ℂ) * errPairing a err p := by
  classical
  unfold weightedPacket templatePairing errPairing
  have step : ∀ p : Pi,
      (w p : ℂ) * ∑ c : Ch, a p c * B p c
        = (∑ nu : Nu, (w p : ℂ) * lambda nu p * ∑ c : Ch, a p c * template nu c)
          + (w p : ℂ) * ∑ c : Ch, a p c * err p c := by
    intro p
    have h1 : ∀ c : Ch, a p c * B p c
        = (∑ nu : Nu, a p c * (lambda nu p * template nu c)) + a p c * err p c := by
      intro c; rw [hdec p c, mul_add, Finset.mul_sum]
    have hinner : ∑ c : Ch, a p c * B p c
        = (∑ nu : Nu, lambda nu p * ∑ c : Ch, a p c * template nu c)
          + ∑ c : Ch, a p c * err p c := by
      rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun nu _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hinner, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun nu _ => by ring
  rw [Finset.sum_congr rfl fun p _ => step p, Finset.sum_add_distrib, Finset.sum_comm]

/-- **Nuclear bound.**  With
* `∑_p |w p| ≤ wTotal`,
* `‖templatePairing a (template nu) p‖ ≤ sourceNorm nu` for every `p`,
* `‖lambda nu p‖ ≤ lamSup nu` for every `p`,
* `∑_nu lamSup nu * sourceNorm nu ≤ nuclearCost`,
* `‖errPairing a err p‖ ≤ errNorm` for every `p`,

the packet obeys the deterministic inequality

    ‖T‖ ≤ wTotal * nuclearCost + wTotal * errNorm.

Everything on the right is supplied data: no analytic estimate is created. -/
theorem jointPacket_le_nuclear_sum
    (w : Pi → ℝ) (a B : Pi → Ch → ℂ)
    (lambda : Nu → Pi → ℂ) (template : Nu → Ch → ℂ) (err : Pi → Ch → ℂ)
    (lamSup sourceNorm : Nu → ℝ) (wTotal nuclearCost errNorm : ℝ)
    (hdec : ∀ p c, B p c = (∑ nu : Nu, lambda nu p * template nu c) + err p c)
    (hlam : ∀ nu p, ‖lambda nu p‖ ≤ lamSup nu)
    (hlam0 : ∀ nu, 0 ≤ lamSup nu)
    (hsrc : ∀ nu p, ‖templatePairing a (template nu) p‖ ≤ sourceNorm nu)
    (hsrc0 : ∀ nu, 0 ≤ sourceNorm nu)
    (hwtot : ∑ p : Pi, |w p| ≤ wTotal)
    (hnuc : ∑ nu : Nu, lamSup nu * sourceNorm nu ≤ nuclearCost)
    (herr : ∀ p, ‖errPairing a err p‖ ≤ errNorm)
    (herr0 : 0 ≤ errNorm) :
    ‖weightedPacket w a B‖ ≤ wTotal * nuclearCost + wTotal * errNorm := by
  classical
  set S : ℝ := ∑ p : Pi, |w p| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hnuc0 : 0 ≤ nuclearCost :=
    le_trans (Finset.sum_nonneg fun nu _ => mul_nonneg (hlam0 nu) (hsrc0 nu)) hnuc
  -- main term
  have hmain :
      ‖∑ nu : Nu, ∑ p : Pi, (w p : ℂ) * lambda nu p * templatePairing a (template nu) p‖
        ≤ S * ∑ nu : Nu, lamSup nu * sourceNorm nu := by
    calc ‖∑ nu : Nu, ∑ p : Pi, (w p : ℂ) * lambda nu p * templatePairing a (template nu) p‖
        ≤ ∑ nu : Nu, ‖∑ p : Pi, (w p : ℂ) * lambda nu p * templatePairing a (template nu) p‖ :=
          norm_sum_le _ _
      _ ≤ ∑ nu : Nu, ∑ p : Pi, |w p| * (lamSup nu * sourceNorm nu) := by
          refine Finset.sum_le_sum fun nu _ => ?_
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          have hnorm : ‖(w p : ℂ) * lambda nu p * templatePairing a (template nu) p‖
              = |w p| * (‖lambda nu p‖ * ‖templatePairing a (template nu) p‖) := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
          rw [hnorm]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact mul_le_mul (hlam nu p) (hsrc nu p) (norm_nonneg _) (hlam0 nu)
      _ = S * ∑ nu : Nu, lamSup nu * sourceNorm nu := by
          rw [hS, Finset.mul_sum]
          refine Finset.sum_congr rfl fun nu _ => ?_
          rw [← Finset.sum_mul, mul_comm]
  -- error term
  have herrterm : ‖∑ p : Pi, (w p : ℂ) * errPairing a err p‖ ≤ S * errNorm := by
    calc ‖∑ p : Pi, (w p : ℂ) * errPairing a err p‖
        ≤ ∑ p : Pi, ‖(w p : ℂ) * errPairing a err p‖ := norm_sum_le _ _
      _ ≤ ∑ p : Pi, |w p| * errNorm := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (herr p) (abs_nonneg _)
      _ = S * errNorm := by rw [hS, Finset.sum_mul]
  rw [commonSequence_expand w a B lambda template err hdec]
  refine (norm_add_le _ _).trans ?_
  have h1 : S * ∑ nu : Nu, lamSup nu * sourceNorm nu ≤ wTotal * nuclearCost := by
    have := mul_le_mul_of_nonneg_left hnuc hS0
    have h2 : S * nuclearCost ≤ wTotal * nuclearCost :=
      mul_le_mul_of_nonneg_right hwtot hnuc0
    linarith
  have h2 : S * errNorm ≤ wTotal * errNorm := mul_le_mul_of_nonneg_right hwtot herr0
  linarith [hmain, herrterm]

end Gate1B.SafeAlgebra
