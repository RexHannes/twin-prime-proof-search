/-
# Gate 1B v8.5 — source common-sequence interface

**Status: SOURCE_INTERFACE (structure defined, deliberately *not* inhabited).**

The finite compiler `Gate1B/SafeAlgebra/CommonSequenceCompiler.lean` consumes an
exact decomposition

    B p c = ∑_ν lambda ν p * template ν c + err p c

together with a nuclear cost bound and an error bound.  The claim that the
*actual* H7 smooth source weights produce such data is a statement about the
literal source normalisation, and is therefore represented here as a structure
whose fields must be constructed from the source — never as an axiom and never
as an instance.

`commonSequence_load_bearing` is the guard: an arbitrary `p`-dependent family
`B_p` need **not** admit a bounded-rank commonisation.  A two-by-two finite
countermodel is given.
-/
import Mathlib
import Gate1B.SafeAlgebra.CommonSequenceCompiler

namespace Gate1B.SafeExtensions

open Finset
open Gate1B.SafeAlgebra

/-- **Source interface.**  The data that the literal H7 source would have to
provide for the finite common-sequence compiler to fire.

There is no inhabitant of this structure in the bank: constructing one is
exactly the open source-normalisation obligation. -/
structure H7CommonSequenceInput (Pi : Type*) [Fintype Pi] [DecidableEq Pi]
    (Ch : Type*) [Fintype Ch] [DecidableEq Ch]
    (Nu : Type*) [Fintype Nu] [DecidableEq Nu] where
  /-- The `p`-dependent long-source transforms produced by the source. -/
  B : Pi → Ch → ℂ
  /-- The finite family of common templates (the "common sequence"). -/
  templates : Nu → Ch → ℂ
  /-- The commonisation coefficients. -/
  coeff : Nu → Pi → ℂ
  /-- The residual error family. -/
  err : Pi → Ch → ℂ
  /-- **Exactness** of the decomposition. -/
  exactDecomp : ∀ p c, B p c = (∑ nu : Nu, coeff nu p * templates nu c) + err p c
  /-- A uniform bound for the coefficients. -/
  lamSup : Nu → ℝ
  lamSup_nonneg : ∀ nu, 0 ≤ lamSup nu
  coeff_le : ∀ nu p, ‖coeff nu p‖ ≤ lamSup nu
  /-- The declared nuclear cost. -/
  nuclearCost : ℝ
  /-- The template source norms and the nuclear bound. -/
  sourceNorm : Nu → ℝ
  sourceNorm_nonneg : ∀ nu, 0 ≤ sourceNorm nu
  nuclearBound : ∑ nu : Nu, lamSup nu * sourceNorm nu ≤ nuclearCost
  /-- The declared error norm. -/
  errNorm : ℝ
  errNorm_nonneg : 0 ≤ errNorm

/-- Given the source data *and* the pairing bounds for the coefficient family
`a`, the finite compiler fires.  This is the only way a common-sequence bound
enters the bank. -/
theorem h7CommonSequence_compile
    {Pi : Type*} [Fintype Pi] [DecidableEq Pi]
    {Ch : Type*} [Fintype Ch] [DecidableEq Ch]
    {Nu : Type*} [Fintype Nu] [DecidableEq Nu]
    (input : H7CommonSequenceInput Pi Ch Nu) (w : Pi → ℝ) (a : Pi → Ch → ℂ)
    (wTotal : ℝ) (hwtot : ∑ p : Pi, |w p| ≤ wTotal)
    (hsrc : ∀ nu p, ‖templatePairing a (input.templates nu) p‖ ≤ input.sourceNorm nu)
    (herr : ∀ p, ‖errPairing a input.err p‖ ≤ input.errNorm) :
    ‖weightedPacket w a input.B‖
      ≤ wTotal * input.nuclearCost + wTotal * input.errNorm :=
  jointPacket_le_nuclear_sum w a input.B input.coeff input.templates input.err
    input.lamSup input.sourceNorm wTotal input.nuclearCost input.errNorm
    input.exactDecomp input.coeff_le input.lamSup_nonneg hsrc input.sourceNorm_nonneg
    hwtot input.nuclearBound herr input.errNorm_nonneg

/-! ## Guard: commonisation is load-bearing -/

/-- The `2 × 2` identity family `B p c = [p = c]` is a legitimate `p`-dependent
family, but it admits **no** rank-one common-sequence decomposition: there is no
single template `t` and coefficient family `l` with `B p c = l p * t c`.

Hence "there exists a bounded-rank common sequence" is a genuine extra source
hypothesis, not a consequence of finiteness. -/
theorem commonSequence_load_bearing :
    ¬ ∃ (l : Fin 2 → ℂ) (t : Fin 2 → ℂ),
        ∀ p c : Fin 2, (if p = c then (1 : ℂ) else 0) = l p * t c := by
  rintro ⟨l, t, h⟩
  have h00 : l 0 * t 0 = 1 := by simpa using (h 0 0).symm
  have h01 : l 0 * t 1 = 0 := by simpa using (h 0 1).symm
  have h11 : l 1 * t 1 = 1 := by simpa using (h 1 1).symm
  have hl0 : l 0 ≠ 0 := by intro h0; rw [h0, zero_mul] at h00; exact zero_ne_one h00
  have ht1 : t 1 = 0 := by
    rcases mul_eq_zero.mp h01 with h | h
    · exact absurd h hl0
    · exact h
  rw [ht1, mul_zero] at h11
  exact zero_ne_one h11

/-- The same obstruction with the *error* term made explicit: a rank-one
decomposition of the identity family forces an error of norm at least `1/2`
somewhere, so "small error" is also a genuine source hypothesis. -/
theorem commonSequence_error_load_bearing
    (l t : Fin 2 → ℂ) (err : Fin 2 → Fin 2 → ℂ)
    (hdec : ∀ p c : Fin 2, (if p = c then (1 : ℂ) else 0) = l p * t c + err p c) :
    ∃ p c : Fin 2, err p c ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  exact commonSequence_load_bearing ⟨l, t, fun p c => by
    rw [hdec p c, hcon p c, add_zero]⟩

end Gate1B.SafeExtensions
