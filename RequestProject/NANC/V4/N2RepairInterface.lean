/-
NANC V4 — proposed N₂ shifted-prime repair: INTERFACE ONLY.

The replacement of the bounded `|w_n|` condition in the Ford–Maynard exceptional
`H₂` region by a source-specific shifted-prime upper bound is a *research
proposal*, not a published theorem.

Therefore:  DEFINED, NOT INHABITED.

    proposed N₂ shifted-prime repair  ≠  published theorem
-/
import Mathlib
import RequestProject.NANC.V4.Status
import RequestProject.NANC.V4.FordMaynardPredicates

namespace NANC.V4

open scoped BigOperators

/-- A finite abstract model of the exceptional factorization region: the
exceptional set `N2set` together with the weight `H`. -/
structure N2Region where
  N2set : Finset ℕ
  H : ℕ → ℝ
  H_nonneg : ∀ n, 0 ≤ H n

/-- The explicit finite inequality demanded of the exceptional region. -/
def N2UpperBound (R : N2Region) (target : ℝ) : Prop :=
  ∑ n ∈ R.N2set, R.H n ≤ target

/-- **Proposed repair (UNINHABITED).**  The required weighted upper bound on the
exceptional factorization region for the shifted-prime sequence. -/
def FMShiftedPrimeN2Upper (R : N2Region) (target : ℝ) : Prop := N2UpperBound R target

/-- **Proposed splice (UNINHABITED).**  The assertion that the `N₂` upper bound may
legally substitute for the bounded-sequence step inside the Ford–Maynard
argument.  This is strictly stronger than the bound itself and is *not* implied
by it. -/
structure FMShiftedPrimeEndgameSplice (R : N2Region) (target : ℝ)
    (substitutionLegal : Prop) : Prop where
  /-- The exceptional-region bound itself. -/
  n2Upper : FMShiftedPrimeN2Upper R target
  /-- A proof that the substitution is legal inside the Ford–Maynard proof.
  This is external analytic content and is never supplied in this bank. -/
  substitutionLegal_holds : substitutionLegal

/-- The splice yields the bound; the converse is deliberately not available. -/
theorem splice_imp_n2Upper {R : N2Region} {target : ℝ} {L : Prop}
    (h : FMShiftedPrimeEndgameSplice R target L) : FMShiftedPrimeN2Upper R target :=
  h.n2Upper

/-- Monotone bookkeeping: a smaller target is a stronger bound. -/
theorem n2Upper_mono {R : N2Region} {t t' : ℝ} (h : FMShiftedPrimeN2Upper R t) (ht : t ≤ t') :
    FMShiftedPrimeN2Upper R t' := le_trans h ht

/-- Trivially, an empty exceptional region satisfies the bound for nonnegative
targets.  This is *not* a proof of the repair: the analytic content is that the
real exceptional region is small. -/
theorem n2Upper_of_empty {R : N2Region} {t : ℝ} (h : R.N2set = ∅) (ht : 0 ≤ t) :
    FMShiftedPrimeN2Upper R t := by
  simp [FMShiftedPrimeN2Upper, N2UpperBound, h, ht]

/-- Status: the proposed repair is a research claim, not a Lean-banked proof. -/
def statusN2Repair : BankStatus := BankStatus.uninhabitedInterface

/-- Status: the endgame splice is a research claim, not a Lean-banked proof. -/
def statusEndgameSplice : BankStatus := BankStatus.uninhabitedInterface

theorem statusN2Repair_not_proofBearing :
    BankStatus.IsProofBearing statusN2Repair = false := by decide

/-- **No-overclaim.**  The `N₂` interface alone does not close Gate 2: the Gate-2
conclusion is a separate Prop and is not implied by the exceptional-region bound.
Witness: an empty exceptional region satisfies the bound while the Gate-2
conclusion is `False`. -/
theorem n2_alone_does_not_close_gate2 :
    ∃ (R : N2Region) (t : ℝ) (gate2 : Prop),
      FMShiftedPrimeN2Upper R t ∧ ¬ gate2 := by
  refine ⟨⟨∅, fun _ => 0, fun _ => le_refl 0⟩, 0, False, ?_, not_false⟩
  simp [FMShiftedPrimeN2Upper, N2UpperBound]

/-! ### Optional finite two-linear-forms upper-sieve scaffold

Only the *interface* is defined.  No sieve theorem is invented, and no
inhabitant is produced: the repository contains no upper-bound sieve result for
the pair of linear forms `p, m·p + 2`. -/

/-- Input data for an upper-bound sieve applied to the two linear forms
`n ↦ n` and `n ↦ m·n + 2`. -/
structure TwoLinearFormsUpperSieveInput where
  /-- The multiplier `m` of the second linear form. -/
  m : ℕ
  /-- The finite sifting range. -/
  range : Finset ℕ
  /-- The sifting level. -/
  level : ℕ
  /-- Nonnegative weights attached to the range. -/
  weight : ℕ → ℝ
  weight_nonneg : ∀ n, 0 ≤ weight n

/-- The conclusion an upper-bound sieve would provide: a bound on the weighted
count of `n` in the range for which both linear forms are prime.  UNINHABITED. -/
def TwoLinearFormsUpperSieveOutput (I : TwoLinearFormsUpperSieveInput) (target : ℝ) : Prop :=
  ∑ n ∈ I.range.filter (fun n => Nat.Prime n ∧ Nat.Prime (I.m * n + 2)), I.weight n ≤ target

/-- Trivial monotonicity of the sieve conclusion in the target.  (Bookkeeping
only; it produces no sieve bound.) -/
theorem twoLinearForms_output_mono {I : TwoLinearFormsUpperSieveInput} {t t' : ℝ}
    (h : TwoLinearFormsUpperSieveOutput I t) (ht : t ≤ t') :
    TwoLinearFormsUpperSieveOutput I t' := le_trans h ht

/-- The Gate-2 application of the sieve scaffold to the exceptional region.
UNINHABITED. -/
def Gate2N2SieveApplication (I : TwoLinearFormsUpperSieveInput) (R : N2Region)
    (target : ℝ) : Prop :=
  TwoLinearFormsUpperSieveOutput I target → FMShiftedPrimeN2Upper R target

end NANC.V4
