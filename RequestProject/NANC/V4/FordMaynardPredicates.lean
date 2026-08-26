/-
NANC V4 — exact finite-at-scale Ford–Maynard Type-I / Type-II predicates.

These are DEFINITIONS ONLY.  Nothing in this file inhabits either predicate:
the Ford–Maynard Type-I and Type-II hypotheses are *external analytic inputs*.

Design notes.

* We do not attempt to encode `x^γ` or asymptotic notation.  The dyadic scale
  `X`, the outer range of `m`, and the family of admissible intervals `I` are
  supplied as explicit finite data.  This is the "finite-at-scale" form of the
  hypotheses; the passage from the finite-at-scale form to the asymptotic form
  is itself part of the external analytic layer.

* The Type-I shape is preserved exactly: outer `m`-sum, `τ^B(m)` weight,
  *maximum over intervals* `I`, and multiplicative argument `w(m*n)`.  The
  maximum is encoded by universally quantifying over interval *selection
  functions* `m ↦ I m`, which is equivalent to bounding the sum of maxima and
  avoids nonemptiness side conditions.

* The Type-II shape is preserved exactly: the universal quantifier over
  *arbitrary* divisor-bounded complex coefficients `ξ_m, κ_n` appears literally.
-/
import Mathlib
import RequestProject.NANC.V4.Status

namespace NANC.V4

open scoped BigOperators

/-- The dyadic support condition `X/2 < m*n ≤ X`, written without division. -/
def dyadicSupport (X m n : ℕ) : Prop := X < 2 * (m * n) ∧ m * n ≤ X

instance (X m n : ℕ) : Decidable (dyadicSupport X m n) := by
  unfold dyadicSupport; infer_instance

/-- The part of an interval `I` that lies in the dyadic window for a given `m`. -/
def dyadicPart (X m : ℕ) (I : Finset ℕ) : Finset ℕ := I.filter (fun n => dyadicSupport X m n)

/-- An *interval selection*: for each outer variable `m`, a choice of admissible
interval `I m` from the given family. -/
def IsSelection (intervals : Finset (Finset ℕ)) (Isel : ℕ → Finset ℕ) : Prop :=
  ∀ m, Isel m ∈ intervals

/-- The Type-I quantity attached to a selection: `∑_m τ(m) · |∑_{n ∈ I m, X/2 < mn ≤ X} w(mn)|`. -/
noncomputable def typeISum (X : ℕ) (typeIRange : Finset ℕ) (tauWeight w : ℕ → ℝ)
    (Isel : ℕ → Finset ℕ) : ℝ :=
  ∑ m ∈ typeIRange, tauWeight m * |∑ n ∈ dyadicPart X m (Isel m), w (m * n)|

/-- **Ford–Maynard Type-I hypothesis, finite-at-scale form.**

`∑_{m ∈ typeIRange} τ^B(m) · max_{I ∈ intervals} |∑_{n ∈ I, X/2 < mn ≤ X} w(mn)| ≤ target`,

with the maximum encoded via arbitrary interval selections.

NO INHABITANT is provided anywhere in this bank. -/
def FMTypeIAtScale (X : ℕ) (typeIRange : Finset ℕ) (intervals : Finset (Finset ℕ))
    (tauWeight w : ℕ → ℝ) (target : ℝ) : Prop :=
  ∀ Isel : ℕ → Finset ℕ, IsSelection intervals Isel →
    typeISum X typeIRange tauWeight w Isel ≤ target

/-- Divisor-boundedness of a complex coefficient sequence on a finite range. -/
def DivisorBoundedCoeff (R : Finset ℕ) (divisorWeight : ℕ → ℝ) (xi : ℕ → ℂ) : Prop :=
  ∀ m ∈ R, ‖xi m‖ ≤ divisorWeight m

/-- The bilinear Type-II sum `∑_m ∑_{n : X/2 < mn ≤ X} ξ_m κ_n w(mn)`. -/
noncomputable def typeIISum (X : ℕ) (typeIIRange nRange : Finset ℕ) (w : ℕ → ℂ)
    (xi kappa : ℕ → ℂ) : ℂ :=
  ∑ m ∈ typeIIRange, ∑ n ∈ nRange.filter (fun n => dyadicSupport X m n),
    xi m * kappa n * w (m * n)

/-- **Ford–Maynard Type-II hypothesis, finite-at-scale form.**

For **all** divisor-bounded complex `ξ, κ`, the bilinear sum is `≤ target` in norm.

CRITICAL: the universal quantifier over arbitrary `ξ, κ` appears literally; this is
what distinguishes the genuine Ford–Maynard Type-II hypothesis from any bound for
one specific pair of source packets.

NO INHABITANT is provided anywhere in this bank. -/
def FMTypeIIAtScale (X : ℕ) (typeIIRange nRange : Finset ℕ) (dwM dwN : ℕ → ℝ)
    (w : ℕ → ℂ) (target : ℝ) : Prop :=
  ∀ xi kappa : ℕ → ℂ, DivisorBoundedCoeff typeIIRange dwM xi →
    DivisorBoundedCoeff nRange dwN kappa →
    ‖typeIISum X typeIIRange nRange w xi kappa‖ ≤ target

/-- A **source-specific** Type-II bound: the same bilinear sum, but only for one
fixed pair of coefficient sequences.  This is what a concrete packet computation
produces. -/
def SourceSpecificTypeII (X : ℕ) (typeIIRange nRange : Finset ℕ) (w : ℕ → ℂ)
    (xi0 kappa0 : ℕ → ℂ) (target : ℝ) : Prop :=
  ‖typeIISum X typeIIRange nRange w xi0 kappa0‖ ≤ target

/-- Trivially, the universal Type-II hypothesis implies each source-specific
instance whose coefficients are divisor bounded. -/
theorem FMTypeII_imp_sourceSpecific {X : ℕ} {R Rn : Finset ℕ} {dwM dwN : ℕ → ℝ}
    {w : ℕ → ℂ} {target : ℝ} {xi0 kappa0 : ℕ → ℂ}
    (h : FMTypeIIAtScale X R Rn dwM dwN w target)
    (hxi : DivisorBoundedCoeff R dwM xi0) (hkappa : DivisorBoundedCoeff Rn dwN kappa0) :
    SourceSpecificTypeII X R Rn w xi0 kappa0 target :=
  h xi0 kappa0 hxi hkappa

/-- **Firewall (finite counterexample).**  The converse fails: a source-specific
Type-II bound does *not* imply the Ford–Maynard Type-II hypothesis, not even for
divisor-bounded source coefficients.  Witness: `X = 1`, ranges `{1}`,
`w ≡ 1`, divisor weights `≡ 1`, `target = 0`, source coefficients `ξ₀ = κ₀ = 0`. -/
theorem sourceSpecificTypeII_not_definitionally_FMTypeII :
    ∃ (X : ℕ) (R Rn : Finset ℕ) (dwM dwN : ℕ → ℝ) (w : ℕ → ℂ) (xi0 kappa0 : ℕ → ℂ)
      (target : ℝ),
      DivisorBoundedCoeff R dwM xi0 ∧ DivisorBoundedCoeff Rn dwN kappa0 ∧
      SourceSpecificTypeII X R Rn w xi0 kappa0 target ∧
      ¬ FMTypeIIAtScale X R Rn dwM dwN w target := by
  refine ⟨1, {1}, {1}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0, 0,
    ?_, ?_, ?_, ?_⟩
  · intro m _; norm_num
  · intro m _; norm_num
  · simp [SourceSpecificTypeII, typeIISum]
  · intro h
    have h1 := h (fun _ => 1) (fun _ => 1) (fun m _ => by norm_num) (fun m _ => by norm_num)
    simp [typeIISum, dyadicSupport] at h1

/-- Status of the Type-I predicate in the bank. -/
def statusFMTypeIPredicate : BankStatus := BankStatus.uninhabitedInterface

/-- Status of the Type-II predicate in the bank. -/
def statusFMTypeIIPredicate : BankStatus := BankStatus.uninhabitedInterface

theorem statusFMTypeI_not_proofBearing :
    BankStatus.IsProofBearing statusFMTypeIPredicate = false := by decide

theorem statusFMTypeII_not_proofBearing :
    BankStatus.IsProofBearing statusFMTypeIIPredicate = false := by decide

end NANC.V4
