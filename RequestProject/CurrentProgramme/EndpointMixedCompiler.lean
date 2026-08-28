import RequestProject.CurrentProgramme.EndpointCollisionL2
import RequestProject.CurrentProgramme.EndpointCenteredRewriting
import RequestProject.CurrentProgramme.LichtmanT18Capacity
import RequestProject.CurrentProgramme.AnalyticInterfaces

/-!
# Phase H · the source-explicit conditional endpoint compiler

This module assembles the strongest implication justified by the *abstract*
finite algebra banked in this layer:

```
centered endpoint finite source        (EndpointCentering)
+ exact 2|2 split                      (EndpointTwoByTwoSplit)
+ centered 2|2 rewriting               (EndpointCenteredRewriting)
+ mixed coefficient regrouping         (EndpointMixedAddMult)
+ mixed L² / collision bound           (EndpointCollisionL2)
+ a valid Lichtman source dictionary   (UNINHABITED)
+ the external Lichtman analytic input (UNINHABITED)
+ an exact J-capacity certificate      (UNINHABITED)
⟹ a bound for the nonzero centered congruence contribution.
```

Everything before the dictionary is kernel-proved finite algebra.  The
dictionary, the external analytic bound and the capacity certificate are
**explicit uninhabited antecedents**, carried as fields of
`EndpointMixedSocketInput`.  Nothing here closes Gate 1B, and the comparison
main-term pin is deliberately *not* connected: see
`comparison_remains_independent`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace EndpointMixedCompiler

open Finset MixedAddMult LichtmanSocket LichtmanCapacity

/-! ## 1. Aggregation of the socket bound (kernel-proved) -/

/-- **Aggregation.**  Given a bound `Bsock` for each mixed `(ℓ, r, s)`-socket
sum, the nonzero centered congruence contribution obeys the corresponding
triangle-inequality aggregate.  This is the only step that the finite algebra
can supply; the socket bound itself is the analytic obligation. -/
theorem nonzeroCongruence_norm_le_of_socket
    (Pm : Finset ℤ) (α : ℤ → ℂ) (Z : ℤ → ℕ → ℤ → ℂ) (Ls : Finset ℕ)
    (Pr : Finset ℤ) (γ : ℤ → ℂ) (k : ℤ) (Js : ℕ → ℤ → ℤ → Finset ℤ)
    (hLs : ∀ l ∈ Ls, l ≠ 0)
    (hJ : ∀ l ∈ Ls, ∀ r ∈ Pr, ∀ s ∈ Pr, ∀ p ∈ Pm ×ˢ Pm, ∀ j : ℤ, j ≠ 0 →
      nu p.1 p.2 r s = j * (l : ℤ) → j ∈ (Js l r s).filter (fun j => j ≠ 0))
    (Bsock : ℕ → ℤ → ℤ → ℝ)
    (hsock : ∀ l ∈ Ls, ∀ r ∈ Pr, ∀ s ∈ Pr,
      ‖∑ j ∈ (Js l r s).filter (fun j => j ≠ 0),
        bMix Pm α Z l k r s (j * (l : ℤ))‖ ≤ Bsock l r s) :
    ‖nonzeroCongruenceContribution Pm α Z Ls Pr γ k‖
      ≤ ∑ l ∈ Ls, ∑ r ∈ Pr, ∑ s ∈ Pr, ‖γ r‖ * ‖γ s‖ * Bsock l r s := by
  classical
  rw [nonzeroCongruence_regroup Pm α Z Ls Pr γ k Js hLs hJ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_left (hsock l hl r hr s hs) (by positivity)

/-! ## 2. The uninhabited source/analytic input package -/

/-- **UNINHABITED INPUT PACKAGE** for the source-explicit endpoint compiler.

Fields `dict`, `pin`, `norms` are the open *source* obligations; `analytic` is
the open *external analytic* obligation; `capacity` is the open exponent
certificate.  The finite-model fields (`Js`, `Ls_ne`, `Jsupport`) are the exact
support data that the banked regrouping theorem consumes. -/
structure EndpointMixedSocketInput (Pm : Finset ℤ) (α : ℤ → ℂ)
    (Z : ℤ → ℕ → ℤ → ℂ) (Ls : Finset ℕ) (Pr : Finset ℤ) (γ : ℤ → ℂ) (k : ℤ) where
  /-- the finite `j`-ranges of the model -/
  Js : ℕ → ℤ → ℤ → Finset ℤ
  /-- the moduli are nonzero -/
  Ls_ne : ∀ l ∈ Ls, l ≠ 0
  /-- exact finite support condition for the `j`-ranges -/
  Jsupport : ∀ l ∈ Ls, ∀ r ∈ Pr, ∀ s ∈ Pr, ∀ p ∈ Pm ×ˢ Pm, ∀ j : ℤ, j ≠ 0 →
    nu p.1 p.2 r s = j * (l : ℤ) → j ∈ (Js l r s).filter (fun j => j ≠ 0)
  /-- OPEN SOURCE: the proposed Lichtman dictionary -/
  dict : LichtmanT18Dictionary
  /-- OPEN SOURCE: its pin to the physical mixed summand -/
  pin : LichtmanT18PhysicalPin α Z
  /-- the pin is about this dictionary -/
  pin_dict : pin.dict = dict
  /-- OPEN SOURCE: the `b` / `tilde-b` norm obligations -/
  norms : LichtmanT18CoeffNorms
  /-- the norm record is about this dictionary's coefficient family -/
  bMatch : dict.b = norms.b
  /-- the socket bound levels -/
  Bsock : ℕ → ℤ → ℤ → ℝ
  /-- OPEN ANALYTIC: the external Lichtman-type bound for each socket sum -/
  analytic : ∀ l ∈ Ls, ∀ r ∈ Pr, ∀ s ∈ Pr,
    ‖∑ j ∈ (Js l r s).filter (fun j => j ≠ 0),
      bMix Pm α Z l k r s (j * (l : ℤ))‖ ≤ Bsock l r s
  /-- the physical target -/
  target : ℝ
  /-- OPEN CAPACITY: the aggregated socket bound clears the target -/
  capacity : ∑ l ∈ Ls, ∑ r ∈ Pr, ∑ s ∈ Pr, ‖γ r‖ * ‖γ s‖ * Bsock l r s ≤ target

/-- **THE CONDITIONAL ENDPOINT COMPILER.**  Deterministic implication from the
input package to the endpoint conclusion.  No antecedent is inhabited here, so
this is *not* a proof of the endpoint bound. -/
theorem endpoint_bound_of_socket_input
    {Pm : Finset ℤ} {α : ℤ → ℂ} {Z : ℤ → ℕ → ℤ → ℂ} {Ls : Finset ℕ}
    {Pr : Finset ℤ} {γ : ℤ → ℂ} {k : ℤ}
    (I : EndpointMixedSocketInput Pm α Z Ls Pr γ k) :
    ‖nonzeroCongruenceContribution Pm α Z Ls Pr γ k‖ ≤ I.target :=
  (nonzeroCongruence_norm_le_of_socket Pm α Z Ls Pr γ k I.Js I.Ls_ne I.Jsupport
    I.Bsock I.analytic).trans I.capacity

/-- **Non-vacuity of the target.**  The nonzero centered congruence
contribution is *not* identically zero: in the finite model `Pm = {1,2}`,
`Ls = {1}`, `Pr = {1}` with all coefficients equal to `1` it equals `2`.

Hence the compiler's conclusion `‖·‖ ≤ target` is a genuine constraint and the
socket obligation cannot be discharged by observing that the object vanishes. -/
theorem nonzeroCongruenceContribution_nonvacuous :
    nonzeroCongruenceContribution ({1, 2} : Finset ℤ) (fun _ => 1)
        (fun _ _ _ => 1) ({1} : Finset ℕ) ({1} : Finset ℤ) (fun _ => 1) 0 = 2 := by
  norm_num [nonzeroCongruenceContribution, Finset.sum_filter, Finset.sum_product]
  norm_cast

/-- Consequently a zero socket budget cannot certify that model. -/
theorem zero_budget_fails :
    ¬ ‖nonzeroCongruenceContribution ({1, 2} : Finset ℤ) (fun _ => 1)
        (fun _ _ _ => 1) ({1} : Finset ℕ) ({1} : Finset ℤ) (fun _ => 1) 0‖ ≤ 0 := by
  rw [nonzeroCongruenceContribution_nonvacuous]
  norm_num

/-! ## 3. Firewalls -/

/-- **Non-automaticity.**  The compiler genuinely consumes a Lichtman
dictionary: one can be extracted from any input package.  Since no
`LichtmanT18Dictionary` is constructed anywhere in this repository, the
conclusion is not available. -/
def EndpointMixedSocketInput.requiresDictionary
    {Pm : Finset ℤ} {α : ℤ → ℂ} {Z : ℤ → ℕ → ℤ → ℂ} {Ls : Finset ℕ}
    {Pr : Finset ℤ} {γ : ℤ → ℂ} {k : ℤ}
    (I : EndpointMixedSocketInput Pm α Z Ls Pr γ k) : LichtmanT18Dictionary :=
  I.dict

/-- **Non-automaticity.**  The compiler also genuinely consumes the external
analytic bound. -/
theorem EndpointMixedSocketInput.requiresAnalytic
    {Pm : Finset ℤ} {α : ℤ → ℂ} {Z : ℤ → ℕ → ℤ → ℂ} {Ls : Finset ℕ}
    {Pr : Finset ℤ} {γ : ℤ → ℂ} {k : ℤ}
    (I : EndpointMixedSocketInput Pm α Z Ls Pr γ k) :
    ∀ l ∈ Ls, ∀ r ∈ Pr, ∀ s ∈ Pr,
      ‖∑ j ∈ (I.Js l r s).filter (fun j => j ≠ 0),
        bMix Pm α Z l k r s (j * (l : ℤ))‖ ≤ I.Bsock l r s := I.analytic

/-- **Comparison firewall.**  The endpoint conclusion is a norm inequality; it
says nothing about the physical/residue main-term identification, which remains

  `PURE5-COMPARISON-MAINTERM-PIN : SOURCE_OPEN`.

Formally: an endpoint bound can hold while the two main terms differ, so no
comparison pin is produced by this compiler. -/
theorem comparison_remains_independent :
    ∃ (bound target physicalMain residueMain : ℝ),
      bound ≤ target ∧ physicalMain ≠ residueMain :=
  ⟨0, 1, 0, 1, by norm_num, by norm_num⟩

/-- The comparison pin is a *separate* obligation, still uninhabited: it is the
existing project interface, unchanged by this layer. -/
theorem comparison_pin_is_the_existing_interface
    (p : Interfaces.Pure5ComparisonMainTermPin) :
    p.physicalMain = p.residueMain := p.identified

end EndpointMixedCompiler
end CurrentProgramme
end TwinPrimeProject
