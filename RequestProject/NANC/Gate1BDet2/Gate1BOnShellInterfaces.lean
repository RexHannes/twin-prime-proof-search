import RequestProject.NANC.Gate1BDet2.PrimitiveDet2PairConverse
import RequestProject.NANC.Gate1BDet2.CommonShiftRigidity

/-!
# Gate 1B / determinant-2 bank, Module 29: on-shell Gate-1B interfaces

This module *extends* the existing interface layer (`Gate1BInterfaces`,
`Gate1BMCInterfaces`) rather than replacing it; the propositions live in their
own namespace `OnShell`.  **No `axiom` is introduced.**

Two of the propositions are genuinely banked, because the corresponding exact
mathematics is proved in this bank:

* `PrimitivePairSurfaceBanked` — the forward/converse/gcd pair-surface package;
* `ShortIntervalRigidityBanked` — the residue-uniqueness step.

All the analytic ones are open interfaces, never inhabited.  In particular the
implications

  `PrimitivePairSurfaceBanked → OnShellAnalyticCoreClosed`,
  `CommonShiftGraphControlled → OnShellAnalyticCoreClosed`,

are **not** proved (guards below exhibit the gap), and `BetaU2ProjectorStable`
is not proved.

The one valid deterministic package is

  `OnShellAnalyticCoreClosed + SourceExpectedTermIdentified +
   Kappa4NormalizationMatched + FixedSwitchedPacketReassembled → Gate1BClosed`.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace OnShell

/-! ## 1. The banked structural propositions -/

/-- The exact pair-surface package of Modules 19–21, as a single proposition. -/
def PrimitivePairSurfaceBanked : Prop :=
  ∀ u l v₁ z₁ v₂ z₂ h : ℤ, Int.gcd u l = 1 → 0 < h →
    v₂ = v₁ + l * h → z₂ = z₁ + u * h →
      (OnDet2Line u l v₁ z₁ ↔ v₂ * z₁ - v₁ * z₂ = 2 * h) ∧
        (Int.gcd (v₂ - v₁) (z₂ - z₁) : ℤ) = h

/-- **BANKED.**  The pair-surface package holds; it is exact structural
mathematics, and by itself it is *not* analytic progress. -/
theorem primitivePairSurfaceBanked_holds : PrimitivePairSurfaceBanked := by
  intro u l v₁ z₁ v₂ z₂ h hc hh hv hz
  exact primitive_det2_pair_surface hc hh hv hz

/-- The short-interval residue-uniqueness step of Module 22, as a proposition. -/
def ShortIntervalRigidityBanked : Prop :=
  ∀ u z₁ l₁ l₂ : ℤ, 0 < u → IsCoprime z₁ u →
    l₁ * z₁ ≡ 2 [ZMOD u] → l₂ * z₁ ≡ 2 [ZMOD u] → |l₁ - l₂| < u → l₁ = l₂

/-- **BANKED.**  The rigidity step holds. -/
theorem shortIntervalRigidityBanked_holds : ShortIntervalRigidityBanked := by
  intro u z₁ l₁ l₂ hu hcop h₁ h₂ hshort
  exact ell_unique_in_short_interval hu hcop h₁ h₂ hshort

/-! ## 2. Open analytic interfaces -/

/-- **OPEN INTERFACE.**  The common-shift incidence graph is controlled: the
relevant bilinear form is bounded by `bound`.  The *finite* degree arithmetic is
banked in `CommonShiftRigidity`; the analytic control is not. -/
def CommonShiftGraphControlled (graphSum bound : ℝ) : Prop := |graphSum| ≤ bound

/-- **OPEN INTERFACE.**  Stability of the `β`-`U²` projector. -/
def BetaU2ProjectorStable (projectorError tol : ℝ) : Prop := |projectorError| ≤ tol

/-- **OPEN INTERFACE.**  The five-prime `β` joint moment bound. -/
def FivePrimeBetaJointMoment (moment bound : ℝ) : Prop := |moment| ≤ bound

/-- **OPEN INTERFACE.**  The Pascadi quotient interface (the external analytic
proposition is not formalized anywhere in this bank). -/
def PascadiQuotientInterface (quotientSum bound : ℝ) : Prop := |quotientSum| ≤ bound

/-- **OPEN INTERFACE.**  A determinant-conditioned `U^{1+}` input. -/
def DeterminantConditionedU1Plus (sum bound : ℝ) : Prop := |sum| ≤ bound

/-- **OPEN INTERFACE.**  Compatibility of the source weight with automorphic
invariance. -/
def AutomorphicSourceWeightCompatible (weightDefect tol : ℝ) : Prop := |weightDefect| ≤ tol

/-- **OPEN SOURCE INTERFACE.**  The source expected term agrees with the banked
centering term up to `tol`. -/
def SourceExpectedTermIdentified (sourceExpected centering tol : ℝ) : Prop :=
  |sourceExpected - centering| ≤ tol

/-- **OPEN SOURCE INTERFACE.**  The `κ₄` normalisation is matched. -/
def Kappa4NormalizationMatched (kappaError tol : ℝ) : Prop := |kappaError| ≤ tol

/-- **OPEN SOURCE INTERFACE.**  The fixed switched packet reassembles the total
out of the on-shell analytic core, the expected-term discrepancy and the `κ₄`
residue, up to `rem`. -/
def FixedSwitchedPacketReassembled
    (total core sourceExpected centering kappaError rem : ℝ) : Prop :=
  |total - (core + (sourceExpected - centering) + kappaError)| ≤ rem

/-! ## 3. Targets -/

/-- **UNINHABITED TARGET.**  The on-shell analytic core is closed. -/
def OnShellAnalyticCoreClosed (core bound : ℝ) : Prop := |core| ≤ bound

/-- **UNINHABITED TARGET.**  Gate 1B is closed.  Nothing in this development
proves it. -/
def Gate1BClosed (gate1BTotal bound : ℝ) : Prop := |gate1BTotal| ≤ bound

/-! ## 4. The valid deterministic package -/

/-- **Closure package (triangle inequality only).**  Given the on-shell core
bound, the source expected term, the `κ₄` normalisation and the packet
reassembly, the Gate-1B total is bounded by the sum of the tolerances.  This
proves none of its premises; in particular it does not prove `Gate1BClosed`. -/
theorem gate1BClosed_of_onShell_interfaces
    {total core sourceExpected centering kappaError b t₂ t₃ rem : ℝ}
    (hcore : OnShellAnalyticCoreClosed core b)
    (hsrc : SourceExpectedTermIdentified sourceExpected centering t₂)
    (hkappa : Kappa4NormalizationMatched kappaError t₃)
    (hpkt : FixedSwitchedPacketReassembled total core sourceExpected centering kappaError rem) :
    Gate1BClosed total (b + t₂ + t₃ + rem) := by
  unfold Gate1BClosed OnShellAnalyticCoreClosed SourceExpectedTermIdentified
    Kappa4NormalizationMatched FixedSwitchedPacketReassembled at *
  set S := core + (sourceExpected - centering) + kappaError with hS
  have h1 : |total| ≤ |total - S| + |S| := by
    have := abs_add_le (total - S) S
    simpa using this
  have h2 : |S| ≤ b + t₂ + t₃ := by
    have a1 : |S| ≤ |core + (sourceExpected - centering)| + |kappaError| := by
      rw [hS]; exact abs_add_le _ _
    have a2 : |core + (sourceExpected - centering)| ≤ |core| + |sourceExpected - centering| :=
      abs_add_le _ _
    linarith
  linarith

/-! ## 5. Guards -/

/-- **Guard D.**  The banked pair surface is *not* analytic progress sufficient
for closure: it holds unconditionally, while the on-shell analytic core
interface can fail.  Hence `PrimitivePairSurfaceBanked → OnShellAnalyticCoreClosed`
is unprovable, and is not proved. -/
theorem pairSurface_does_not_close_core :
    PrimitivePairSurfaceBanked ∧ ¬ OnShellAnalyticCoreClosed 1 0 := by
  refine ⟨primitivePairSurfaceBanked_holds, ?_⟩
  unfold OnShellAnalyticCoreClosed; norm_num

/-- **Guard.**  Likewise graph control at some bound does not close the core at
that bound. -/
theorem graphControl_does_not_close_core :
    CommonShiftGraphControlled 0 1 ∧ ¬ OnShellAnalyticCoreClosed 2 1 := by
  constructor
  · unfold CommonShiftGraphControlled; norm_num
  · unfold OnShellAnalyticCoreClosed; norm_num

/-- **Guard.**  `BetaU2ProjectorStable` is not automatic (and is nowhere
proved). -/
theorem betaU2_not_automatic : ¬ BetaU2ProjectorStable 1 0 := by
  unfold BetaU2ProjectorStable; norm_num

/-- **Guard.**  The interfaces are satisfiable, hence genuine open inputs rather
than vacuous or contradictory statements. -/
theorem onShell_interfaces_satisfiable :
    BetaU2ProjectorStable 1 1 ∧ DeterminantConditionedU1Plus 1 1 ∧
      AutomorphicSourceWeightCompatible 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [BetaU2ProjectorStable, DeterminantConditionedU1Plus,
      AutomorphicSourceWeightCompatible]

/-- **Guard.**  Nothing here inhabits `Gate1BClosed`: it is a genuine
constraint, false for suitable data. -/
theorem gate1BClosed_not_automatic : ¬ Gate1BClosed 1 0 := by
  unfold Gate1BClosed; norm_num

end OnShell
end Gate1BDet2
end TwinPrimeProject
