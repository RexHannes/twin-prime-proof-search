/-
# NANC Gate 1A v9.6 — certificate construction attempts

The v9.5 bank left four structures without inhabitants:

    RootDefectSourceFactorization
    ZeroProjectiveSourceFactorization
    Gate1ACleanP3ClosureCertificateV95
    Gate1AAllMClosureCertificate  (attempted in `V96SourceDictionary`)

This file settles the first three, and states precisely what an inhabitant is
worth in each case.  The pattern found in every one of them is the same and it
is the central v9.6 audit finding:

> the object the certificate is *about* is a **free field** of the structure,
> so the structure is inhabited canonically, and the whole analytic content sits
> in the separate equation pinning that field to the actual Gate 1A source.

Accordingly each construction below comes with

* a canonical inhabitant, built from the actual repository definitions, and
* a *pinning* predicate together with a rigidity theorem showing that the
  factorization hypothesis determines the free field uniquely, so that pinning
  is exactly the remaining content.

No analytic estimate is created, no axiom is introduced, and no v9–v9.5 item is
weakened.
-/
import Mathlib
import RequestProject.NANC.Gate1A.SafeExtensions.RootDefectFactor
import RequestProject.NANC.Gate1A.SafeExtensions.ProjectiveSourceInterfaces
import RequestProject.NANC.Gate1A.SafeExtensions.V95Closure

namespace TwinPrimeProject.NANC.Gate1A.V96

open Finset
open TwinPrimeProject.NANC.Gate1A.V91
open TwinPrimeProject.NANC.Gate1A.V95

/-! ## 1. `RootDefectSourceFactorization` — canonical inhabitant -/

variable {n : ℕ} [NeZero n]

/-- **Canonical root–defect source factorization.**  Given actual root maps,
analysis weights and a defect weight, the hard parent that *does* factor as
`A₁* W A₂` is definable, so the interface is inhabited. -/
noncomputable def canonicalRootDefect
    (State₁ State₂ : Type) [Fintype State₁] [Fintype State₂]
    (rho₁ : State₁ → ZMod n) (rho₂ : State₂ → ZMod n)
    (beta₁ : State₁ → ℂ) (beta₂ : State₂ → ℂ) (w : ZMod n → ℂ) :
    RootDefectSourceFactorization n where
  State₁ := State₁
  State₂ := State₂
  rho₁ := rho₁
  rho₂ := rho₂
  beta₁ := beta₁
  beta₂ := beta₂
  w := w
  hardParent := fun f g =>
    ∑ z : ZMod n, (starRingEnd ℂ) (rootAnalysis rho₁ beta₁ f z)
      * defectOp w (rootAnalysis rho₂ beta₂ g) z
  factorization := fun _ _ => rfl

/-- `RootDefectSourceFactorization` is inhabited. -/
theorem rootDefectSourceFactorization_inhabited
    (State₁ State₂ : Type) [Fintype State₁] [Fintype State₂]
    (rho₁ : State₁ → ZMod n) (rho₂ : State₂ → ZMod n)
    (beta₁ : State₁ → ℂ) (beta₂ : State₂ → ℂ) (w : ZMod n → ℂ) :
    Nonempty (RootDefectSourceFactorization n) :=
  ⟨canonicalRootDefect State₁ State₂ rho₁ rho₂ beta₁ beta₂ w⟩

/-- A factorization **pins** an externally given hard parent form when its
`hardParent` field is literally that form. -/
def PinsHardParent (S : RootDefectSourceFactorization n)
    (P : (S.State₁ → ℂ) → (S.State₂ → ℂ) → ℂ) : Prop :=
  S.hardParent = P

/-- **Rigidity.**  The factorization hypothesis determines `hardParent`
uniquely, so the only content of an inhabitant is the pinning equation: a
factorization certificate proves something about the actual Gate parent exactly
when the actual parent equals this canonical form. -/
theorem rootDefect_hardParent_unique (S : RootDefectSourceFactorization n)
    (f : S.State₁ → ℂ) (g : S.State₂ → ℂ) :
    S.hardParent f g
      = ∑ z : ZMod n, (starRingEnd ℂ) (rootAnalysis S.rho₁ S.beta₁ f z)
          * defectOp S.w (rootAnalysis S.rho₂ S.beta₂ g) z :=
  S.factorization f g

/-! ## 2. `ZeroProjectiveSourceFactorization` — canonical inhabitant -/

variable {Row Graph Prod' : Type*} [Fintype Row] [Fintype Graph] [Fintype Prod']
  [DecidableEq Prod']

/-- **Canonical zero-projective source factorization.**  The source coefficient
that *is* the projective row is definable, and the trivial fibre bound
`#(Row × Graph)` is proved, so the interface is inhabited. -/
noncomputable def canonicalZeroProjective
    (pmap : Row → Graph → Prod') (A : Row → ℂ) (B : Graph → ℂ) :
    ZeroProjectiveSourceFactorization Row Graph Prod' where
  pmap := pmap
  A := A
  B := B
  sourceCoeff := fun w => projRow pmap A B w
  factorization := fun _ => rfl
  fibreCard := (Fintype.card (Row × Graph) : ℝ)
  fibreCard_le := by
    intro w
    exact_mod_cast Finset.card_le_univ
      (Finset.univ.filter fun p : Row × Graph => pmap p.1 p.2 = w)

/-- `ZeroProjectiveSourceFactorization` is inhabited. -/
theorem zeroProjectiveSourceFactorization_inhabited
    (pmap : Row → Graph → Prod') (A : Row → ℂ) (B : Graph → ℂ) :
    Nonempty (ZeroProjectiveSourceFactorization Row Graph Prod') :=
  ⟨canonicalZeroProjective pmap A B⟩

/-- The canonical inhabitant carries the *trivial* fibre multiplicity
`#(Row × Graph)`; an `X^{o(1)}` fibre bound is a strictly further input. -/
theorem canonicalZeroProjective_fibreCard
    (pmap : Row → Graph → Prod') (A : Row → ℂ) (B : Graph → ℂ) :
    (canonicalZeroProjective pmap A B).fibreCard = (Fintype.card (Row × Graph) : ℝ) := rfl

/-- **Rigidity.**  As above, the factorization equality determines the source
coefficient, so an inhabitant is worth exactly its pinning to the actual Gate
source coefficient. -/
theorem zeroProjective_sourceCoeff_unique
    (S : ZeroProjectiveSourceFactorization Row Graph Prod') (w : Prod') :
    S.sourceCoeff w = projRow S.pmap S.A S.B w :=
  S.factorization w

/-! ## 3. `Gate1ACleanP3ClosureCertificateV95` — inhabitant and its price -/

/-- **Clean-P3 closure certificate from an explicit `E♯` bound.**  This is the
only honest way to inhabit the type: the generic bound and the exception bank
are supplied, and the budget inequality is checked. -/
noncomputable def cleanP3Certificate_of_bound {R : Type*} [Fintype R]
    (P : V94.PositiveRowEnlargement R) (energy : R → ℝ) (henergy : ∀ r, 0 ≤ energy r)
    (genericBound exceptionalEnergy exceptionBank cleanP3Target : ℝ)
    (hgen : ∑ r ∈ P.esharpRows, energy r ≤ genericBound)
    (hexc : exceptionalEnergy ≤ exceptionBank)
    (hbudget : genericBound + exceptionBank ≤ cleanP3Target) :
    Gate1ACleanP3ClosureCertificateV95 R where
  enlargement := P
  energy := energy
  energy_nonneg := henergy
  genericBound := genericBound
  esharp_controlled := hgen
  exceptionalEnergy := exceptionalEnergy
  exceptionBank := exceptionBank
  exceptional_controlled := hexc
  cleanP3Target := cleanP3Target
  budget := hbudget

/-- **Price of the clean-P3 certificate.**  Choosing the target to be the
quantity one is trying to bound always succeeds: the type is inhabited with a
self-referential target for *every* non-negative energy.  Hence inhabiting the
type is not closure; closure is inhabiting it with the *physical* target
`M L⁴ / H` supplied from outside. -/
theorem cleanP3Certificate_self_referential {R : Type*} [Fintype R]
    (P : V94.PositiveRowEnlargement R) (energy : R → ℝ) (henergy : ∀ r, 0 ≤ energy r) :
    ∃ C : Gate1ACleanP3ClosureCertificateV95 R,
      C.cleanP3Target = ∑ r ∈ P.esharpRows, energy r :=
  ⟨cleanP3Certificate_of_bound P energy henergy (∑ r ∈ P.esharpRows, energy r) 0 0
      (∑ r ∈ P.esharpRows, energy r) (le_refl _) (le_refl _) (by simp), rfl⟩

/-- A clean-P3 certificate reaches the **physical** Gate 1A target `M L⁴ / H`
exactly when the supplied generic bound and exception bank fit inside it. -/
theorem cleanP3Certificate_physical_target {R : Type*} [Fintype R]
    (P : V94.PositiveRowEnlargement R) (energy : R → ℝ) (henergy : ∀ r, 0 ≤ energy r)
    (M L H genericBound exceptionBank : ℝ)
    (hgen : ∑ r ∈ P.esharpRows, energy r ≤ genericBound)
    (hbudget : genericBound + exceptionBank ≤ M * L ^ 4 / H)
    (hexc : (0 : ℝ) ≤ exceptionBank) :
    (∑ r ∈ P.cleanRows, energy r) + 0 ≤ M * L ^ 4 / H :=
  Gate1ACleanP3ClosureCertificateV95.toTarget
    (cleanP3Certificate_of_bound P energy henergy genericBound 0 exceptionBank
      (M * L ^ 4 / H) hgen hexc hbudget)

end TwinPrimeProject.NANC.Gate1A.V96
