import Gate1B.HStarAnchorPreservingCovariance

/-!
# Gate 1B · the **true current analytic residual**, as an uninhabited interface

This module contains **no analytic theorem**.  It contains

* the interface `HStarK0J0AnchorPreservingCovarianceBound`, whose sole analytic
  field is a bound for the exact finite anchor-preserving centred covariance of
  `Gate1B.HStarAnchorPreservingCovariance`.  It corresponds semantically to

  ```
  HSTAR-K0J0-PERRON-INTEGRATED-SMALLG-ANCHORPRESERVING-
  CENTERED-MOBIUSPRIME-COVARIANCE45
  ```

  It is **never inhabited**: no axiom, no `sorry`, no default constructor and
  no instance is provided anywhere in this repository;

* the deterministic downstream compilers that are proved *conditionally on* an
  argument of that interface type;

* **non-vacuity guards**: the centred factors are not identically zero, so the
  interface is a genuine analytic claim, not a statement about a trivial
  object;

* the `FM722` generated-source metadata layer (§20), also never inhabited and
  stated only for *generated* coefficient families, never for arbitrary ones.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarAnchorInterface

open Finset
open TwinPrimeProject.CurrentProgramme.HStarTwoAnchor
open TwinPrimeProject.CurrentProgramme.HStarCentered
open TwinPrimeProject.CurrentProgramme.HStarAnchorCovariance

/-! ## 1. Non-vacuity guards for the centred factors -/

/-- The principal model at a unit residue equals `1/φ(q)`. -/
theorem unitPrincipal_of_unit {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    unitPrincipal q (u : ZMod q) = 1 / (q.totient : ℂ) := by
  classical
  rw [unitPrincipal, Finset.sum_eq_single u]
  · simp
  · intro b _ hb
    have : (b : ZMod q) ≠ (u : ZMod q) := fun h => hb (Units.ext h)
    simp [this]
  · intro hb; exact absurd (Finset.mem_univ _) hb

/-- The centred projector at a unit residue equals `1 − 1/φ(q)`. -/
theorem centeredProjector_at_unit {q : ℕ} [NeZero q] (u : (ZMod q)ˣ)
    (hu : (u : ZMod q) = -2) :
    centeredProjector q (-2) = 1 - 1 / (q.totient : ℂ) := by
  rw [centeredProjector, if_pos rfl, ← hu, unitPrincipal_of_unit u]

/-- **Non-vacuity guard.**  Whenever `−2` is a unit modulo `q` and `φ(q) > 1`,
the centred factor at the anchored residue is nonzero.  The covariance object
is therefore not identically zero for structural reasons. -/
theorem centeredProjector_neg_two_ne_zero {q : ℕ} [NeZero q] (u : (ZMod q)ˣ)
    (hu : (u : ZMod q) = -2) (hphi : 1 < q.totient) :
    centeredProjector q (-2) ≠ 0 := by
  rw [centeredProjector_at_unit u hu]
  intro h
  have hphi0 : ((q.totient : ℂ)) ≠ 0 := totient_cast_ne_zero q
  rw [sub_eq_zero] at h
  field_simp at h
  have hnat : q.totient = 1 := by exact_mod_cast h
  omega

/-! ## 2. The analytic interface — UNINHABITED -/

/-- **OPEN ANALYTIC INTERFACE — never inhabited.**

`HStarK0J0AnchorPreservingCovarianceBound` is the sole current analytic
residual of the HSTAR `k = 0`, `J = ∅` two-anchor reconstruction: a power-saving
bound for the exact finite anchor-preserving centred covariance, uniform over
finite families of *physical* two-anchor sources and over amplitudes bounded
by `1`.

No axiom asserts it, no instance is constructed, and nothing downstream of it
is claimed unconditionally. -/
structure HStarK0J0AnchorPreservingCovarianceBound where
  /-- The saving exponent. -/
  eta : ℝ
  eta_pos : 0 < eta
  /-- The implied constant. -/
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- **The analytic field.**  The only unproved content of the interface. -/
  covarianceBound :
    ∀ (n : ℕ) (S : Fin n → HStarTwoAnchorSource) (c : Fin n → ℂ),
      (∀ i, ‖c i‖ ≤ 1) →
        ‖familyCovariance S c‖ ≤ const * (n : ℝ) ^ (1 - eta)

/-- **Deterministic compiler (single source).**  Given the interface, one
physical source obeys the constant bound. -/
theorem single_source_bound (I : HStarK0J0AnchorPreservingCovarianceBound)
    (S : HStarTwoAnchorSource) :
    ‖AnchorPreservingCenteredCovariance S‖ ≤ I.const := by
  have h := I.covarianceBound 1 (fun _ => S) (fun _ => 1) (by intro i; simp)
  have hfam : familyCovariance (fun _ : Fin 1 => S) (fun _ => 1)
      = AnchorPreservingCenteredCovariance S := by
    simp [familyCovariance]
  rw [hfam] at h
  simpa using h

/-- **Deterministic compiler (scaled amplitudes).**  Given the interface, a
family with amplitudes bounded by `A > 0` obeys the bound scaled by `A`. -/
theorem scaled_family_bound (I : HStarK0J0AnchorPreservingCovarianceBound)
    {n : ℕ} (S : Fin n → HStarTwoAnchorSource) (c : Fin n → ℂ) {A : ℝ}
    (hA : 0 < A) (hc : ∀ i, ‖c i‖ ≤ A) :
    ‖familyCovariance S c‖ ≤ A * (I.const * (n : ℝ) ^ (1 - I.eta)) := by
  have hAC : ((A : ℂ)) ≠ 0 := by
    simpa using (ne_of_gt hA)
  have hnorm : ‖((A : ℝ) : ℂ)‖ = A := by
    simp [Complex.norm_real, abs_of_pos hA]
  have h := I.covarianceBound n S (fun i => c i / (A : ℂ)) (by
    intro i
    rw [norm_div, hnorm]
    exact div_le_one_of_le₀ (hc i) hA.le)
  have hEq : familyCovariance S (fun i => c i / (A : ℂ))
      = familyCovariance S c / (A : ℂ) := by
    simp [familyCovariance, Finset.sum_div, div_mul_eq_mul_div]
  rw [hEq, norm_div, hnorm, div_le_iff₀ hA] at h
  calc ‖familyCovariance S c‖ ≤ I.const * (n : ℝ) ^ (1 - I.eta) * A := h
    _ = A * (I.const * (n : ℝ) ^ (1 - I.eta)) := by ring

/-! ## 3. FM722 generated-source metadata layer — UNINHABITED -/

/-- The four ingredients of the intended `FM722` source class. -/
inductive FM722SourceIngredient
  /-- Actual generated `Γ` factors. -/
  | generatedGammaFactors
  /-- The two exact `+2` anchors. -/
  | twoPlusTwoAnchors
  /-- The Möbius-prime source. -/
  | mobiusPrimeSource
  /-- The Perron-integrated coefficient family. -/
  | perronIntegratedCoefficientFamily
  deriving DecidableEq, Repr

/-- The intended source class of

`FM722-ANCHORPRESERVING-QUADRATICDIVISOR-GENERATEDSOURCE45`. -/
def fm722IntendedSourceClass : List FM722SourceIngredient :=
  [FM722SourceIngredient.generatedGammaFactors,
   FM722SourceIngredient.twoPlusTwoAnchors,
   FM722SourceIngredient.mobiusPrimeSource,
   FM722SourceIngredient.perronIntegratedCoefficientFamily]

theorem fm722_sourceClass_has_four_ingredients :
    fm722IntendedSourceClass.length = 4 := by decide

theorem fm722_sourceClass_nodup : fm722IntendedSourceClass.Nodup := by decide

/-- **OPEN TARGET — never inhabited.**  The `FM722` anchor-preserving
quadratic-divisor **generated-source** target.  It is stated *only* for
coefficient families satisfying the generation predicate `generated`; it is
never stated, and never asserted, for arbitrary coefficients. -/
structure FM722AnchorPreservingQuadraticDivisorGeneratedSource
    (generated : ∀ n : ℕ, (Fin n → HStarTwoAnchorSource) → (Fin n → ℂ) → Prop) where
  /-- Metadata: the intended source class. -/
  ingredients : List FM722SourceIngredient
  ingredients_eq : ingredients = fm722IntendedSourceClass
  eta : ℝ
  eta_pos : 0 < eta
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- **The analytic field, restricted to generated families.** -/
  generatedBound :
    ∀ (n : ℕ) (S : Fin n → HStarTwoAnchorSource) (c : Fin n → ℂ),
      generated n S c →
        ‖familyCovariance S c‖ ≤ const * (n : ℝ) ^ (1 - eta)

/-- **Deterministic projection.**  Given the `FM722` target and a *generated*
family, the covariance bound holds for that family.  Nothing is claimed for
non-generated families. -/
theorem fm722_bound_of_target
    {generated : ∀ n : ℕ, (Fin n → HStarTwoAnchorSource) → (Fin n → ℂ) → Prop}
    (F : FM722AnchorPreservingQuadraticDivisorGeneratedSource generated)
    {n : ℕ} (S : Fin n → HStarTwoAnchorSource) (c : Fin n → ℂ)
    (hgen : generated n S c) :
    ‖familyCovariance S c‖ ≤ F.const * (n : ℝ) ^ (1 - F.eta) :=
  F.generatedBound n S c hgen

end HStarAnchorInterface
end CurrentProgramme
end TwinPrimeProject
