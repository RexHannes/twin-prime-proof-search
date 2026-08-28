/-
# Gate 1B v12 — abstract QK source-character covariance: data, exact value,
UNINHABITED bound

**Status: data structure and identities PROVED; the analytic bound is an
UNINHABITED interface.**

`QKSourceCharacterCovarianceData` is a *non-vacuous* finite record: it carries
the two moduli, the two source transforms, the `h`- and `k`-correlations, the
Gauss weights and the physical normalisation.  An explicit inhabitant is given
(`trivialData`) to show the structure is not empty; that inhabitant asserts
nothing analytic.

`qkCovariance` is the exact finite covariance value.  Only deterministic
identities are proved: sector splitting along an arbitrary decomposition
predicate (principal / non-principal routing), and the deterministic triangle
inequality.  No target bound is proved.

`QKSourceCharacterCovarianceBound` is the UNINHABITED analytic interface.

Contents:

* `QKSourceCharacterCovarianceData`, `trivialData`;
* `qkCovariance`;
* `qkCovariance_sector_split`, `qkCovariance_norm_le`;
* `qkCovariance_eq_of_movingMultiplier_decomposition`;
* `QKSourceCharacterCovarianceBound` (UNINHABITED) + non-vacuity guard.
-/
import Mathlib
import Gate1B.SafeAlgebra.MovingMultiplierPrime

namespace Gate1B.SafeExtensions

open Finset Gate1B.SafeAlgebra

/-- **Finite QK source-character covariance data.**  Every field is data; no
field asserts an estimate. -/
structure QKSourceCharacterCovarianceData (Ch : Type*) [Fintype Ch] [DecidableEq Ch] where
  /-- First modulus. -/
  q1 : ℕ
  /-- Second modulus. -/
  q2 : ℕ
  /-- Source transform attached to `q1`. -/
  F1 : Ch → ℂ
  /-- Source transform attached to `q2`. -/
  F2 : Ch → ℂ
  /-- The `h`-correlation. -/
  hCorr : Ch → ℂ
  /-- The `k`-correlation. -/
  kCorr : Ch → ℂ
  /-- The Gauss weights. -/
  gauss : Ch → ℂ
  /-- The physical normalisation. -/
  normalization : ℝ
  /-- The normalisation is positive. -/
  normalization_pos : 0 < normalization

namespace QKSourceCharacterCovarianceData

variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch]

/-- An explicit inhabitant: the structure is **not vacuous**.  It carries no
analytic content. -/
def trivialData (Ch : Type*) [Fintype Ch] [DecidableEq Ch] :
    QKSourceCharacterCovarianceData Ch where
  q1 := 1
  q2 := 1
  F1 := fun _ => 0
  F2 := fun _ => 0
  hCorr := fun _ => 0
  kCorr := fun _ => 0
  gauss := fun _ => 0
  normalization := 1
  normalization_pos := one_pos

/-- The per-character covariance summand. -/
noncomputable def summand (D : QKSourceCharacterCovarianceData Ch) (ch : Ch) : ℂ :=
  D.gauss ch * D.F1 ch * (starRingEnd ℂ) (D.F2 ch)
    * D.hCorr ch * (starRingEnd ℂ) (D.kCorr ch)

/-- **The exact finite covariance value.** -/
noncomputable def qkCovariance (D : QKSourceCharacterCovarianceData Ch) : ℂ :=
  (1 / (D.normalization : ℂ)) * ∑ ch : Ch, D.summand ch

/-- **Deterministic sector splitting.**  Along any decomposition predicate
(e.g. principal versus non-principal characters) the covariance splits exactly.
This is the routing identity, not an estimate. -/
theorem qkCovariance_sector_split (D : QKSourceCharacterCovarianceData Ch)
    (P : Ch → Prop) [DecidablePred P] :
    D.qkCovariance
      = (1 / (D.normalization : ℂ)) * (∑ ch ∈ Finset.univ.filter P, D.summand ch)
        + (1 / (D.normalization : ℂ)) * (∑ ch ∈ Finset.univ.filter (fun ch => ¬ P ch),
            D.summand ch) := by
  classical
  unfold qkCovariance
  rw [← mul_add, Finset.sum_filter_add_sum_filter_not]

/-- **Deterministic triangle inequality.**  No cancellation is claimed. -/
theorem qkCovariance_norm_le (D : QKSourceCharacterCovarianceData Ch) :
    ‖D.qkCovariance‖ ≤ (1 / D.normalization) * ∑ ch : Ch, ‖D.summand ch‖ := by
  unfold qkCovariance
  rw [norm_mul]
  have h1 : ‖(1 / (D.normalization : ℂ))‖ = 1 / D.normalization := by
    have hn : ‖(D.normalization : ℂ)‖ = D.normalization := by
      simp [abs_of_pos D.normalization_pos]
    rw [norm_div, norm_one, hn]
  rw [h1]
  have hpos : 0 ≤ 1 / D.normalization := div_nonneg zero_le_one (le_of_lt D.normalization_pos)
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hpos

/-- **Deterministic identity connecting the covariance to a moving-multiplier
sum**, under an explicit decomposition hypothesis identifying the per-character
summands with the terms of that sum.  The hypothesis is an input, never
supplied here. -/
theorem qkCovariance_eq_of_movingMultiplier_decomposition
    (D : QKSourceCharacterCovarianceData Ch) (T : Ch → ℂ)
    (hdecomp : ∀ ch : Ch, D.summand ch = T ch) :
    D.qkCovariance = (1 / (D.normalization : ℂ)) * ∑ ch : Ch, T ch := by
  unfold qkCovariance
  rw [Finset.sum_congr rfl fun ch _ => hdecomp ch]

end QKSourceCharacterCovarianceData

/-- **UNINHABITED ANALYTIC INTERFACE.**  The QK source-character covariance
bound.  Nothing in this bank constructs it. -/
structure QKSourceCharacterCovarianceBound {Ch : Type*} [Fintype Ch] [DecidableEq Ch]
    (D : QKSourceCharacterCovarianceData Ch) (target : ℝ) : Prop where
  /-- EXTERNAL ANALYTIC INPUT — never supplied here. -/
  covariance_le : ‖D.qkCovariance‖ ≤ target

/-- **Non-vacuity guard.**  The interface has content: a negative target is
impossible. -/
theorem qkSourceCharacterCovarianceBound_not_vacuous
    {Ch : Type*} [Fintype Ch] [DecidableEq Ch] (D : QKSourceCharacterCovarianceData Ch) :
    ¬ QKSourceCharacterCovarianceBound D (-1) := by
  intro h
  have := h.covariance_le
  have h0 : (0 : ℝ) ≤ ‖D.qkCovariance‖ := norm_nonneg _
  linarith

end Gate1B.SafeExtensions
