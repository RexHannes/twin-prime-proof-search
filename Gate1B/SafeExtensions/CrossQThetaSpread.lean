/-
# Gate 1B v13 — cross-`q` Θ-spread: finite mass inequalities and the
deterministic spread criterion

**Status: finite inequalities PROVED; the real source certificate is
UNINHABITED.**

The cross-`q` sector needs the Θ-source vector `A : Θ → ℂ` to be *spread*, i.e.
its `ℓ²` mass must be small relative to its `ℓ¹` mass.  Everything in this file
is deterministic finite algebra:

* `crossL1`, `crossL2` — the two masses;
* `crossL2_sq_le_maxFibre_mul_l1` — `‖A‖₂² ≤ F ‖A‖₁` when `‖A‖_∞ ≤ F`;
* `crossL1_le_states_mul_maxFibre` — `‖A‖₁ ≤ (#states) F`;
* `crossL2_le_crossL1` — the trivial comparison;
* `crossQ_spread_criterion` — the deterministic criterion: if `‖A‖_∞ ≤ F` and
  `F ≤ ρ² ‖A‖₁` then `‖A‖₂ ≤ ρ ‖A‖₁`.

The *actual* Θ-source of the cross-`q` sector is **not** shown to satisfy the
criterion: the corresponding data are packaged as the interfaces
`ProductMultiplicityCertificate` and `CrossQThetaSourceMassCertificate`, which
are never inhabited here.
-/
import Mathlib

namespace Gate1B.SafeExtensions

open Finset

variable {Θ : Type*} [Fintype Θ]

/-- The `ℓ¹` mass of a finite source vector. -/
noncomputable def crossL1 (A : Θ → ℂ) : ℝ := ∑ t : Θ, ‖A t‖

/-- The `ℓ²` mass of a finite source vector. -/
noncomputable def crossL2 (A : Θ → ℂ) : ℝ := Real.sqrt (∑ t : Θ, ‖A t‖ ^ 2)

theorem crossL1_nonneg (A : Θ → ℂ) : 0 ≤ crossL1 A :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem crossL2_nonneg (A : Θ → ℂ) : 0 ≤ crossL2 A := Real.sqrt_nonneg _

/-- **Fibre inequality**: a pointwise fibre bound `F` converts `ℓ²` mass into
`ℓ¹` mass. -/
theorem crossL2_sq_le_maxFibre_mul_l1 (A : Θ → ℂ) {F : ℝ}
    (hF : ∀ t : Θ, ‖A t‖ ≤ F) :
    crossL2 A ^ 2 ≤ F * crossL1 A := by
  have hsum0 : (0 : ℝ) ≤ ∑ t : Θ, ‖A t‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hsq : crossL2 A ^ 2 = ∑ t : Θ, ‖A t‖ ^ 2 := Real.sq_sqrt hsum0
  rw [hsq, crossL1, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have := hF t
  nlinarith [norm_nonneg (A t)]

/-- **Total-states inequality**: the `ℓ¹` mass is at most the number of states
times the maximal fibre. -/
theorem crossL1_le_states_mul_maxFibre (A : Θ → ℂ) {F : ℝ}
    (hF : ∀ t : Θ, ‖A t‖ ≤ F) :
    crossL1 A ≤ (Fintype.card Θ : ℝ) * F := by
  have h := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset Θ)) => hF t)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h
  exact h

/-- The `ℓ²` mass never exceeds the `ℓ¹` mass. -/
theorem crossL2_le_crossL1 (A : Θ → ℂ) : crossL2 A ≤ crossL1 A := by
  have hsum0 : (0 : ℝ) ≤ ∑ t : Θ, ‖A t‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [crossL2]
  refine (Real.sqrt_le_left (crossL1_nonneg A)).mpr ?_
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun t _ => norm_nonneg _

/-- **Deterministic spread criterion.**  A pointwise fibre bound `F` together
with the mass condition `F ≤ ρ² ‖A‖₁` gives `‖A‖₂ ≤ ρ ‖A‖₁`. -/
theorem crossQ_spread_criterion (A : Θ → ℂ) {F rho : ℝ} (hrho : 0 ≤ rho)
    (hF : ∀ t : Θ, ‖A t‖ ≤ F) (hmass : F ≤ rho ^ 2 * crossL1 A) :
    crossL2 A ≤ rho * crossL1 A := by
  have hsum0 : (0 : ℝ) ≤ ∑ t : Θ, ‖A t‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h1 : crossL2 A ^ 2 ≤ F * crossL1 A := crossL2_sq_le_maxFibre_mul_l1 A hF
  have hL1 : 0 ≤ crossL1 A := crossL1_nonneg A
  have h2 : F * crossL1 A ≤ (rho * crossL1 A) ^ 2 := by nlinarith
  have hnn : 0 ≤ rho * crossL1 A := mul_nonneg hrho hL1
  rw [crossL2]
  refine (Real.sqrt_le_left hnn).mpr ?_
  have hsq : ∑ t : Θ, ‖A t‖ ^ 2 = crossL2 A ^ 2 := (Real.sq_sqrt hsum0).symm
  rw [hsq]
  exact le_trans h1 h2

/-- **INTERFACE (never inhabited here).**  A multiplicity certificate for the
product Θ-source: the pointwise fibre bound of the actual cross-`q` source. -/
structure ProductMultiplicityCertificate (A : Θ → ℂ) (F : ℝ) : Prop where
  /-- EXTERNAL SOURCE INPUT — never supplied here. -/
  fibre_le : ∀ t : Θ, ‖A t‖ ≤ F

/-- **INTERFACE (never inhabited here).**  The cross-`q` source-mass
certificate: the actual Θ-source is `ρ`-spread. -/
structure CrossQThetaSourceMassCertificate (A : Θ → ℂ) (rho : ℝ) : Prop where
  /-- EXTERNAL SOURCE INPUT — never supplied here. -/
  spread : crossL2 A ≤ rho * crossL1 A

/-- The criterion is a genuine bridge: multiplicity data plus the mass
condition produce the spread certificate. -/
theorem crossQThetaSourceMassCertificate_of_multiplicity (A : Θ → ℂ) {F rho : ℝ}
    (hrho : 0 ≤ rho) (hcert : ProductMultiplicityCertificate A F)
    (hmass : F ≤ rho ^ 2 * crossL1 A) :
    CrossQThetaSourceMassCertificate A rho :=
  ⟨crossQ_spread_criterion A hrho hcert.fibre_le hmass⟩

/-- **Non-vacuity guard.**  A negative spread constant is impossible for a
nonzero source. -/
theorem crossQThetaSourceMassCertificate_not_vacuous (A : Θ → ℂ) (t : Θ)
    (ht : A t ≠ 0) : ¬ CrossQThetaSourceMassCertificate A (-1) := by
  intro h
  have hspread := h.spread
  have hL1 : 0 ≤ crossL1 A := crossL1_nonneg A
  have hpos : 0 < crossL2 A := by
    have hsum : 0 < ∑ s : Θ, ‖A s‖ ^ 2 := by
      refine Finset.sum_pos' (fun s _ => by positivity) ⟨t, Finset.mem_univ t, ?_⟩
      have : 0 < ‖A t‖ := norm_pos_iff.mpr ht
      positivity
    exact Real.sqrt_pos.mpr hsum
  nlinarith

end Gate1B.SafeExtensions
