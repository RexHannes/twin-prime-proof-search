/-
NANC V5 CONTROLLING LAYER — FORD–MAYNARD METADATA, P_ε GEOMETRY, THEOREM 4.16.

Contents.

* Bibliographic metadata for the source paper, including the **strict** form of
  the published Theorem-2.7(b) inequality `ν > 0.1663` (not `ν ≥ 0.1663`), with
  a Lean separation showing that the strict and non-strict hypotheses are
  genuinely different predicates.
* The exact rational threshold facts, re-exported from V4 (never re-proved):
  `1/6 > 1663/10000` and `1/6 - 1663/10000 = 11/30000`.
* The `P_ε` parameter geometry `γ = 1/2 - ε`, `θ = ε`, `ν = 1/6 - 2ε`, with the
  two rational facts `θ + ν = 1/6 - ε` and, for `ε > 0`, `γ > θ + ν`.
* `FMTheorem416` — an UNINHABITED external interface for the vanishing statement
  of the source's Theorem 4.16 — and the deterministic compiler
  `FMTheorem416 → ordinary P_ε coefficient vanishes`.
* `FMDependencyAudit` — provenance metadata recording the *displayed* dependency
  chain only.  It deliberately cannot express "there is no indirect use anywhere
  in the paper".

NOTHING analytic is inhabited here.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.Status

namespace NANC.V5.Controlling

open NANC.V4

/-! ### Source metadata -/

/-- Bibliographic record of the source paper, at the controlling-layer status. -/
def fmSourceEntry : ControlEntry where
  name := "Ford–Maynard, On the theory of prime-producing sieves, arXiv:2407.14368"
  status := ControlStatus.externallyPublished
  notes :=
    "Public 107-page version.  Cited only.  No part of the analysis is formalized. " ++
    "Published Theorem 2.7(b) uses the STRICT inequality nu > 0.1663."

theorem fmSourceEntry_not_leanEvidence :
    ControlEntry.IsLeanEvidence fmSourceEntry = false := rfl

/-- The published threshold as the exact rational `1663/10000` (the V4 constant). -/
def fmThresholdQ : ℚ := fmThreshold

theorem fmThresholdQ_eq : fmThresholdQ = 1663 / 10000 := rfl

/-- Re-export of the V4 exact comparison `1/6 > 1663/10000`. -/
theorem control_one_sixth_gt_threshold : fmThresholdQ < nu0 := one_sixth_gt_fm_threshold

/-- Re-export of the V4 exact margin `1/6 - 1663/10000 = 11/30000`. -/
theorem control_threshold_margin : nu0 - fmThresholdQ = 11 / 30000 :=
  one_sixth_threshold_margin

/-! ### Strict vs non-strict threshold convention -/

/-- The **strict** hypothesis of the published Theorem 2.7(b): `ν > 0.1663`. -/
def ThresholdHypStrict (nu : ℚ) : Prop := fmThresholdQ < nu

/-- The **non-strict** variant `ν ≥ 0.1663`, recorded only so that it can be kept
apart from the published statement. -/
def ThresholdHypNonStrict (nu : ℚ) : Prop := fmThresholdQ ≤ nu

/-- The strict hypothesis implies the non-strict one. -/
theorem strict_imp_nonStrict {nu : ℚ} (h : ThresholdHypStrict nu) : ThresholdHypNonStrict nu :=
  le_of_lt h

/-- **Firewall.**  The two conventions are genuinely different: at `ν = 0.1663`
the non-strict hypothesis holds while the published strict one fails. -/
theorem nonStrict_not_strict :
    ∃ nu : ℚ, ThresholdHypNonStrict nu ∧ ¬ ThresholdHypStrict nu :=
  ⟨fmThresholdQ, le_refl _, lt_irrefl _⟩

/-- `1/6` satisfies the published strict hypothesis. -/
theorem nu0_thresholdHypStrict : ThresholdHypStrict nu0 := control_one_sixth_gt_threshold

/-! ### The `P_ε` parameter geometry -/

/-- The `P_ε` parameter triple `(γ, θ, ν) = (1/2 - ε, ε, 1/6 - 2ε)`.  This is the
V4 `shrinkParams`, named for the controlling layer. -/
def PEpsilon (eps : ℚ) : ℚ × ℚ × ℚ := shrinkParams eps

@[simp] theorem PEpsilon_gamma (eps : ℚ) : (PEpsilon eps).1 = 1 / 2 - eps := rfl
@[simp] theorem PEpsilon_theta (eps : ℚ) : (PEpsilon eps).2.1 = eps := rfl
@[simp] theorem PEpsilon_nu (eps : ℚ) : (PEpsilon eps).2.2 = 1 / 6 - 2 * eps := rfl

/-- `θ(ε) + ν(ε) = 1/6 - ε` (re-export of the V4 identity). -/
theorem PEpsilon_theta_add_nu (eps : ℚ) :
    (PEpsilon eps).2.1 + (PEpsilon eps).2.2 = 1 / 6 - eps := shrunk_theta_add_nu eps

/-- The target exponent lies strictly **above** the Type-II window:
`γ(ε) > θ(ε) + ν(ε)` for every `ε`.  Exact rational arithmetic only. -/
theorem PEpsilon_gamma_gt_theta_add_nu (eps : ℚ) :
    (PEpsilon eps).2.1 + (PEpsilon eps).2.2 < (PEpsilon eps).1 := by
  rw [PEpsilon_theta_add_nu]
  simp only [PEpsilon_gamma]
  linarith

/-- For `ε > 0` the target exponent is below `1/2`. -/
theorem PEpsilon_gamma_lt_half {eps : ℚ} (h : 0 < eps) : (PEpsilon eps).1 < 1 / 2 := by
  simp only [PEpsilon_gamma]; linarith

/-- On the admissible ε-range the shrunk exponent still satisfies the published
strict threshold hypothesis (re-export of the V4 arithmetic). -/
theorem PEpsilon_nu_thresholdHypStrict {eps : ℚ} (h0 : 0 < eps) (h1 : eps < 11 / 60000) :
    ThresholdHypStrict (PEpsilon eps).2.2 :=
  shrunk_nu_gt_threshold_of_eps_small h0 h1

/-! ### Theorem 4.16: external interface and the deterministic compiler -/

/-- The Ford–Maynard "support window" `[θ, θ+ν]` of a parameter triple. -/
def InSupportWindow (gamma theta nu : ℚ) : Prop := theta ≤ gamma ∧ gamma ≤ theta + nu

/-- **External interface (UNINHABITED): Ford–Maynard Theorem 4.16.**

For the ordinary sequence class, a target exponent `γ < 1/2` lying outside the
window `[θ, θ+ν]` forces the sieve-conversion coefficient to vanish. -/
def FMTheorem416 (Cminus : SieveCoefficient) : Prop :=
  ∀ gamma theta nu : ℚ, gamma < 1 / 2 → ¬ InSupportWindow gamma theta nu →
    Cminus gamma theta nu = 0

/-- The conclusion the `P_ε` death certificate needs: the ordinary coefficient at
the `P_ε` triple vanishes. -/
def OrdinaryPEpsilonZero (Cminus : SieveCoefficient) (eps : ℚ) : Prop :=
  Cminus (PEpsilon eps).1 (PEpsilon eps).2.1 (PEpsilon eps).2.2 = 0

/-- **Deterministic compiler (the only Lean content of the death certificate).**
Given the external Theorem-4.16 interface, the ordinary `P_ε` coefficient
vanishes for every `ε > 0`.  All analytic content stays in the hypothesis. -/
theorem fmTheorem416_imp_ordinary_PEpsilon_zero {Cminus : SieveCoefficient} {eps : ℚ}
    (h416 : FMTheorem416 Cminus) (h : 0 < eps) : OrdinaryPEpsilonZero Cminus eps := by
  refine h416 _ _ _ (PEpsilon_gamma_lt_half h) ?_
  rintro ⟨-, hle⟩
  exact absurd hle (not_le.mpr (PEpsilon_gamma_gt_theta_add_nu eps))

/-- Status entry for Theorem 4.16: external, uninhabited. -/
def theorem416Entry : ControlEntry where
  name := "Ford–Maynard Theorem 4.16 (vanishing outside the support window)"
  status := ControlStatus.uninhabitedInterface
  notes := "Defined as a Prop; never inhabited.  Only the conditional compiler is Lean-proved."

theorem theorem416Entry_not_leanEvidence :
    ControlEntry.IsLeanEvidence theorem416Entry = false := rfl

/-! ### Ordinary vs bounded sequence class -/

/-- Which Ford–Maynard sequence class a statement belongs to. -/
inductive SequenceClass where
  /-- The ordinary class: conditions (b.1), (b.2), Type I, Type II, condition (w). -/
  | ordinary
  /-- The bounded class: the ordinary requirements *plus* the external condition (4.1). -/
  | bounded
  deriving DecidableEq, Repr

/-- The requirements attached to each class, as data. -/
def classRequirements : SequenceClass → List String
  | SequenceClass.ordinary => ["b.1", "b.2", "Type I", "Type II", "condition (w)"]
  | SequenceClass.bounded =>
      ["b.1", "b.2", "Type I", "Type II", "condition (w)", "condition (4.1)"]

/-- **Firewall.**  The two classes are distinct, and the bounded class carries a
strictly larger requirement list.  Consequently `C⁻` and `C⁻_bd` are never
identified in this bank. -/
theorem ordinary_ne_bounded : SequenceClass.ordinary ≠ SequenceClass.bounded := by decide

theorem bounded_requires_more :
    "condition (4.1)" ∈ classRequirements SequenceClass.bounded ∧
    "condition (4.1)" ∉ classRequirements SequenceClass.ordinary := by
  constructor <;> decide

/-! ### Displayed dependency audit (metadata only) -/

/-- Provenance metadata recording the **displayed** dependency chain of the source
argument.  Each field is a Prop asserted by an external audit; the record is data,
never a Lean proof about the paper.

Scope guard: there is deliberately no field expressing "there is no indirect use
anywhere in the paper" — such a statement is outside the audit's scope. -/
structure FMDependencyAudit where
  /-- Proposition 7.19 uses condition (w), Type I and Type II. -/
  prop719UsesWTypeITypeII : Prop
  /-- Lemma 7.20 uses comparison condition (b.2). -/
  lemma720UsesB2 : Prop
  /-- Lemma 7.21 uses Type I. -/
  lemma721UsesTypeI : Prop
  /-- The displayed proof of Theorem 8.2 uses the pointwise bounded-class
  condition at the final `N₂` estimate. -/
  theorem82PointwiseBoundedAtN2 : Prop
  /-- Notes recording exactly what was inspected. -/
  notes : String
  /-- The status of the audit record. -/
  status : ControlStatus

/-- The current audit record.  Its status is `opusAuditedAnalyticPass`: an external
audit verdict, never a Lean proof. -/
def fmDependencyAudit (p719 l720 l721 t82 : Prop) : FMDependencyAudit where
  prop719UsesWTypeITypeII := p719
  lemma720UsesB2 := l720
  lemma721UsesTypeI := l721
  theorem82PointwiseBoundedAtN2 := t82
  notes :=
    "Displayed dependency chain only: Prop. 7.19 uses (w),(I),(II); Lemma 7.20 uses " ++
    "comparison (b.2); Lemma 7.21 uses Type I; the displayed Theorem-8.2 proof uses the " ++
    "pointwise bounded-class condition at the final N2 estimate.  No claim is made about " ++
    "indirect uses elsewhere in the paper."
  status := ControlStatus.opusAuditedAnalyticPass

/-- The audit record is never Lean evidence. -/
theorem fmDependencyAudit_not_leanEvidence (p q r s : Prop) :
    ControlStatus.IsLeanEvidence (fmDependencyAudit p q r s).status = false := rfl

/-- **Scope guard.**  Recording the displayed uses is compatible with further,
indirect uses: an audit record can assert the displayed chain while an additional
indirect use also holds. -/
theorem dependencyAudit_does_not_exclude_indirect_uses :
    ∃ (A : FMDependencyAudit) (indirectUse : Prop),
      A.theorem82PointwiseBoundedAtN2 ∧ indirectUse :=
  ⟨fmDependencyAudit True True True True, True, trivial, trivial⟩

end NANC.V5.Controlling
