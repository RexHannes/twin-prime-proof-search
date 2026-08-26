/-
NANC V4 — external Ford–Maynard interfaces.

NOTHING IN THIS FILE IS INHABITED.

The 107-page Ford–Maynard analysis is *not* formalized.  What is formalized is
the *shape of the dependency*: each published external result is a Prop
parameterized by the data it speaks about, so that any downstream use is forced
to carry it as an explicit hypothesis.

PERMANENT FIREWALL:
    ordinary_positive (C⁻)  ≠  bounded_positive (C⁻_bd)
-/
import Mathlib
import RequestProject.NANC.V4.Parameters
import RequestProject.NANC.V4.Status

namespace NANC.V4

/-- Abstract type of a sieve-conversion coefficient `C⁻(γ, θ, ν)`.  The concrete
Ford–Maynard construction is *not* formalized; it is supplied as data. -/
abbrev SieveCoefficient := ℚ → ℚ → ℚ → ℝ

/-- **External interface** (Ford–Maynard Theorem 2.7(b), central-width form).

`ν > 1663/10000  →  C⁻(γ, θ, ν) > 0` for the given `C⁻` at the central parameters.

UNINHABITED. -/
def FMPositiveCentralWidth (Cminus : SieveCoefficient) (gamma theta : ℚ) : Prop :=
  ∀ nu : ℚ, fmThreshold < nu → nu ≤ 1 - theta → 0 < Cminus gamma theta nu

/-- **External interface** (bounded-sequence variant).  The *bounded* coefficient
`C⁻_bd` is a different object; this Prop is deliberately kept separate from
`FMPositiveCentralWidth`.  UNINHABITED. -/
def FMBoundedPositiveNearCentral (CminusBd : SieveCoefficient) (gamma theta : ℚ)
    (epsBound : ℚ) : Prop :=
  ∀ eps nu : ℚ, 0 < eps → eps < epsBound → fmThreshold < nu → 0 < CminusBd (gamma - eps) theta nu

/-- **Firewall (genuine separation).**  Positivity of the bounded coefficient
`C⁻_bd` does not entail positivity of the ordinary coefficient `C⁻`: there are
data for which the bounded statement holds and the ordinary one fails.  Hence the
two must never be silently identified. -/
theorem ordinary_positive_ne_bounded_positive :
    ∃ (Cminus CminusBd : SieveCoefficient) (gamma theta epsBound : ℚ),
      FMBoundedPositiveNearCentral CminusBd gamma theta epsBound ∧
      ¬ FMPositiveCentralWidth Cminus gamma theta := by
  refine ⟨fun _ _ _ => -1, fun _ _ _ => 1, gamma0, theta0, 1, ?_, ?_⟩
  · intro eps nu _ _ _; norm_num
  · intro h
    have := h nu0 one_sixth_gt_fm_threshold (by norm_num [nu0, theta0])
    norm_num at this

/-- **External interface**: Ford–Maynard comparison regularity condition (b.1).
UNINHABITED. -/
structure FMComparisonRegularityData where
  /-- Condition (b.1) of the comparison framework. -/
  b1 : Prop
  /-- Condition (b.2) of the comparison framework. -/
  b2 : Prop
  /-- The growth condition on the comparison sequence. -/
  growth : Prop

/-- Conjunction of the three comparison conditions.  UNINHABITED: no inhabitant of
`FMComparisonB1`, `FMComparisonB2` or `FMGrowthCondition` is produced anywhere in
this bank. -/
def FMComparisonB1 (D : FMComparisonRegularityData) : Prop := D.b1

/-- Condition (b.2) as a Prop.  UNINHABITED. -/
def FMComparisonB2 (D : FMComparisonRegularityData) : Prop := D.b2

/-- Growth condition as a Prop.  UNINHABITED. -/
def FMGrowthCondition (D : FMComparisonRegularityData) : Prop := D.growth

/-- The packaged comparison-regularity hypothesis. -/
def FMComparisonRegularity (D : FMComparisonRegularityData) : Prop :=
  FMComparisonB1 D ∧ FMComparisonB2 D ∧ FMGrowthCondition D

theorem FMComparisonRegularity_b1 {D : FMComparisonRegularityData}
    (h : FMComparisonRegularity D) : FMComparisonB1 D := h.1

theorem FMComparisonRegularity_b2 {D : FMComparisonRegularityData}
    (h : FMComparisonRegularity D) : FMComparisonB2 D := h.2.1

theorem FMComparisonRegularity_growth {D : FMComparisonRegularityData}
    (h : FMComparisonRegularity D) : FMGrowthCondition D := h.2.2

/-- Status labels for the external Ford–Maynard layer. -/
def statusFMTheorem27 : BankStatus := BankStatus.externalAnalyticInput

/-- Status label for `C⁻` positivity. -/
def statusOrdinaryCminusPositivity : BankStatus := BankStatus.uninhabitedInterface

/-- Status label for `C⁻_bd` positivity. -/
def statusBoundedCminusPositivity : BankStatus := BankStatus.uninhabitedInterface

theorem statusFMTheorem27_not_proofBearing :
    BankStatus.IsProofBearing statusFMTheorem27 = false := by decide

end NANC.V4
