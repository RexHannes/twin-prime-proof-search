import RequestProject.CurrentProgramme.AnalyticInterfaces
import RequestProject.CurrentProgramme.EndpointBilinear
import RequestProject.CurrentProgramme.SmoothLocalisation
import RequestProject.NANC.Gate1BDet2.Gate1BInterfaces

/-!
# Phase A10 / F4 · current Gate-1B endpoint conditional compiler

**Non-circular.**  The input package below does **not** contain its own target
proposition as a field, and it does not contain `Gate1BClosed`.

## What the compiler does

Given

1. a localized fivefold discrepancy bound,
2. an endpoint diagonal bound,
3. an endpoint off-diagonal bound,
4. a literal β/source dictionary,
5. a physical comparison / local-density match,

together with the **source decomposition** of the endpoint quantity into these
pieces (itself an exposed hypothesis, not a theorem), it produces the
small/fixed-polylog-`k` endpoint estimate.

Items 1–3 and 5 are `UNINHABITED` interfaces; item 4 is `SOURCE_OPEN`.  The
package is therefore **not** inhabited, and

  `GATE1B : OPEN`

remains the status.  `Gate1BClosed` is *not* proved: the compiler stops at the
endpoint estimate, and the remaining Gate-1B leaves (`PURE5`, lower defect
orders, near-primitive, `r>1`, transition strip, proper-divisor recursion,
`QK56` exhaustiveness, shifted `TT*`, source reassembly) are separate open
obligations recorded in `Gate1BCurrentStatus.lean`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Gate1BEndpoint

open Interfaces

/-- The target: the fixed-polylog-`k` endpoint estimate. -/
def EndpointEstimate (endpointQuantity level : ℝ) : Prop :=
  |endpointQuantity| ≤ level

/-- **A10 input package.**  Five genuinely open leaves; the target is *not* a
field. -/
structure EndpointInputs where
  /-- (1) localized fivefold discrepancy — UNINHABITED. -/
  localizedFivefold : LocalizedFivefoldDiscrepancyInput
  /-- (2) endpoint `u`-diagonal — UNINHABITED (analytic side). -/
  diagonal : RankOneEndpointUDiagonalInput
  /-- (3) endpoint `u`-offdiagonal — UNINHABITED, first analytic open. -/
  offdiagonal : RankOneEndpointUOffdiagInput
  /-- (4) literal β source dictionary — SOURCE_OPEN. -/
  betaDictionary : EndpointBetaSourceDictionary
  /-- (5) physical comparison / local-density match — SOURCE_OPEN. -/
  comparison : Pure5ComparisonMainTermPin

/-- **A10, the conditional compiler.**

`hsplit` is the *source decomposition* of the endpoint quantity: it is an
exposed antecedent, not something the compiler proves.  Given it, and the three
supplied bounds, the endpoint estimate follows by the triangle inequality.

Note that the comparison pin enters through `hsplit` (it identifies the main
term that has been subtracted); by `Interfaces.residue_discrepancy_ne_physical_without_pin`
this identification is not automatic. -/
theorem endpointEstimate_of_inputs (I : EndpointInputs)
    {endpointQuantity : ℝ} {smoothCost : ℝ} {q a : ℕ} {F : ℕ → ℝ} {S : ℝ}
    (hS : ∀ i < I.localizedFivefold.n, |F i| ≤ S)
    (hn : 0 < I.localizedFivefold.n)
    (hcost : smoothCost = S + SmoothLocalisation.totalVariation F I.localizedFivefold.n)
    (hsplit : endpointQuantity =
      SmoothLocalisation.wDiscrepancy F (I.localizedFivefold.E q a)
          I.localizedFivefold.n
        + I.diagonal.diagEnergy + I.offdiagonal.offdiagEnergy
        + (I.comparison.physicalMain - I.comparison.residueMain)) :
    EndpointEstimate endpointQuantity
      (smoothCost * I.localizedFivefold.T q + I.diagonal.level
        + I.offdiagonal.T_off) := by
  unfold EndpointEstimate
  have hloc : |SmoothLocalisation.wDiscrepancy F (I.localizedFivefold.E q a)
      I.localizedFivefold.n| ≤ smoothCost * I.localizedFivefold.T q := by
    rw [hcost]
    exact SmoothLocalisation.wDiscrepancy_le F (I.localizedFivefold.E q a)
      (I.localizedFivefold.base q a) I.localizedFivefold.n
      (I.localizedFivefold.bound q a) hS hn
  have hcomp : I.comparison.physicalMain - I.comparison.residueMain = 0 := by
    rw [I.comparison.identified]; ring
  rw [hsplit, hcomp, add_zero]
  have h1 := abs_add_le
    (SmoothLocalisation.wDiscrepancy F (I.localizedFivefold.E q a)
      I.localizedFivefold.n + I.diagonal.diagEnergy) I.offdiagonal.offdiagEnergy
  have h2 := abs_add_le
    (SmoothLocalisation.wDiscrepancy F (I.localizedFivefold.E q a)
      I.localizedFivefold.n) I.diagonal.diagEnergy
  have h3 := I.diagonal.bound
  have h4 := I.offdiagonal.bound
  linarith

/-- **A10 counterguard / toy model.**  The endpoint estimate is *not*
automatic: there are data violating it. -/
theorem endpointEstimate_not_automatic : ¬ EndpointEstimate 2 1 := by
  unfold EndpointEstimate; norm_num

/-- **Non-circularity witness.**  `EndpointInputs` does not mention
`EndpointEstimate`: the target is a two-argument predicate on reals that can
fail while every field type is inhabited-in-principle.  Recorded concretely:
supplying inputs whose levels are small does not make an arbitrary quantity
small. -/
theorem compiler_is_not_circular :
    ∀ level : ℝ, level < 2 → ¬ EndpointEstimate 2 level := by
  intro level h
  unfold EndpointEstimate
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

/-! ## Gate-1B remains OPEN -/

/-- **Firewall.**  This module proves no instance of `Gate1BClosed`, and the
endpoint estimate does not entail it: `Gate1BClosed` additionally requires the
Gate-0 uncovered mass to vanish, which is a separate open obligation. -/
theorem endpointEstimate_does_not_give_gate1BClosed :
    EndpointEstimate 0 1 ∧ ¬ Gate1BDet2.Gate1BClosed 0 1 1 := by
  refine ⟨by unfold EndpointEstimate; norm_num, ?_⟩
  rintro ⟨-, h⟩
  norm_num at h

end Gate1BEndpoint
end CurrentProgramme
end TwinPrimeProject
