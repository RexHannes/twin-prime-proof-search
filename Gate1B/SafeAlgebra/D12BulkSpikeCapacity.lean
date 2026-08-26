/-
# Gate 1B v8.3 — D₁₂ bulk/spike capacity bookkeeping

**Status: CAPACITY_ONLY.**

Rational exponent bookkeeping only — no real asymptotic function is encoded and
**no analytic D₁₂ statement is proved or refuted here**.

With the supplied exponent scale (all exponents in the variable `Q`):

* `#D` exponent `2`;
* `‖T‖₂` exponent `2`;
* `‖T‖_∞` exponent `11/6`;

one gets

* RMS exponent `2 - 2/2 = 1`;
* sup-over-RMS gap `11/6 - 1 = 5/6`;
* generic bulk/spike square-root loss `(5/6)/2 = 5/12`.

`bulkSpike_balance_exponent` records the generic optimisation fact behind the
halving: balancing the two branches of the bulk/spike split can never beat half
the gap.

Comment (deliberately not a theorem): generic bulk/spike plus a fixed-`D`
external estimate does not improve the pure `D`-ℓ² route at this exponent
scale.  This is a capacity statement about the *method*, not a proof that the
D₁₂ analytic moment fails; the moving-`D` source-specific moment remains OPEN.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- Exponent of `#D` in the variable `Q`. -/
def d12CardExponent : ℚ := 2

/-- Exponent of `‖T‖₂`. -/
def d12T2Exponent : ℚ := 2

/-- Exponent of `‖T‖_∞`. -/
def d12TinfExponent : ℚ := 11 / 6

/-- Exponent of the root-mean-square size of `T`. -/
def d12RmsExponent : ℚ := d12T2Exponent - d12CardExponent / 2

/-- The sup-over-RMS gap. -/
def d12SupOverRmsGap : ℚ := d12TinfExponent - d12RmsExponent

/-- The generic bulk/spike square-root loss. -/
def d12BulkSpikeLoss : ℚ := d12SupOverRmsGap / 2

/-- RMS exponent is `1`. -/
theorem d12_rms_exponent : d12RmsExponent = 1 := by
  unfold d12RmsExponent d12T2Exponent d12CardExponent; norm_num

/-- Sup-over-RMS exponent gap is `5/6`. -/
theorem d12_sup_over_rms_exponent : d12SupOverRmsGap = 5 / 6 := by
  unfold d12SupOverRmsGap d12TinfExponent d12RmsExponent d12T2Exponent d12CardExponent
  norm_num

/-- Generic bulk/spike loss exponent is `5/12`. -/
theorem d12_bulkSpike_loss_exponent : d12BulkSpikeLoss = 5 / 12 := by
  unfold d12BulkSpikeLoss d12SupOverRmsGap d12TinfExponent d12RmsExponent d12T2Exponent
    d12CardExponent
  norm_num

/-- **Balancing fact.**  Whatever threshold exponent `lam` is chosen, the worse
of the two bulk/spike branches is at least half the gap: the square-root loss
cannot be avoided by tuning the threshold. -/
theorem bulkSpike_balance_exponent (gap lam : ℚ) : gap / 2 ≤ max lam (gap - lam) := by
  rcases le_total lam (gap / 2) with h | h
  · have : gap / 2 ≤ gap - lam := by linarith
    exact le_max_of_le_right this
  · exact le_max_of_le_left h

/-- The balance is attained exactly at the midpoint. -/
theorem bulkSpike_balance_attained (gap : ℚ) : max (gap / 2) (gap - gap / 2) = gap / 2 := by
  have : gap - gap / 2 = gap / 2 := by ring
  rw [this, max_self]

end Gate1B.SafeAlgebra
