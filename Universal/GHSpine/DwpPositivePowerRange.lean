/-
# Universal / GHSpine — `DwpPositivePowerRange` (supersedes the fixed-`1/3` range)

**Status of this module: KERNEL_PROVED exponent algebra.  The new range pin is
deliberately left UNINHABITED, exactly as the superseded one was.**

The earlier interface `Universal.D0WP.HardP3PhysicalRange` hard-coded the two
lower bounds

```
D ≥ X^{1/3-ε},   W ≥ X^{1/3-ε},   Q = D W ≥ X^{2/3-ε},   r ≤ X^{1/2+ε}.
```

That fixed `1/3` is **superseded as controlling** by the positive-power range
`DwpPositivePowerRange`, in which the two lower exponents are free positive
parameters `δ_D, δ_W > 0`.  Nothing in the historical module is edited: the old
structure, its pin and its two exponent lemmas keep their statements and their
`SOURCE_PIN_OPEN` status.

Kernel content of this module:

* `dwp_Q_lower`         — `Q ≥ X^{δ_D + δ_W}` (derived, not assumed);
* `dwp_one_div_D_le`    — `1/D ≤ X^{-δ_D}`;
* `dwp_r_div_Q_le`      — `r/Q ≤ X^{1/2 + ε - (δ_D + δ_W)}`;
* `dwp_r_div_Q_power_saving` — the same bound is a genuine negative power
  exactly when `δ_D + δ_W > 1/2 + ε`;
* `hardP3_to_dwpPositivePower` — the old fixed-`1/3` range is a *special case*
  of the new one (so no banked consequence is lost);
* `dwpPositivePowerRange_strictly_more_general` — a datum satisfying the new
  range and **failing** the old one (so the supersession is strict);
* `DwpPositivePowerRangePin` — the new source pin, UNINHABITED here, together
  with `dwpPositivePowerRangePin_not_automatic`.
-/
import Mathlib
import Universal.D0WP.SourcePins

namespace Universal.GHSpine

open Universal.D0WP

/-- The `d0 · wp` **positive-power** physical range: both dyadic scales carry a
fixed positive power of `X`, with the exponents free rather than pinned to
`1/3`, and the modulus stays below `X^{1/2+ε}`. -/
structure DwpPositivePowerRange (X eps deltaD deltaW : ℝ) (S : D0WPSource) : Prop where
  /-- The size parameter is large. -/
  X_gt_one : 1 < X
  /-- The slack is nonnegative. -/
  eps_nonneg : 0 ≤ eps
  /-- The `d0`-side exponent is a genuine positive power. -/
  deltaD_pos : 0 < deltaD
  /-- The `wp`-side exponent is a genuine positive power. -/
  deltaW_pos : 0 < deltaW
  /-- `D ≥ X^{δ_D}`. -/
  D_lower : S.D ≥ X ^ deltaD
  /-- `W ≥ X^{δ_W}`. -/
  W_lower : S.W ≥ X ^ deltaW
  /-- `D W = Q`. -/
  DW_eq_Q : S.D * S.W = S.Q
  /-- `r ≤ X^{1/2+ε}`. -/
  r_upper : (S.r : ℝ) ≤ X ^ ((1:ℝ)/2 + eps)

namespace DwpPositivePowerRange

variable {X eps deltaD deltaW : ℝ} {S : D0WPSource}

theorem X_pos (h : DwpPositivePowerRange X eps deltaD deltaW S) : (0:ℝ) < X :=
  lt_trans zero_lt_one h.X_gt_one

theorem D_pos (h : DwpPositivePowerRange X eps deltaD deltaW S) : 0 < S.D :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos h.X_pos _) h.D_lower

theorem W_pos (h : DwpPositivePowerRange X eps deltaD deltaW S) : 0 < S.W :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos h.X_pos _) h.W_lower

end DwpPositivePowerRange

/-- **Derived, not assumed:** the total scale satisfies `Q ≥ X^{δ_D + δ_W}`. -/
theorem dwp_Q_lower {X eps deltaD deltaW : ℝ} {S : D0WPSource}
    (h : DwpPositivePowerRange X eps deltaD deltaW S) : S.Q ≥ X ^ (deltaD + deltaW) := by
  have hX0 : (0:ℝ) < X := h.X_pos
  have hmul : X ^ deltaD * X ^ deltaW ≤ S.D * S.W :=
    mul_le_mul h.D_lower h.W_lower (le_of_lt (Real.rpow_pos_of_pos hX0 _))
      (le_of_lt h.D_pos)
  calc X ^ (deltaD + deltaW) = X ^ deltaD * X ^ deltaW := Real.rpow_add hX0 _ _
    _ ≤ S.D * S.W := hmul
    _ = S.Q := h.DW_eq_Q

/-- Exponent consequence used by the large-`rSharp` lane: `1/D ≤ X^{-δ_D}`. -/
theorem dwp_one_div_D_le {X eps deltaD deltaW : ℝ} {S : D0WPSource}
    (h : DwpPositivePowerRange X eps deltaD deltaW S) : 1 / S.D ≤ X ^ (-deltaD) := by
  have hX0 : (0:ℝ) < X := h.X_pos
  have hpos : (0:ℝ) < X ^ deltaD := Real.rpow_pos_of_pos hX0 _
  calc 1 / S.D ≤ 1 / X ^ deltaD := one_div_le_one_div_of_le hpos h.D_lower
    _ = X ^ (-deltaD) := by
        rw [Real.rpow_neg (le_of_lt hX0)]
        simp

/-- Exponent consequence used by the large-`rSharp` lane:
`r/Q ≤ X^{1/2 + ε - (δ_D + δ_W)}`. -/
theorem dwp_r_div_Q_le {X eps deltaD deltaW : ℝ} {S : D0WPSource}
    (h : DwpPositivePowerRange X eps deltaD deltaW S) :
    (S.r : ℝ) / S.Q ≤ X ^ ((1:ℝ)/2 + eps - (deltaD + deltaW)) := by
  have hX0 : (0:ℝ) < X := h.X_pos
  have hQlow : S.Q ≥ X ^ (deltaD + deltaW) := dwp_Q_lower h
  have hQpos : (0:ℝ) < X ^ (deltaD + deltaW) := Real.rpow_pos_of_pos hX0 _
  have hstep : (S.r : ℝ) / S.Q ≤ X ^ ((1:ℝ)/2 + eps) / X ^ (deltaD + deltaW) :=
    div_le_div₀ (le_of_lt (Real.rpow_pos_of_pos hX0 _)) h.r_upper hQpos hQlow
  calc (S.r : ℝ) / S.Q ≤ X ^ ((1:ℝ)/2 + eps) / X ^ (deltaD + deltaW) := hstep
    _ = X ^ ((1:ℝ)/2 + eps - (deltaD + deltaW)) := (Real.rpow_sub hX0 _ _).symm

/-- **Power saving criterion.**  The conductor ratio is bounded by a *negative*
power of `X` exactly when the two positive powers beat the modulus range. -/
theorem dwp_r_div_Q_power_saving {X eps deltaD deltaW : ℝ} {S : D0WPSource}
    (h : DwpPositivePowerRange X eps deltaD deltaW S)
    (hgain : (1:ℝ)/2 + eps < deltaD + deltaW) :
    ∃ gamma : ℝ, 0 < gamma ∧ (S.r : ℝ) / S.Q ≤ X ^ (-gamma) := by
  refine ⟨deltaD + deltaW - ((1:ℝ)/2 + eps), by linarith, ?_⟩
  have hle := dwp_r_div_Q_le h
  have hrw : -(deltaD + deltaW - ((1:ℝ)/2 + eps)) = (1:ℝ)/2 + eps - (deltaD + deltaW) := by
    ring
  rwa [hrw]

/-- **No banked consequence is lost.**  The superseded fixed-`1/3` range is the
special case `δ_D = δ_W = 1/3 - ε` of the positive-power range (for `ε < 1/3`,
which is the only regime in which the old bounds were genuine positive
powers). -/
theorem hardP3_to_dwpPositivePower {X eps : ℝ} {S : D0WPSource}
    (h : HardP3PhysicalRange X eps S) (heps : eps < 1/3) :
    DwpPositivePowerRange X eps ((1:ℝ)/3 - eps) ((1:ℝ)/3 - eps) S where
  X_gt_one := h.X_gt_one
  eps_nonneg := h.eps_nonneg
  deltaD_pos := by linarith
  deltaW_pos := by linarith
  D_lower := h.D_lower
  W_lower := h.W_lower
  DW_eq_Q := h.DW_eq_Q
  r_upper := h.r_upper

/-- **The supersession is strict.**  There is a source datum that satisfies the
positive-power range (with `δ_D = δ_W = 1/10`) and **fails** the fixed-`1/3`
range.  Hence `DwpPositivePowerRange` is strictly weaker as a hypothesis, i.e.
strictly more general as an interface. -/
theorem dwpPositivePowerRange_strictly_more_general :
    ∃ (X eps deltaD deltaW : ℝ) (S : D0WPSource),
      DwpPositivePowerRange X eps deltaD deltaW S ∧ ¬ HardP3PhysicalRange X eps S := by
  have hX1 : (1:ℝ) < 2 := by norm_num
  refine ⟨2, 0, 1/10, 1/10,
    ⟨1, 1, 1, 1, (2:ℝ) ^ ((1:ℝ)/10), (2:ℝ) ^ ((1:ℝ)/10),
      (2:ℝ) ^ ((1:ℝ)/10) * (2:ℝ) ^ ((1:ℝ)/10)⟩, ?_, ?_⟩
  · refine ⟨hX1, le_rfl, by norm_num, by norm_num, le_rfl, le_rfl, rfl, ?_⟩
    have h0 : ((1:ℕ) : ℝ) = (2:ℝ) ^ (0:ℝ) := by simp
    rw [h0]
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hX1) (by norm_num)
  · intro hbad
    have hD : (2:ℝ) ^ ((1:ℝ)/10) ≥ (2:ℝ) ^ ((1:ℝ)/3 - 0) := hbad.D_lower
    have hlt : (2:ℝ) ^ ((1:ℝ)/10) < (2:ℝ) ^ ((1:ℝ)/3 - 0) :=
      Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
    exact absurd hD (not_le.mpr hlt)

/-- **SOURCE PIN (UNINHABITED here).**  The obligation that the literal current
source derives the positive-power range, for *some* pair of positive exponents
with a genuine gain over the modulus range.  No inhabitant is constructed in
this repository, and none may be inferred from a research report. -/
def DwpPositivePowerRangePin (X eps : ℝ) (S : D0WPSource) : Prop :=
  ∃ deltaD deltaW : ℝ,
    DwpPositivePowerRange X eps deltaD deltaW S ∧ (1:ℝ)/2 + eps < deltaD + deltaW

/-- The new pin is a genuine obligation: it can fail. -/
theorem dwpPositivePowerRangePin_not_automatic :
    ∃ (X eps : ℝ) (S : D0WPSource), ¬ DwpPositivePowerRangePin X eps S := by
  refine ⟨2, 0, ⟨1, 1, 1, 1, 0, 0, 0⟩, ?_⟩
  rintro ⟨dD, dW, hR, -⟩
  have hpos := hR.D_pos
  simp at hpos

end Universal.GHSpine
