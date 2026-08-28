/-
# Gate 1B v8.4 — power-recovery capacity for the H7 dual determinant

**Status: CAPACITY_ONLY (rational exponent bookkeeping).**

No `X^{o(1)}` factor is formalised; all statements are exact rational exponent
identities.  Scales: `Y = X^{1/9}`, `Q = X^ω`.

PREVIOUS DEFICIT.  `Q / Y⁴ = X^{ω - 4/9}`:

* at `ω = 13/18` the exponent is `5/18`;
* as `ω → 8/9` the exponent tends to `4/9`.

NATURAL-SCALE CAPACITY.  Under the abstract hypotheses

* `#(e,m)` states `∼ Y`      (exponent `1`),
* `N`-source mass `∼ Y⁸`     (exponent `8`),
* large-`p` divisor multiplicity `O(1)`  (exponent `0`),
* `d`-divisor multiplicity subpower      (exponent `0`),
* dyadic `s` harmonic sum `O(1)`         (exponent `0`),

the capacity exponent is `1 + 8 = 9`, i.e. `Y⁹`, so the *fixed positive-power*
deficit is reduced to exponent `0`.

**This is not a log saving.**  Exponent-zero capacity does not instantiate the
`Y⁹ log^{-A} X` interface; see `Gate1B/SafeExtensions/H7LogClosureFirewall.lean`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- The previous fixed-power deficit exponent of `Q / Y⁴`, in the `X` scale. -/
def h7DeficitExponentX (omega : ℚ) : ℚ := omega - 4 / 9

/-- The same deficit in the `Y` scale (`Y = X^{1/9}`). -/
def h7DeficitExponentY (omega : ℚ) : ℚ := 9 * omega - 4

/-- Consistency of the two scales. -/
theorem h7Deficit_scales (omega : ℚ) : 9 * h7DeficitExponentX omega = h7DeficitExponentY omega := by
  unfold h7DeficitExponentX h7DeficitExponentY; ring

/-- At `ω = 13/18` the deficit exponent is `5/18`. -/
theorem h7Deficit_at_13_18 : h7DeficitExponentX (13 / 18) = 5 / 18 := by
  unfold h7DeficitExponentX; norm_num

/-- At `ω = 8/9` the deficit exponent is `4/9`. -/
theorem h7Deficit_at_8_9 : h7DeficitExponentX (8 / 9) = 4 / 9 := by
  unfold h7DeficitExponentX; norm_num

/-- The deficit exponent is strictly positive on the whole range `ω > 4/9`: this
is the fixed-power wall that the dual determinant has to remove. -/
theorem h7Deficit_pos {omega : ℚ} (h : 4 / 9 < omega) : 0 < h7DeficitExponentX omega := by
  unfold h7DeficitExponentX; linarith

/-- The natural-scale capacity exponent (in the `Y` scale) assembled from the
five abstract inputs. -/
def h7NaturalScaleExponent (states mass largeP dDiv dyadic : ℚ) : ℚ :=
  states + mass + largeP + dDiv + dyadic

/-- **Natural-scale exponent.**  `1 + 8 + 0 + 0 + 0 = 9`, i.e. `Y⁹`. -/
theorem h7_dualDet_naturalScaleExponent {states mass largeP dDiv dyadic : ℚ}
    (hstates : states = 1) (hmass : mass = 8) (hlargeP : largeP = 0)
    (hdDiv : dDiv = 0) (hdyadic : dyadic = 0) :
    h7NaturalScaleExponent states mass largeP dDiv dyadic = 9 := by
  unfold h7NaturalScaleExponent; rw [hstates, hmass, hlargeP, hdDiv, hdyadic]; norm_num

/-- **Fixed-power deficit recovered to natural scale.**  With capacity exponent
`9` against the target exponent `9`, the remaining exponent gap is `0`: the
fixed positive-power deficit has been removed, and nothing more. -/
theorem h7_fixedPower_deficit_recovered {states mass largeP dDiv dyadic target : ℚ}
    (hstates : states = 1) (hmass : mass = 8) (hlargeP : largeP = 0)
    (hdDiv : dDiv = 0) (hdyadic : dyadic = 0) (htarget : target = 9) :
    h7NaturalScaleExponent states mass largeP dDiv dyadic - target = 0 := by
  rw [h7_dualDet_naturalScaleExponent hstates hmass hlargeP hdDiv hdyadic, htarget]
  norm_num

/-- The recovered exponent is `0`, hence **not** negative: no power saving is
claimed, only the removal of the fixed-power wall. -/
theorem h7_recovered_exponent_not_negative {states mass largeP dDiv dyadic : ℚ}
    (hstates : states = 1) (hmass : mass = 8) (hlargeP : largeP = 0)
    (hdDiv : dDiv = 0) (hdyadic : dyadic = 0) :
    ¬ (h7NaturalScaleExponent states mass largeP dDiv dyadic - 9 < 0) := by
  rw [h7_dualDet_naturalScaleExponent hstates hmass hlargeP hdDiv hdyadic]
  norm_num

end Gate1B.SafeAlgebra
