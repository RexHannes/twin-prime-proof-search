/-
# Gate1B / R11 / Frontier / CanonicalRootSync : the open j = 2 box certificate  (P6)

Append-only module.  Exact rational arithmetic; no analytic claim.

A single rational **physical survivor**

```
η = 2/5,   a = 11/100,   b = 111/1000,   θ = 621/1000
```

is certified to satisfy simultaneously

* the retained physical K = 5 constraints (`η < 99/200`, `η + 5a ≤ 1`, `η + 5b ≤ 1`);
* `θ = 621/1000`;
* `θ > 4/7`  (above the Pascadi capacity ceiling, hence **every** permutation of the literal
  Pascadi conditions fails — proved from the firewall, not assumed);
* `θ < 5/8`;
* `θ > 45/89` (outside the Wright interface region).

Hence the geometric survivor region — physical, uncovered by Wright, above the Pascadi capacity —
is **nonempty**.  No finite huge integer witness is formalised: it would add no logical
dependency. -/
import Gate1B.R11.Frontier.CanonicalRootSync.PascadiFirewall
import Gate1B.R11.Frontier.CanonicalRootSync.WrightPrefix

namespace Gate1B.R11.Frontier.CanonicalRootSync

/-- The certified open-box packet. -/
def openBox : K5Packet := ⟨2/5, 11/100, 111/1000⟩

/-- The box is physical for the retained K = 5, `j = 2` constraints. -/
theorem openBox_physical : PhysicalK5 openBox := by
  norm_num [PhysicalK5, openBox]

/-- Its total exponent is exactly `621/1000`. -/
theorem openBox_theta : openBox.theta = 621/1000 := by
  norm_num [K5Packet.theta, openBox]

/-- `θ > 4/7`: the box is above the Pascadi capacity ceiling. -/
theorem openBox_theta_gt_four_sevenths : (4 : ℚ)/7 < openBox.theta := by
  rw [openBox_theta]; norm_num

/-- `θ < 5/8`. -/
theorem openBox_theta_lt_five_eighths : openBox.theta < 5/8 := by
  rw [openBox_theta]; norm_num

/-- `θ > 45/89`: the box is outside the Wright interface region. -/
theorem openBox_theta_gt_wright : (45 : ℚ)/89 < openBox.theta := by
  rw [openBox_theta]; norm_num

/-- **Every Pascadi permutation fails on the box**, for every nonnegative slack — derived from
the capacity firewall, not assumed. -/
theorem openBox_not_pascadiCallable {epsP : ℚ} (heps : 0 ≤ epsP) :
    ¬ PascadiCallable epsP openBox := by
  refine not_pascadiCallable_of_theta_large heps openBox_physical ?_
  rw [openBox_theta]
  linarith

/-- **The box is not in the Wright region** either, for every nonnegative slack. -/
theorem openBox_not_wright {epsW : ℚ} (heps : 0 ≤ epsW) : ¬ WrightRegion epsW openBox := by
  unfold WrightRegion
  rw [openBox_theta]
  push_neg
  linarith

/-- **Nonemptiness of the geometric survivor region.**  There is a physical K = 5, `j = 2`
packet which is simultaneously outside the Wright interface region and above the Pascadi
capacity ceiling, with `4/7 < θ < 5/8`. -/
theorem survivor_region_nonempty {epsP epsW : ℚ} (hP : 0 ≤ epsP) (hW : 0 ≤ epsW) :
    ∃ p : K5Packet, PhysicalK5 p ∧ 4/7 < p.theta ∧ p.theta < 5/8 ∧ 45/89 < p.theta
      ∧ ¬ PascadiCallable epsP p ∧ ¬ WrightRegion epsW p :=
  ⟨openBox, openBox_physical, openBox_theta_gt_four_sevenths, openBox_theta_lt_five_eighths,
    openBox_theta_gt_wright, openBox_not_pascadiCallable hP, openBox_not_wright hW⟩

end Gate1B.R11.Frontier.CanonicalRootSync
