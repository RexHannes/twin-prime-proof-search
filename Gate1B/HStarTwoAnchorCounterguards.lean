import Gate1B.HStarTwoAnchorDifferenceAlgebra

/-!
# Gate 1B · **non-converse / source-loss firewall** for the two-anchor source

This module is load-bearing *negative* mathematics.  It shows exactly how much
information the difference algebra of
`Gate1B.HStarTwoAnchorDifferenceAlgebra` retains, and how much of the physical
`+2` source it **loses**.

## Contents

* §1 the difference system as a predicate, and the theorem
  `differenceSystem_implies_common_defect` : `C₁ = C₂`;
* §2 the explicit finite integer **countermodel**
  `differenceSystem_does_not_imply_physicalAnchors` : a configuration with
  strictly positive variables satisfying *both* difference lines, with
  `C₁ = C₂ = 0 ≠ 2`; hence neither physical anchor holds.  Consequently the
  implication "difference equations `→` `C₁ = 2`" is **refuted**;
* §3 the **independent-`H` energy firewall**: abstract `A(H)`, `B(H)` factors
  attached to the two difference lines; a nonzero product enforces only
  `C₁ = C₂`, and the countermodel gives a nonzero product at a nonphysical
  common defect (`independentHEnergy_not_physicalSource`);
* §4 the **single-line Δ retraction**: the eliminated-`H` line is *equivalent*
  to `C₁ = C₂`, hence strictly weaker than the physical two-anchor system
  (`singleLineDelta_strictly_weaker`).

Nothing here says that the difference equations or the single Δ-line are
*false*; the banked content is that they are **insufficient as a physical
source dictionary**.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTwoAnchor

namespace TwoTRawConfig

variable (c : TwoTRawConfig)

/-! ## 1. The difference system and the common-defect consequence -/

/-- The two-`T` **difference system** at parameter `H`: the `g`-scaled
numerator line together with the quotient line. -/
def DifferenceSystem (H : ℤ) : Prop :=
  c.Hnum = c.g * H ∧ c.quotDiff = H

/-- **The difference system implies only the equality of the two physical
defects.** -/
theorem differenceSystem_implies_common_defect {H : ℤ}
    (h : c.DifferenceSystem H) : c.rawDefect1 = c.rawDefect2 := by
  obtain ⟨hnum, hquot⟩ := h
  have hg : c.g * c.quotDiff = c.g * H := by rw [hquot]
  simp only [Hnum] at hnum
  simp only [quotDiff] at hg
  simp only [rawDefect1, rawDefect2]
  linarith [hg, hnum]

end TwoTRawConfig

/-! ## 2. The countermodel: the difference system is strictly weaker -/

/-- The explicit finite countermodel

```
  g = 1,  e₁ = e₂ = wp₁ = wp₂ = 1,  ℓ₁ = 5, ℓ₂ = 3,  T₁ = T₂ = 1,  π₁ = 5, π₂ = 3
```

All eleven variables are strictly positive.  Both difference lines hold with
`H = 2`, and both defects are `0`. -/
def defectCountermodel : TwoTRawConfig :=
  { g := 1, e1 := 1, e2 := 1, wp1 := 1, wp2 := 1, ell1 := 5, ell2 := 3,
    T1 := 1, T2 := 1, pi1 := 5, pi2 := 3 }

theorem defectCountermodel_positive :
    0 < defectCountermodel.g ∧ 0 < defectCountermodel.e1 ∧
      0 < defectCountermodel.e2 ∧ 0 < defectCountermodel.wp1 ∧
      0 < defectCountermodel.wp2 ∧ 0 < defectCountermodel.ell1 ∧
      0 < defectCountermodel.ell2 ∧ 0 < defectCountermodel.T1 ∧
      0 < defectCountermodel.T2 ∧ 0 < defectCountermodel.pi1 ∧
      0 < defectCountermodel.pi2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [defectCountermodel]

theorem defectCountermodel_differenceSystem :
    defectCountermodel.DifferenceSystem 2 := by
  constructor <;>
    simp [defectCountermodel, TwoTRawConfig.Hnum, TwoTRawConfig.quotDiff]

theorem defectCountermodel_defects :
    defectCountermodel.rawDefect1 = 0 ∧ defectCountermodel.rawDefect2 = 0 := by
  constructor <;>
    simp [defectCountermodel, TwoTRawConfig.rawDefect1, TwoTRawConfig.rawDefect2]

/-- **BANKED FIREWALL.**  `differenceSystem_does_not_imply_physicalAnchors`.

There is a strictly positive integer configuration satisfying **both**
difference lines whose common defect is `0`, not `2`; neither physical anchor
holds.  Hence the difference system is *not* a physical source dictionary. -/
theorem differenceSystem_does_not_imply_physicalAnchors :
    ∃ (c : TwoTRawConfig) (H : ℤ),
      c.DifferenceSystem H ∧ c.rawDefect1 = c.rawDefect2 ∧ c.rawDefect1 ≠ 2 ∧
        ¬ c.Anchor1 ∧ ¬ c.Anchor2 := by
  refine ⟨defectCountermodel, 2, defectCountermodel_differenceSystem, ?_, ?_, ?_, ?_⟩
  · rw [defectCountermodel_defects.1, defectCountermodel_defects.2]
  · rw [defectCountermodel_defects.1]; norm_num
  · rw [TwoTRawConfig.anchor1_iff_defect1, defectCountermodel_defects.1]; norm_num
  · rw [TwoTRawConfig.anchor2_iff_defect2, defectCountermodel_defects.2]; norm_num

/-- **The forbidden implication is refuted.**  "Difference equations `→`
`C₁ = 2`" is false. -/
theorem differenceSystem_does_not_imply_defect_two :
    ¬ ∀ (c : TwoTRawConfig) (H : ℤ), c.DifferenceSystem H → c.rawDefect1 = 2 := by
  intro h
  exact absurd (h defectCountermodel 2 defectCountermodel_differenceSystem)
    (by rw [defectCountermodel_defects.1]; norm_num)

/-! ## 3. The independent-`H` energy firewall -/

/-- The abstract `H`-energy factor of the **numerator** difference line. -/
noncomputable def AFactor (c : TwoTRawConfig) (H : ℤ) : ℂ :=
  if c.Hnum = c.g * H then 1 else 0

/-- The abstract `H`-energy factor of the **quotient** difference line. -/
noncomputable def BFactor (c : TwoTRawConfig) (H : ℤ) : ℂ :=
  if c.quotDiff = H then 1 else 0

theorem AFactor_mul_BFactor_ne_zero_iff (c : TwoTRawConfig) (H : ℤ) :
    AFactor c H * BFactor c H ≠ 0 ↔ c.DifferenceSystem H := by
  unfold AFactor BFactor TwoTRawConfig.DifferenceSystem
  by_cases h1 : c.Hnum = c.g * H <;> by_cases h2 : c.quotDiff = H <;>
    simp [h1, h2]

/-- **A nonzero independent-`H` product enforces only `C₁ = C₂`.** -/
theorem independentH_product_implies_common_defect (c : TwoTRawConfig) (H : ℤ)
    (h : AFactor c H * BFactor c H ≠ 0) : c.rawDefect1 = c.rawDefect2 :=
  c.differenceSystem_implies_common_defect ((AFactor_mul_BFactor_ne_zero_iff c H).1 h)

/-- **BANKED FIREWALL.**  `independentHEnergy_not_physicalSource`.

The independent-`H` product `A(H)·B(H)` is supported on configurations that are
*not* physical: it is nonzero at the countermodel, whose common defect is
`0 ≠ 2`. -/
theorem independentHEnergy_not_physicalSource :
    ∃ (c : TwoTRawConfig) (H : ℤ),
      AFactor c H * BFactor c H ≠ 0 ∧ c.rawDefect1 = c.rawDefect2 ∧
        c.rawDefect1 ≠ 2 := by
  refine ⟨defectCountermodel, 2, ?_, ?_, ?_⟩
  · exact (AFactor_mul_BFactor_ne_zero_iff _ _).2 defectCountermodel_differenceSystem
  · rw [defectCountermodel_defects.1, defectCountermodel_defects.2]
  · rw [defectCountermodel_defects.1]; norm_num

/-- The independent-`H` product does **not** characterise the physical source:
there is no implication from "some `H` has nonzero product" to the anchors. -/
theorem independentHEnergy_does_not_imply_anchors :
    ¬ ∀ c : TwoTRawConfig,
        (∃ H : ℤ, AFactor c H * BFactor c H ≠ 0) → c.Anchor1 := by
  intro h
  have hA : defectCountermodel.Anchor1 :=
    h defectCountermodel ⟨2, (AFactor_mul_BFactor_ne_zero_iff _ _).2
      defectCountermodel_differenceSystem⟩
  rw [TwoTRawConfig.anchor1_iff_defect1, defectCountermodel_defects.1] at hA
  norm_num at hA

/-! ## 4. The single-line Δ retraction -/

namespace TwoTRawConfig

/-- The **eliminated-`H` single Δ-line**

`T₁π₁ − T₂π₂ = g (e₁wp₁ℓ₁ − e₂wp₂ℓ₂)`. -/
def SingleLineDelta (c : TwoTRawConfig) : Prop := c.Hnum = c.g * c.quotDiff

/-- **The single Δ-line is exactly the common-defect equation `C₁ = C₂`.** -/
theorem singleLineDelta_iff_common_defect (c : TwoTRawConfig) :
    c.SingleLineDelta ↔ c.rawDefect1 = c.rawDefect2 := by
  simp only [SingleLineDelta, Hnum, quotDiff, rawDefect1, rawDefect2]
  constructor <;> intro h <;> nlinarith [h]

end TwoTRawConfig

/-- **SINGLE-LINE-DELTA45 : RETRACTED AS A PHYSICAL SOURCE DICTIONARY.**

The single Δ-line is strictly weaker than the physical two-anchor system: the
countermodel satisfies it while both anchors fail.  (The equation itself is
*not* false — it is a true consequence of the anchors; it is merely
insufficient.) -/
theorem singleLineDelta_strictly_weaker :
    (∀ c : TwoTRawConfig, c.Anchor1 → c.Anchor2 → c.SingleLineDelta) ∧
      ∃ c : TwoTRawConfig, c.SingleLineDelta ∧ ¬ c.Anchor1 ∧ ¬ c.Anchor2 := by
  refine ⟨fun c h1 h2 => c.hnum_eq_g_mul_quotDiff h1 h2, defectCountermodel, ?_, ?_, ?_⟩
  · exact (TwoTRawConfig.singleLineDelta_iff_common_defect _).2
      (by rw [defectCountermodel_defects.1, defectCountermodel_defects.2])
  · rw [TwoTRawConfig.anchor1_iff_defect1, defectCountermodel_defects.1]; norm_num
  · rw [TwoTRawConfig.anchor2_iff_defect2, defectCountermodel_defects.2]; norm_num

end HStarTwoAnchor
end CurrentProgramme
end TwinPrimeProject
