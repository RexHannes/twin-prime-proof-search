import Gate1B.HStarTwoAnchorPhysicalSource

/-!
# Gate 1B · derived **two-`T` difference algebra** of the two-anchor source

Exact integer algebra only.  The difference relations

```
  T₁ π₁ − T₂ π₂ = g · H          (the `g`-scaled numerator line)
  e₁ wp₁ ℓ₁ − e₂ wp₂ ℓ₂ = H      (the quotient line)
```

are proved here as **consequences** of the two physical `+2` anchors, and the
exact *source-equivalent* system is identified:

```
  anchor₁ ∧ anchor₂   ↔   (T₁π₁ − T₂π₂ = gH) ∧ (e₁wp₁ℓ₁ − e₂wp₂ℓ₂ = H) ∧ (C₁ = 2)
```

The converse *without* the `+2` anchor line is **false**; that is the firewall
banked in `Gate1B.HStarTwoAnchorCounterguards`.

## Contents

* §1 the raw integer configuration `TwoTRawConfig` (no equations imposed) and
  its named derived quantities `Hnum`, `quotDiff`, `rawDefect₁`, `rawDefect₂`;
* §2 the two anchors of a raw configuration and the derived difference pair;
* §3 the **two-`T` difference equivalence** `Hnum = g·H ↔ quotDiff = H`;
* §4 the **source-exact equivalent system** and the recovery of the second
  anchor from both difference lines and the first anchor;
* §5 specialisation to the physical source `HStarTwoAnchorSource`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTwoAnchor

/-! ## 1. Raw integer configurations -/

/-- A **raw** two-`T` configuration: the eleven physical integer variables with
*no* equation imposed.  Physical sources and non-physical counterexamples are
both configurations; the difference between them is exactly the anchor data. -/
structure TwoTRawConfig where
  g : ℤ
  e1 : ℤ
  e2 : ℤ
  wp1 : ℤ
  wp2 : ℤ
  ell1 : ℤ
  ell2 : ℤ
  T1 : ℤ
  T2 : ℤ
  pi1 : ℤ
  pi2 : ℤ
  deriving DecidableEq

namespace TwoTRawConfig

variable (c : TwoTRawConfig)

/-- The numerator difference `Hnum = T₁π₁ − T₂π₂`. -/
def Hnum : ℤ := c.T1 * c.pi1 - c.T2 * c.pi2

/-- The quotient difference `e₁wp₁ℓ₁ − e₂wp₂ℓ₂`. -/
def quotDiff : ℤ := c.e1 * c.wp1 * c.ell1 - c.e2 * c.wp2 * c.ell2

/-- The first defect `C₁ = g e₁ wp₁ ℓ₁ − T₁ π₁`. -/
def rawDefect1 : ℤ := c.g * c.e1 * c.wp1 * c.ell1 - c.T1 * c.pi1

/-- The second defect `C₂ = g e₂ wp₂ ℓ₂ − T₂ π₂`. -/
def rawDefect2 : ℤ := c.g * c.e2 * c.wp2 * c.ell2 - c.T2 * c.pi2

/-- The literal first `+2` anchor of a raw configuration. -/
def Anchor1 : Prop := c.g * c.e1 * c.wp1 * c.ell1 = c.T1 * c.pi1 + 2

/-- The literal second `+2` anchor of a raw configuration. -/
def Anchor2 : Prop := c.g * c.e2 * c.wp2 * c.ell2 = c.T2 * c.pi2 + 2

theorem anchor1_iff_defect1 : c.Anchor1 ↔ c.rawDefect1 = 2 := by
  simp only [Anchor1, rawDefect1]; omega

theorem anchor2_iff_defect2 : c.Anchor2 ↔ c.rawDefect2 = 2 := by
  simp only [Anchor2, rawDefect2]; omega

/-! ## 2. The difference pair derived from the two anchors -/

/-- **From the two physical anchors, the numerator difference is exactly `g`
times the quotient difference.** -/
theorem hnum_eq_g_mul_quotDiff (h1 : c.Anchor1) (h2 : c.Anchor2) :
    c.Hnum = c.g * c.quotDiff := by
  simp only [Anchor1, Anchor2] at h1 h2
  simp only [Hnum, quotDiff]
  linarith [h1, h2]

/-- **BOXED.**  The two physical anchors imply the two-`T` difference system,
with `H` the quotient difference:

`T₁π₁ − T₂π₂ = gH` **and** `e₁wp₁ℓ₁ − e₂wp₂ℓ₂ = H`. -/
theorem anchors_imply_difference_system (h1 : c.Anchor1) (h2 : c.Anchor2) :
    ∃ H : ℤ, c.Hnum = c.g * H ∧ c.quotDiff = H :=
  ⟨c.quotDiff, c.hnum_eq_g_mul_quotDiff h1 h2, rfl⟩

/-! ## 3. The two-`T` difference equivalence -/

/-- **The difference equivalence.**  Given the two physical anchors and a
nonzero `g`, the `g`-scaled numerator line holds for `H` **iff** the quotient
line holds for the same `H`. -/
theorem hnum_eq_iff_quotDiff_eq (hg : c.g ≠ 0) (h1 : c.Anchor1) (h2 : c.Anchor2)
    (H : ℤ) : c.Hnum = c.g * H ↔ c.quotDiff = H := by
  rw [c.hnum_eq_g_mul_quotDiff h1 h2]
  constructor
  · intro h; exact mul_left_cancel₀ hg h
  · intro h; rw [h]

/-! ## 4. The source-exact equivalent system -/

/-- **Source-exact equivalence.**  For `g ≠ 0` the two physical anchors,
together with the naming of `H` by the quotient line, are *equivalent* to the
three-line system

```
  T₁π₁ − T₂π₂ = g H,      e₁wp₁ℓ₁ − e₂wp₂ℓ₂ = H,      C₁ = 2.
```

The third line is the irreducible physical `+2` input: dropping it makes the
system strictly weaker (`differenceSystem_does_not_imply_physicalAnchors`). -/
theorem twoAnchor_iff_differenceSystem_with_anchor (H : ℤ) :
    (c.Anchor1 ∧ c.Anchor2 ∧ c.quotDiff = H) ↔
      (c.Hnum = c.g * H ∧ c.quotDiff = H ∧ c.rawDefect1 = 2) := by
  constructor
  · rintro ⟨h1, h2, hH⟩
    refine ⟨?_, hH, (c.anchor1_iff_defect1).1 h1⟩
    rw [c.hnum_eq_g_mul_quotDiff h1 h2, hH]
  · rintro ⟨hnum, hH, hd1⟩
    have h1 : c.Anchor1 := (c.anchor1_iff_defect1).2 hd1
    refine ⟨h1, ?_, hH⟩
    simp only [Anchor1] at h1
    simp only [Hnum] at hnum
    simp only [quotDiff] at hH
    have hgH : c.g * (c.e1 * c.wp1 * c.ell1 - c.e2 * c.wp2 * c.ell2) = c.g * H := by
      rw [hH]
    simp only [Anchor2]
    linarith [hgH, hnum, h1]

/-- **The second anchor is recovered** from both difference lines and the first
anchor.  (This is the only legal way to obtain anchor₂ from difference data.) -/
theorem anchor2_of_differences_and_anchor1 {H : ℤ}
    (hnum : c.Hnum = c.g * H) (hquot : c.quotDiff = H) (h1 : c.Anchor1) :
    c.Anchor2 := by
  have hg : c.g * c.quotDiff = c.g * H := by rw [hquot]
  simp only [Anchor1] at h1
  simp only [Hnum] at hnum
  simp only [quotDiff] at hg
  simp only [Anchor2]
  linarith [hg, hnum, h1]

end TwoTRawConfig

/-! ## 5. Specialisation to the physical source -/

namespace HStarTwoAnchorSource

/-- The raw integer configuration underlying a physical source. -/
def toRaw (S : HStarTwoAnchorSource) : TwoTRawConfig :=
  { g := S.g, e1 := S.e1, e2 := S.e2, wp1 := S.wp1, wp2 := S.wp2,
    ell1 := S.ell1, ell2 := S.ell2, T1 := S.T1, T2 := S.T2,
    pi1 := S.pi1, pi2 := S.pi2 }

theorem toRaw_anchor1 (S : HStarTwoAnchorSource) : S.toRaw.Anchor1 := by
  simpa [toRaw, TwoTRawConfig.Anchor1] using S.anchor1Z

theorem toRaw_anchor2 (S : HStarTwoAnchorSource) : S.toRaw.Anchor2 := by
  simpa [toRaw, TwoTRawConfig.Anchor2] using S.anchor2Z

theorem toRaw_g_ne_zero (S : HStarTwoAnchorSource) : S.toRaw.g ≠ 0 := by
  have := S.g_pos
  simp only [toRaw]
  exact_mod_cast this.ne'

/-- **BOXED, physical form.**  Every physical two-anchor source satisfies the
two-`T` difference system with `H` the quotient difference. -/
theorem physical_difference_system (S : HStarTwoAnchorSource) :
    (S.T1 : ℤ) * S.pi1 - (S.T2 : ℤ) * S.pi2
        = (S.g : ℤ) * ((S.e1 : ℤ) * S.wp1 * S.ell1 - (S.e2 : ℤ) * S.wp2 * S.ell2)
      ∧ (S.e1 : ℤ) * S.wp1 * S.ell1 - (S.e2 : ℤ) * S.wp2 * S.ell2
          = (S.e1 : ℤ) * S.wp1 * S.ell1 - (S.e2 : ℤ) * S.wp2 * S.ell2 := by
  refine ⟨?_, rfl⟩
  have := S.toRaw.hnum_eq_g_mul_quotDiff S.toRaw_anchor1 S.toRaw_anchor2
  simpa [toRaw, TwoTRawConfig.Hnum, TwoTRawConfig.quotDiff] using this

/-- The physical difference equivalence: for the physical source, the
`g`-scaled numerator line holds at `H` iff the quotient line does. -/
theorem physical_hnum_iff_quotDiff (S : HStarTwoAnchorSource) (H : ℤ) :
    S.toRaw.Hnum = (S.g : ℤ) * H ↔ S.toRaw.quotDiff = H :=
  S.toRaw.hnum_eq_iff_quotDiff_eq S.toRaw_g_ne_zero S.toRaw_anchor1 S.toRaw_anchor2 H

end HStarTwoAnchorSource

end HStarTwoAnchor
end CurrentProgramme
end TwinPrimeProject
