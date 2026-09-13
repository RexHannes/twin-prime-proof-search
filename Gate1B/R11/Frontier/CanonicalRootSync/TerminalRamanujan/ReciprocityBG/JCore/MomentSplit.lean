/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : the exact moment split  (J4)

Append-only module; exact algebra only, no analytic statement, nothing inhabited.

The JCORE square expansion is split, exactly, into the equal-rational-frequency part and the
off-diagonal (unequal-frequency) part:

```
jExpand = jEqual + jOff .
```

By `delta_eq_zero_iff` the second part is exactly the part on which the normalised determinant
`Δ` is nonzero.  §3 contains the firewall against the standard error of "dropping" signed terms:
a signed sum can grow in modulus when terms are deleted, so no monotonicity is claimed anywhere.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.Determinant

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-! ## 1. The two parts -/

/-- The equal-rational-frequency part of the JCORE square expansion. -/
noncomputable def jEqual (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) : ℂ :=
  ∑ o ∈ O, ∑ i ∈ Iset, ∑ j ∈ Iset,
    if EqualRationalFrequency i j then F o i * (starRingEnd ℂ) (F o j) else 0

/-- The off-diagonal (unequal-frequency) part of the JCORE square expansion. -/
noncomputable def jOff (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) : ℂ :=
  ∑ o ∈ O, ∑ i ∈ Iset, ∑ j ∈ Iset,
    if EqualRationalFrequency i j then 0 else F o i * (starRingEnd ℂ) (F o j)

/-- **The exact moment split** `jExpand = jEqual + jOff`. -/
theorem jExpand_split (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) :
    jExpand O Iset F = jEqual O Iset F + jOff O Iset F := by
  unfold jExpand jEqual jOff
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split <;> ring

/-- **The off-diagonal part lives exactly where `Δ ≠ 0`.**  On admissible core points the
unequal-frequency condition is literally the nonvanishing of the normalised determinant. -/
theorem jOff_support_delta (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ)
    (hadm : ∀ i ∈ Iset, CoreAdmissible i) :
    jOff O Iset F
      = ∑ o ∈ O, ∑ i ∈ Iset, ∑ j ∈ Iset,
          if Delta i j = 0 then 0 else F o i * (starRingEnd ℂ) (F o j) := by
  unfold jOff
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun i hi =>
    Finset.sum_congr rfl fun j hj => ?_
  have hi' := hadm i hi
  have hj' := hadm j hj
  have hiff : Delta i j = 0 ↔ EqualRationalFrequency i j :=
    delta_eq_zero_iff hi'.upos hi'.vpos hj'.upos hj'.vpos
  by_cases h : EqualRationalFrequency i j
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hd => h (hiff.mp hd))]

/-! ## 2. Real families attached to the split -/

/-- An exact split of real families: the JCORE family is the equal part plus the off part. -/
def FamilySplit (J JEq JOffF : ℝ → ℝ) : Prop := ∀ x, J x = JEq x + JOffF x

/-! ## 3. Firewall: no monotonicity under deleting signed terms -/

/-- **Deleting signed terms is not monotone.**  A signed sum of two terms has modulus `0`, while
one of its two subsums has modulus `1`: no JCORE bound may be obtained by discarding terms. -/
theorem deleting_terms_not_monotone :
    ∃ a b : ℂ, ‖a + b‖ < ‖a‖ := by
  refine ⟨1, -1, ?_⟩
  norm_num

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
