/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : clean source/core support  (J5)

Append-only module; exact algebra only.  **No** analytic statement is made here: in particular
it is *not* asserted that the complement of the clean support is small — that payment is carried
by the ordinary proposition `SourceCoreOverlapBudget` of `Owners.lean`, which is never
inhabited.

The clean-support predicate is

```
CleanSupport o i j  :  (z, v ṽ) = 1,
```

and the off-diagonal JCORE part splits exactly as

```
jOff = jOffClean + jOffOverlap .
```

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.MomentSplit

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-! ## 1. The clean-support predicate -/

/-- **Clean source/core support**: the source variable `z` is coprime to the product `v ṽ` of the
two second denominators. -/
def CleanSupport (o : Outer) (i j : Core) : Prop := Nat.Coprime o.z (i.v * j.v)

instance (o : Outer) (i j : Core) : Decidable (CleanSupport o i j) := by
  unfold CleanSupport Nat.Coprime; infer_instance

/-- On clean support the source variable is coprime to each of the two second denominators
separately. -/
theorem cleanSupport_coprime_left {o : Outer} {i j : Core} (h : CleanSupport o i j) :
    Nat.Coprime o.z i.v :=
  Nat.Coprime.coprime_dvd_right (Dvd.intro j.v rfl) h

theorem cleanSupport_coprime_right {o : Outer} {i j : Core} (h : CleanSupport o i j) :
    Nat.Coprime o.z j.v :=
  Nat.Coprime.coprime_dvd_right (Dvd.intro_left i.v rfl) h

/-- **Clean support is a genuine restriction.**  Admissible data exist off the clean support, so
the overlap part may not simply be omitted. -/
theorem cleanSupport_not_automatic :
    ∃ (o : Outer) (i j : Core), OuterAdmissible o ∧ CoreAdmissible i ∧ CoreAdmissible j
      ∧ ¬ CleanSupport o i j := by
  refine ⟨⟨1, 2, 0⟩, ⟨1, 1, 2⟩, ⟨1, 1, 2⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, ?_⟩, ⟨by norm_num, by norm_num, ?_⟩, ?_⟩
  · show Nat.Coprime (1 : ℤ).natAbs (1 * 2); norm_num
  · show Nat.Coprime (1 : ℤ).natAbs (1 * 2); norm_num
  · show ¬ Nat.Coprime 2 (2 * 2)
    decide

/-! ## 2. The exact clean / overlap decomposition -/

/-- The clean part of the off-diagonal JCORE expansion. -/
noncomputable def jOffClean (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) : ℂ :=
  ∑ o ∈ O, ∑ i ∈ Iset, ∑ j ∈ Iset,
    if EqualRationalFrequency i j then 0 else
      if CleanSupport o i j then F o i * (starRingEnd ℂ) (F o j) else 0

/-- The source/core overlap part of the off-diagonal JCORE expansion. -/
noncomputable def jOffOverlap (O : Finset Outer) (Iset : Finset Core)
    (F : Outer → Core → ℂ) : ℂ :=
  ∑ o ∈ O, ∑ i ∈ Iset, ∑ j ∈ Iset,
    if EqualRationalFrequency i j then 0 else
      if CleanSupport o i j then 0 else F o i * (starRingEnd ℂ) (F o j)

/-- **The exact clean-support decomposition** `jOff = jOffClean + jOffOverlap`.  This is an
identity of signed sums; no term is discarded and no monotonicity is used. -/
theorem jOff_clean_split (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) :
    jOff O Iset F = jOffClean O Iset F + jOffOverlap O Iset F := by
  unfold jOff jOffClean jOffOverlap
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hfr : EqualRationalFrequency i j
  · simp [hfr]
  · by_cases hcl : CleanSupport o i j <;> simp [hfr, hcl]

/-- The full expansion in its three exact pieces: equal-frequency, clean off-diagonal, and
source/core overlap. -/
theorem jExpand_three_way (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) :
    jExpand O Iset F = jEqual O Iset F + jOffClean O Iset F + jOffOverlap O Iset F := by
  rw [jExpand_split, jOff_clean_split, add_assoc]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
