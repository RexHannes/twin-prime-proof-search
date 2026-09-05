/-
# Universal / GHSpine — the new disjoint top-level census

**Status of this module: KERNEL_PROVED finite census algebra.**

The old top-level triple

```
FIRST_PARENT   /   BALANCED_R9   /   OTHER_PARENT
```

is **superseded as a disjoint top-level census**.  The reason is banked here as
a theorem, not as prose: the balanced R9 rows live *inside* the `k0 = J0 = 0`
block (see `Universal.GHSpine.FordGHSourceSpine.balancedR9_mem_k0J0` and
`old_triple_not_disjoint` below), so `BALANCED_R9` is not a top-level sibling of
`FIRST_PARENT` — it is a sub-class of it.  A census whose classes overlap cannot
carry a partition argument.

The replacement census is the genuinely disjoint and exhaustive trichotomy

```
P00_R9   ⊔   P00_nonR9   ⊔   P_ge1
```

where `P00` is the `k0 = 0 ∧ J0 = 0` block, split by the R9 flag, and `P_ge1`
is everything with `k0 ≥ 1` or `J0 ≥ 1`.  Kernel content:

* `classify` is total, so the census is exhaustive (`classify_mem_all`);
* membership in each class is characterised exactly
  (`classify_eq_*_iff`), whence pairwise disjointness (`classes_pairwise_disjoint`);
* on any finite row set the three filtered parts partition it
  (`census_card_split`, `census_union`, `census_filters_disjoint`);
* the old triple is **not** disjoint (`old_triple_not_disjoint`), and the new
  `P00_R9` class is exactly the old overlap (`P00_R9_eq_old_overlap`).
-/
import Mathlib

namespace Universal.GHSpine

/-! ## §1 Rows and the new top-level classes -/

/-- A top-level census row: the two Ford `G/H`-spine indices `k0`, `J0`, and the
R9 flag of the row's coordinate vector. -/
structure CensusRow where
  /-- The `k0` index. -/
  k0 : ℕ
  /-- The `J0` index. -/
  J0 : ℕ
  /-- Whether the row is a balanced R9 row. -/
  isR9 : Bool
  deriving DecidableEq, Repr

/-- The `k0 = J0 = 0` block. -/
def inK0J0 (r : CensusRow) : Prop := r.k0 = 0 ∧ r.J0 = 0

instance (r : CensusRow) : Decidable (inK0J0 r) := by
  unfold inK0J0; infer_instance

/-- The new disjoint top-level classes. -/
inductive TopClass
  /-- `k0 = J0 = 0` and the row is balanced R9. -/
  | P00_R9
  /-- `k0 = J0 = 0` and the row is not R9. -/
  | P00_nonR9
  /-- `k0 ≥ 1` or `J0 ≥ 1`. -/
  | P_ge1
  deriving DecidableEq, Repr

namespace TopClass

/-- The three classes, listed once each. -/
def all : List TopClass := [P00_R9, P00_nonR9, P_ge1]

theorem mem_all (c : TopClass) : c ∈ all := by cases c <;> simp [all]

theorem all_nodup : all.Nodup := by decide

end TopClass

/-- The deterministic top-level classifier. -/
def classify (r : CensusRow) : TopClass :=
  if inK0J0 r then (if r.isR9 then TopClass.P00_R9 else TopClass.P00_nonR9)
  else TopClass.P_ge1

/-! ## §2 Exhaustiveness and exact class characterisations -/

/-- **Exhaustive:** every row receives one of the three classes. -/
theorem classify_mem_all (r : CensusRow) : classify r ∈ TopClass.all :=
  TopClass.mem_all _

theorem classify_eq_P00_R9_iff (r : CensusRow) :
    classify r = TopClass.P00_R9 ↔ (r.k0 = 0 ∧ r.J0 = 0) ∧ r.isR9 = true := by
  unfold classify inK0J0
  by_cases h : r.k0 = 0 ∧ r.J0 = 0 <;> by_cases hr : r.isR9 = true <;>
    simp [h, hr]

theorem classify_eq_P00_nonR9_iff (r : CensusRow) :
    classify r = TopClass.P00_nonR9 ↔ (r.k0 = 0 ∧ r.J0 = 0) ∧ r.isR9 = false := by
  unfold classify inK0J0
  by_cases h : r.k0 = 0 ∧ r.J0 = 0 <;> by_cases hr : r.isR9 = true <;>
    simp [h, hr]

theorem classify_eq_P_ge1_iff (r : CensusRow) :
    classify r = TopClass.P_ge1 ↔ ¬ (r.k0 = 0 ∧ r.J0 = 0) := by
  unfold classify inK0J0
  by_cases h : r.k0 = 0 ∧ r.J0 = 0 <;> by_cases hr : r.isR9 = true <;>
    simp [h, hr]

/-- **Disjoint:** no row belongs to two of the three classes, because
`classify` is a function and the class predicates are exactly its fibres. -/
theorem classes_pairwise_disjoint (r : CensusRow) (c c' : TopClass)
    (h : classify r = c) (h' : classify r = c') : c = c' := by
  rw [← h, ← h']

/-! ## §3 Finite partition form -/

variable (rows : Finset CensusRow)

/-- The three census parts of a finite row set. -/
def part (c : TopClass) (rows : Finset CensusRow) : Finset CensusRow :=
  rows.filter (fun r => classify r = c)

theorem mem_part {c : TopClass} {rows : Finset CensusRow} {r : CensusRow} :
    r ∈ part c rows ↔ r ∈ rows ∧ classify r = c := by
  simp [part]

/-- The three parts are pairwise disjoint. -/
theorem census_filters_disjoint {c c' : TopClass} (h : c ≠ c') (rows : Finset CensusRow) :
    Disjoint (part c rows) (part c' rows) := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  rw [mem_part] at hr hr'
  exact h (classes_pairwise_disjoint r c c' hr.2 hr'.2)

/-- The three parts cover the row set. -/
theorem census_union (rows : Finset CensusRow) :
    part TopClass.P00_R9 rows ∪ part TopClass.P00_nonR9 rows ∪ part TopClass.P_ge1 rows
      = rows := by
  ext r
  simp only [Finset.mem_union, mem_part]
  constructor
  · rintro ((⟨hr, -⟩ | ⟨hr, -⟩) | ⟨hr, -⟩) <;> exact hr
  · intro hr
    have htri : classify r = TopClass.P00_R9 ∨ classify r = TopClass.P00_nonR9 ∨
        classify r = TopClass.P_ge1 := by
      cases classify r <;> simp
    rcases htri with hc | hc | hc
    · exact Or.inl (Or.inl ⟨hr, hc⟩)
    · exact Or.inl (Or.inr ⟨hr, hc⟩)
    · exact Or.inr ⟨hr, hc⟩

/-- **The census is a partition, in counting form.** -/
theorem census_card_split (rows : Finset CensusRow) :
    (part TopClass.P00_R9 rows).card + (part TopClass.P00_nonR9 rows).card
        + (part TopClass.P_ge1 rows).card = rows.card := by
  classical
  have h1 : (part TopClass.P00_R9 rows).card + (part TopClass.P00_nonR9 rows).card
      = (part TopClass.P00_R9 rows ∪ part TopClass.P00_nonR9 rows).card :=
    (Finset.card_union_of_disjoint (census_filters_disjoint (by decide) rows)).symm
  have hdisj :
      Disjoint (part TopClass.P00_R9 rows ∪ part TopClass.P00_nonR9 rows)
        (part TopClass.P_ge1 rows) := by
    rw [Finset.disjoint_union_left]
    exact ⟨census_filters_disjoint (by decide) rows, census_filters_disjoint (by decide) rows⟩
  rw [h1, ← Finset.card_union_of_disjoint hdisj, census_union]

/-! ## §4 Why the old triple is superseded -/

/-- The old top-level labels. -/
inductive OldClass
  /-- The `k0 = J0 = 0` first-parent block. -/
  | firstParent
  /-- The balanced R9 rows. -/
  | balancedR9
  /-- Everything outside the first-parent block. -/
  | otherParent
  deriving DecidableEq, Repr

/-- The old membership predicates, as they were used. -/
def oldMem : OldClass → CensusRow → Prop
  | OldClass.firstParent, r => inK0J0 r
  | OldClass.balancedR9, r => r.isR9 = true
  | OldClass.otherParent, r => ¬ inK0J0 r

/-- **The old triple is NOT a disjoint top-level census.**  A balanced R9 row
sits in the `k0 = J0 = 0` first-parent block, so it belongs to two of the three
old classes at once. -/
theorem old_triple_not_disjoint :
    ∃ r : CensusRow, oldMem OldClass.firstParent r ∧ oldMem OldClass.balancedR9 r := by
  refine ⟨⟨0, 0, true⟩, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · rfl

/-- The new `P00_R9` class is exactly the old overlap that broke disjointness,
now isolated as a class of its own. -/
theorem P00_R9_eq_old_overlap (r : CensusRow) :
    classify r = TopClass.P00_R9 ↔
      (oldMem OldClass.firstParent r ∧ oldMem OldClass.balancedR9 r) := by
  rw [classify_eq_P00_R9_iff]
  rfl

/-- The two `P00` classes together are exactly the old first-parent block, and
`P_ge1` is exactly the old other-parent block: no row is lost in the
supersession. -/
theorem new_census_covers_old (r : CensusRow) :
    (classify r = TopClass.P00_R9 ∨ classify r = TopClass.P00_nonR9 ↔
        oldMem OldClass.firstParent r)
      ∧ (classify r = TopClass.P_ge1 ↔ oldMem OldClass.otherParent r) := by
  constructor
  · rw [classify_eq_P00_R9_iff, classify_eq_P00_nonR9_iff]
    unfold oldMem inK0J0
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      cases hr : r.isR9
      · exact Or.inr ⟨h, rfl⟩
      · exact Or.inl ⟨h, rfl⟩
  · rw [classify_eq_P_ge1_iff]
    rfl

end Universal.GHSpine
