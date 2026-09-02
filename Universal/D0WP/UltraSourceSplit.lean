/-
# Universal / D0WP — ultra source split and the exact same-block cut object

**Status of this module: KERNEL_PROVED finite combinatorics.  No analytic
cancellation is encoded anywhere.**

§10.  With block-origin metadata for the HB leaves, and *given* that
block-saturated same-block rows have already been routed elsewhere, the ultra
family splits as a disjoint union

```
ThetaUltra = ThetaCross ⊎ ThetaCut
```

where `ThetaCross` has the two ultra prime `f`-leaves in different blocks and
`ThetaCut` has them in the same block with the selected `E` cutting the block.
There is no claim that the same-block part is empty.

§11.  The finite linear-HB leaf grammar is formalised literally, and we prove
only: the sibling count is `2^h - 1`; the selected/cut classification is exact
and exhaustive.  We also prove explicitly that the same-block cut sum is **not**
universally zero, so that no hidden cancellation can be read into it.
-/
import Mathlib

namespace Universal.D0WP

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## §10 Ultra source split -/

/-- Block-origin metadata of an ultra row: the block origins of the two ultra
prime `f`-leaves, and whether the selected `E` cuts the block. -/
structure UltraBlockData (ι : Type*) where
  /-- Block origin of the first ultra prime `f`-leaf. -/
  origin₁ : ι → ℕ
  /-- Block origin of the second ultra prime `f`-leaf. -/
  origin₂ : ι → ℕ
  /-- Whether the selected `E` cuts the (common) block. -/
  cuts : ι → Bool

variable {ι : Type*} [DecidableEq ι]

/-- Different block origins. -/
def ThetaCross (data : UltraBlockData ι) (Θ : Finset ι) : Finset ι :=
  Θ.filter (fun i => data.origin₁ i ≠ data.origin₂ i)

/-- Same block origin, selected `E` cutting the block. -/
def ThetaCut (data : UltraBlockData ι) (Θ : Finset ι) : Finset ι :=
  Θ.filter (fun i => data.origin₁ i = data.origin₂ i)

/-- **ULTRA SOURCE SPLIT (kernel-proved).**  Cross and cut rows are disjoint and
exhaust the ultra family. -/
theorem theta_ultra_split (data : UltraBlockData ι) (Θ : Finset ι) :
    Disjoint (ThetaCross data Θ) (ThetaCut data Θ) ∧
      ThetaCross data Θ ∪ ThetaCut data Θ = Θ := by
  constructor
  · refine Finset.disjoint_filter.2 ?_
    intro i _ h1 h2
    exact h1 h2
  · ext i
    simp only [Finset.mem_union, ThetaCross, ThetaCut, Finset.mem_filter]
    constructor
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    · intro hi
      by_cases h : data.origin₁ i = data.origin₂ i
      · exact Or.inr ⟨hi, h⟩
      · exact Or.inl ⟨hi, h⟩

omit [DecidableEq ι] in
/-- Under the routing hypothesis (block-saturated same-block rows already
routed), every same-block ultra row is a cut row. -/
theorem theta_cut_is_cutting (data : UltraBlockData ι) (Θ : Finset ι)
    (hrouted : ∀ i ∈ Θ, data.origin₁ i = data.origin₂ i → data.cuts i = true)
    (i : ι) (hi : i ∈ ThetaCut data Θ) : data.cuts i = true := by
  rw [ThetaCut, Finset.mem_filter] at hi
  exact hrouted i hi.1 hi.2

/-- Explicit non-claim: the same-block ultra part may be nonempty. -/
theorem theta_cut_can_be_nonempty :
    ∃ (data : UltraBlockData Unit) (Θ : Finset Unit), (ThetaCut data Θ).Nonempty := by
  refine ⟨⟨fun _ => 0, fun _ => 0, fun _ => true⟩, {()}, ⟨(), ?_⟩⟩
  simp [ThetaCut]

/-! ## §11 The exact same-block cut object -/

/-- Number of linear-HB siblings at depth `h`. -/
def hbSiblingCount (h : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 h, h.choose j

/-- **Finite sibling count (kernel-proved): `2^h - 1`.** -/
theorem hbSiblingCount_eq (h : ℕ) : hbSiblingCount h = 2 ^ h - 1 := by
  have hins : Finset.range (h + 1) = insert 0 (Finset.Icc 1 h) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnot : (0 : ℕ) ∉ Finset.Icc 1 h := by simp
  have h2 : ∑ j ∈ Finset.range (h + 1), h.choose j = 2 ^ h := Nat.sum_range_choose h
  rw [hins, Finset.sum_insert hnot] at h2
  simp only [Nat.choose_zero_right] at h2
  unfold hbSiblingCount
  omega

/-- The literal linear-HB leaf data: for each depth `j` a finite index set of
`(e, f)`-tuples. -/
structure LinearHBLeaves where
  /-- Index set of the depth-`j` leaves. -/
  idx : ℕ → Type
  /-- The index sets are finite. -/
  idxFintype : ∀ j, Fintype (idx j)
  /-- The `e`-variables (only the first `j` entries are used at depth `j`). -/
  e : ∀ j, idx j → ℕ → ℕ
  /-- The `f`-variables (only the first `j` entries are used at depth `j`). -/
  f : ∀ j, idx j → ℕ → ℕ

attribute [instance] LinearHBLeaves.idxFintype

/-- The value of a single leaf: `(log f₁) ∏_{i<j} μ(e_i)`. -/
noncomputable def leafValue (L : LinearHBLeaves) (j : ℕ) (x : L.idx j) : ℂ :=
  (Real.log (L.f j x 0) : ℂ) * ∏ i ∈ Finset.range j, (μ (L.e j x i) : ℂ)

/-- The finite linear-HB leaf sum
`Σ_j (-1)^{j-1} C(h,j) Σ_{e,f} (log f₁) ∏ μ(e_i)`. -/
noncomputable def hbLeafSum (L : LinearHBLeaves) (h : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 h, (-1) ^ (j - 1) * (h.choose j : ℂ) * ∑ x : L.idx j, leafValue L j x

/-- The selected-`E` cut indicator `0 < |E ∩ L_j| < 2j`. -/
def selectedCut (E Lblock : Finset ℕ) (j : ℕ) : Prop :=
  0 < (E ∩ Lblock).card ∧ (E ∩ Lblock).card < 2 * j

instance (E Lblock : Finset ℕ) (j : ℕ) : Decidable (selectedCut E Lblock j) := by
  unfold selectedCut
  infer_instance

/-- **Exact selected/cut classification (kernel-proved).**  For a block of
`2j` labels, the selected set either misses the block, or cuts it, or saturates
it — exactly one of the three. -/
theorem selected_trichotomy (E Lblock : Finset ℕ) (j : ℕ) (hL : Lblock.card = 2 * j) :
    ((E ∩ Lblock).card = 0 ∧ ¬ selectedCut E Lblock j ∧ (E ∩ Lblock).card ≠ 2 * j ∨
      selectedCut E Lblock j ∧ (E ∩ Lblock).card ≠ 0 ∧ (E ∩ Lblock).card ≠ 2 * j ∨
      (E ∩ Lblock).card = 2 * j ∧ (E ∩ Lblock).card ≠ 0 ∧ ¬ selectedCut E Lblock j)
      ∨ j = 0 := by
  have hle : (E ∩ Lblock).card ≤ 2 * j := by
    rw [← hL]
    exact Finset.card_le_card Finset.inter_subset_right
  by_cases hj : j = 0
  · exact Or.inr hj
  · refine Or.inl ?_
    unfold selectedCut
    rcases Nat.eq_zero_or_pos (E ∩ Lblock).card with h0 | hpos
    · exact Or.inl ⟨h0, by omega, by omega⟩
    · rcases eq_or_lt_of_le hle with hfull | hlt
      · exact Or.inr (Or.inr ⟨hfull, by omega, by omega⟩)
      · exact Or.inr (Or.inl ⟨⟨hpos, hlt⟩, by omega, by omega⟩)

/-- The literal same-block cut finite sum: the part of the leaf sum whose
selected set cuts the block. -/
noncomputable def sameBlockCutSum (L : LinearHBLeaves) (h : ℕ)
    (E : ∀ j, L.idx j → Finset ℕ) (Lblock : ∀ j, L.idx j → Finset ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 h, (-1) ^ (j - 1) * (h.choose j : ℂ) *
    ∑ x ∈ Finset.univ.filter (fun x : L.idx j => selectedCut (E j x) (Lblock j x) j),
      leafValue L j x

/-- **Explicit non-claim (kernel-proved).**  The same-block cut sum is not
universally zero: no exact cancellation may be assumed for it. -/
theorem sameBlockCutSum_not_always_zero :
    ∃ (L : LinearHBLeaves) (h : ℕ) (E Lblock : ∀ j, L.idx j → Finset ℕ),
      sameBlockCutSum L h E Lblock ≠ 0 := by
  refine ⟨⟨fun _ => Unit, fun _ => inferInstance, fun _ _ _ => 1, fun _ _ _ => 2⟩, 1,
    fun _ _ => {0}, fun _ _ => {0, 1}, ?_⟩
  simp only [sameBlockCutSum, leafValue]
  norm_num [selectedCut, Finset.filter_true_of_mem, Finset.Icc_self]
  intro hcontra
  have hexp : Complex.exp (Complex.log 2) = 2 := Complex.exp_log (by norm_num)
  rw [hcontra, Complex.exp_zero] at hexp
  norm_num at hexp

end Universal.D0WP
