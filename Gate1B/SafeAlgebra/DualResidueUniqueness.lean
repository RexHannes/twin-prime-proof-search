/-
# Gate 1B v8.4 — dual window uniqueness (repair)

**Status: PROVED_FINITE.**

REPAIR.  It is **not** true that the infinite Poisson dual sum contains only one
frequency `m`: rapid decay is not compact support (see
`CountermodelsV84.lean`, item A).  What is true, and is proved here, is the
*window* statement:

* `residueClass_inter_interval_card_le_one` — an interval of diameter `< p`
  meets each residue class modulo `p` in at most one integer;
* `truncatedDual_frequency_unique` — under the one-sided truncation `|m| ≤ M`
  with `2 M < p`, the dual frequency satisfying the residue condition is unique.

The passage from the infinite dual sum to a truncated window is a
**rapid-decay truncation** and is ANALYTIC_INTERFACE_ONLY: it is not proved,
not axiomatised and not used here.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- **Interval–residue class uniqueness.**  If `hi - lo < p` then any two
integers of `[lo, hi]` in the same class mod `p` are equal. -/
theorem residueClass_inter_interval_card_le_one {p lo hi : ℤ} (hdiam : hi - lo < p)
    {x y : ℤ} (hx : x ∈ Set.Icc lo hi) (hy : y ∈ Set.Icc lo hi) (hcong : p ∣ x - y) :
    x = y := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have habs : |x - y| < p := by
    rw [abs_lt]; constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hcong habs
  linarith [sub_eq_zero.mp this]

/-- Set form: a residue class modulo `p` meets an interval of diameter `< p` in
at most one point. -/
theorem residueClass_inter_interval_subsingleton {p lo hi r : ℤ} (hdiam : hi - lo < p) :
    {x : ℤ | x ∈ Set.Icc lo hi ∧ p ∣ x - r}.Subsingleton := by
  rintro x ⟨hx, hxr⟩ y ⟨hy, hyr⟩
  exact residueClass_inter_interval_card_le_one hdiam hx hy (by
    have : x - y = (x - r) - (y - r) := by ring
    rw [this]; exact dvd_sub hxr hyr)

/-- **Truncated dual frequency uniqueness.**  With the symmetric truncation
`|m| ≤ M` and `2 M < p`, at most one dual frequency satisfies the residue
condition `m ≡ r (mod p)`. -/
theorem truncatedDual_frequency_unique {p M r : ℤ} (hwin : 2 * M < p) :
    {m : ℤ | |m| ≤ M ∧ p ∣ m - r}.Subsingleton := by
  rintro x ⟨hx, hxr⟩ y ⟨hy, hyr⟩
  have hx' : x ∈ Set.Icc (-M) M := by
    constructor <;> [linarith [neg_abs_le x]; linarith [le_abs_self x]]
  have hy' : y ∈ Set.Icc (-M) M := by
    constructor <;> [linarith [neg_abs_le y]; linarith [le_abs_self y]]
  refine residueClass_inter_interval_card_le_one (show M - -M < p by linarith) hx' hy' ?_
  have : x - y = (x - r) - (y - r) := by ring
  rw [this]; exact dvd_sub hxr hyr

end Gate1B.SafeAlgebra
