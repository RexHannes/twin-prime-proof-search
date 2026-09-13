/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
the exact dual-frequency split  (B6)

Append-only module.  Exact algebra only; no estimate is stated, nothing pre-existing is edited.

The EP-M2 / Poisson representation presents each row as a sum over dual frequencies `n`.  With a
cutoff `Nlow` the row splits **exactly** into a low and a high part,

```
FullDualRow = LowDualRow + HighDualRow,
```

and at moment level into the exact square/cross decomposition

```
𝔐(T) = 𝔐(T_high) + 2 𝔠(T_low, T_high) + 𝔐(T_low).
```

§3 records the firewall against the natural but **false** shortcut: deleting frequencies is not
monotone, so a bound for a sub-block of frequencies is not a bound for the whole row (and
conversely).

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Realisation

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Finset

/-! ## 1. The dual-frequency data and the exact row split -/

/-- Dual-frequency data: for each scale `x`, the finite set of dual frequencies occurring in the
Poisson representation together with their coefficients. -/
structure DualData where
  /-- the finite dual-frequency set at scale `x` -/
  freq : ℝ → Finset ℤ
  /-- the dual coefficient of the frequency `n` at scale `x` -/
  coef : ℝ → ℤ → ℝ

namespace DualData

/-- The full dual row at scale `x`. -/
def fullDualRow (D : DualData) (x : ℝ) : ℝ := ∑ n ∈ D.freq x, D.coef x n

/-- The low dual row: the frequencies with `|n| ≤ Nlow x`. -/
def lowDualRow (D : DualData) (Nlow : ℝ → ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (D.freq x).filter (fun n => n.natAbs ≤ Nlow x), D.coef x n

/-- The high dual row: the frequencies with `|n| > Nlow x`. -/
def highDualRow (D : DualData) (Nlow : ℝ → ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (D.freq x).filter (fun n => ¬ n.natAbs ≤ Nlow x), D.coef x n

end DualData

open DualData

/-- **The exact dual-frequency split** `FullDualRow = LowDualRow + HighDualRow`. -/
theorem dual_row_split (D : DualData) (Nlow : ℝ → ℕ) (x : ℝ) :
    D.fullDualRow x = D.lowDualRow Nlow x + D.highDualRow Nlow x := by
  unfold DualData.fullDualRow DualData.lowDualRow DualData.highDualRow
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- A cutoff exceeding every occurring frequency puts the whole row in the low part. -/
theorem highDualRow_eq_zero {D : DualData} {Nlow : ℝ → ℕ} {x : ℝ}
    (h : ∀ n ∈ D.freq x, n.natAbs ≤ Nlow x) : D.highDualRow Nlow x = 0 := by
  unfold DualData.highDualRow
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_filter] at hn
  exact absurd (h n hn.1) hn.2

/-! ## 2. The exact moment decomposition of the split -/

/-- The weighted quadratic moment of a row family over a finite index set. -/
def momentOf {ι : Type*} (S : Finset ι) (W : ι → ℝ) (T : ι → ℝ) : ℝ :=
  ∑ i ∈ S, W i * (T i) ^ 2

/-- The weighted cross term of two row families. -/
def crossOf {ι : Type*} (S : Finset ι) (W : ι → ℝ) (T T' : ι → ℝ) : ℝ :=
  ∑ i ∈ S, W i * (T i * T' i)

/-- **The exact square/cross decomposition at moment level.** -/
theorem momentOf_split {ι : Type*} {S : Finset ι} {W T Tlow Thigh : ι → ℝ}
    (h : ∀ i, T i = Tlow i + Thigh i) :
    momentOf S W T = momentOf S W Thigh + 2 * crossOf S W Tlow Thigh + momentOf S W Tlow := by
  unfold momentOf crossOf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i]
  ring

/-- The moment-level form of the dual-frequency split, for a family of rows indexed by `ι` each
carrying its own dual data. -/
theorem dualMoment_split {ι : Type*} {S : Finset ι} {W : ι → ℝ} {D : ι → DualData}
    {Nlow : ℝ → ℕ} {x : ℝ} :
    momentOf S W (fun i => (D i).fullDualRow x)
      = momentOf S W (fun i => (D i).highDualRow Nlow x)
        + 2 * crossOf S W (fun i => (D i).lowDualRow Nlow x)
            (fun i => (D i).highDualRow Nlow x)
        + momentOf S W (fun i => (D i).lowDualRow Nlow x) :=
  momentOf_split (fun i => dual_row_split (D i) Nlow x)

/-! ## 3. Firewall: deleting frequencies is not monotone -/

/-- **No monotonicity under deleting frequencies.**  A sub-block of the dual row can be larger
than the whole row: there are data whose full row vanishes while the low block equals `1`.  Hence
a bound on the whole row gives nothing for a block, and a bound for a block gives nothing for the
whole row. -/
theorem dual_block_not_monotone :
    ∃ (D : DualData) (Nlow : ℝ → ℕ) (x : ℝ),
      D.fullDualRow x = 0 ∧ D.lowDualRow Nlow x = 1 ∧ D.highDualRow Nlow x = -1 := by
  refine ⟨⟨fun _ => {0, 1}, fun _ n => if n = 0 then 1 else -1⟩, fun _ => 0, 0, ?_, ?_, ?_⟩
  · show ∑ n ∈ ({0, 1} : Finset ℤ), (if n = 0 then (1 : ℝ) else -1) = 0
    norm_num
  · show ∑ n ∈ ({0, 1} : Finset ℤ).filter (fun n => n.natAbs ≤ 0),
      (if n = 0 then (1 : ℝ) else -1) = 1
    norm_num [Finset.filter_insert, Finset.filter_singleton]
  · show ∑ n ∈ ({0, 1} : Finset ℤ).filter (fun n => ¬ n.natAbs ≤ 0),
      (if n = 0 then (1 : ℝ) else -1) = -1
    norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- **The moment of a block is not bounded by the moment of the whole.**  With the data above,
the full row has moment `0` while the low block has moment `1`. -/
theorem dual_block_moment_not_monotone :
    ∃ (D : DualData) (Nlow : ℝ → ℕ) (x : ℝ),
      momentOf ({0} : Finset ℕ) (fun _ => 1) (fun _ => D.fullDualRow x) = 0
        ∧ momentOf ({0} : Finset ℕ) (fun _ => 1) (fun _ => D.lowDualRow Nlow x) = 1 := by
  obtain ⟨D, Nlow, x, hfull, hlow, -⟩ := dual_block_not_monotone
  refine ⟨D, Nlow, x, ?_, ?_⟩
  · simp [momentOf, hfull]
  · simp [momentOf, hlow]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
