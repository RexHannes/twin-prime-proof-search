/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
the low-frequency analytic interface  (B7)

Append-only module.  Nothing pre-existing is edited.

The current research claim outside Lean is a Bourgain–Garaev-type estimate for the dual
frequencies with `0 < |n| ≤ x^{1/40000}`.  **That estimate is not imported, not assumed and not
axiomatised.**  Exactly one ordinary proposition is created for it,

```
LowDualBourgainGaraevBound
```

which is never inhabited, and the surrounding implications are proved:

```
LowDualBourgainGaraevBound + (exact low identification)  ⇒  LowRamanujanBudget
```

`LowRamanujanBudget` is the *pre-existing* banked EP-M2 consumer; no new consumer is created.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.DualFrequency

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. The low-frequency cutoff -/

/-- The low-frequency cutoff `N_low(x) = ⌊x^{1/40000}⌋`, the exact range in which the external
Bourgain–Garaev-type estimate is claimed. -/
noncomputable def bgLowCutoff (x : ℝ) : ℕ := ⌊x ^ ((1 : ℝ) / 40000)⌋₊

/-- The low-frequency dual row at the Bourgain–Garaev cutoff. -/
noncomputable def lowBGRow (D : DualData) (x : ℝ) : ℝ := D.lowDualRow bgLowCutoff x

/-- The high-frequency dual row at the Bourgain–Garaev cutoff. -/
noncomputable def highBGRow (D : DualData) (x : ℝ) : ℝ := D.highDualRow bgLowCutoff x

/-- The exact split at the Bourgain–Garaev cutoff. -/
theorem bg_row_split (D : DualData) (x : ℝ) :
    D.fullDualRow x = lowBGRow D x + highBGRow D x :=
  dual_row_split D bgLowCutoff x

/-! ## 2. The single low-frequency proposition -/

/-- **`LowDualBourgainGaraevBound`** — the external low-frequency estimate required by the EP-M2
consumer on the dual frequencies `0 < |n| ≤ x^{1/40000}`.  EXTERNAL_ANALYTIC / OPEN — an ordinary
proposition, stated, never inhabited, **not** an axiom, and **not** a formalisation of
Bourgain–Garaev's theorem. -/
def LowDualBourgainGaraevBound (D : DualData) (S0 : ℕ) : Prop :=
  ScalarBudget (fun x => lowBGRow D x) (S0 + 2)

/-- **`LowDualBudget`** — what the EP-M2 consumer needs from the low-frequency part: exactly the
pre-existing banked `LowRamanujanBudget`. -/
def LowDualBudget (Mlow : ℝ → ℝ) (S0 : ℕ) : Prop := LowRamanujanBudget Mlow S0

/-- **`LowDualBourgainGaraevBound` ⇒ `LowDualBudget`.**  The only extra input is the exact
identification of the EP-M2 low band with the low dual row; no estimate is created here. -/
theorem lowDualBudget_of_bg {D : DualData} {Mlow : ℝ → ℝ} {S0 : ℕ}
    (hid : ∀ x, Mlow x = lowBGRow D x) (h : LowDualBourgainGaraevBound D S0) :
    LowDualBudget Mlow S0 :=
  scalarBudget_congr hid h

/-- The low-frequency owner is **not** discharged: there are dual data violating it, so it is
not a theorem and may not be silently upgraded. -/
theorem lowDualBourgainGaraevBound_open :
    ∃ D : DualData, ¬ LowDualBourgainGaraevBound D 0 := by
  refine ⟨⟨fun _ => {0}, fun x _ => x⟩, ?_⟩
  intro h
  have hid : ∀ x : ℝ, x = lowBGRow ⟨fun _ => {0}, fun x _ => x⟩ x := by
    intro x
    show x = ∑ n ∈ ({0} : Finset ℤ).filter (fun n => n.natAbs ≤ bgLowCutoff x), x
    rw [Finset.filter_true_of_mem (fun n hn => by
      rw [Finset.mem_singleton] at hn; simp [hn])]
    simp
  exact identity_not_budgeted 1 (scalarBudget_congr hid h)

/-- The exact low/high identification used by the bridge: if the EP-M2 low band *is* the low dual
row and the EP-M2 terminal band *is* the high dual row, their sum is the full dual row. -/
theorem bg_bands_assemble {D : DualData} {Mlow Mtop : ℝ → ℝ}
    (hlow : ∀ x, Mlow x = lowBGRow D x) (htop : ∀ x, Mtop x = highBGRow D x) (x : ℝ) :
    Mlow x + Mtop x = D.fullDualRow x := by
  rw [hlow, htop, bg_row_split D x]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
