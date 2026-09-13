/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
the high-frequency owner and the averaging firewall  (B8)

Append-only module.  Nothing pre-existing is edited.

The remaining dual frequencies (`|n| > x^{1/40000}`) are owned by a **single joint-average**
proposition,

```
HighDualJointAverageBound
```

which is the average the row consumer actually needs.  It is *not* replaced by a stronger
pointwise-per-frequency statement.  §3 encodes the research firewall at the theorem-DAG level:
a proposition bounding each fixed frequency separately (`FixedFrequencyAtomBound`) does **not**
imply the joint bound — there are dual data satisfying the atom bound and violating the joint
bound, because the number of frequencies grows with the scale.  Hence pointwise
Bourgain–Garaev plus absolute summation is insufficient, exactly as the research state records.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.LowFrequencyOwner

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. The two propositions -/

/-- **`HighDualJointAverageBound`** — the joint average over the remaining dual frequencies that
the row consumer requires.  EXTERNAL_ANALYTIC / OPEN — stated, never inhabited, not an axiom. -/
def HighDualJointAverageBound (D : DualData) (S0 : ℕ) : Prop :=
  ScalarBudget (fun x => highBGRow D x) (S0 + 2)

/-- **`FixedFrequencyAtomBound`** — the *strictly weaker* pointwise statement: each individual
dual frequency is bounded.  It is recorded only to be firewalled off in §3. -/
def FixedFrequencyAtomBound (D : DualData) (S0 : ℕ) : Prop :=
  ∀ n : ℤ, ScalarBudget (fun x => D.coef x n) (S0 + 2)

/-- The high-frequency owner feeds the pre-existing banked terminal owner `EPM2TopBound`, given
the exact identification of the EP-M2 terminal band with the high dual row. -/
theorem epM2TopBound_of_high {D : DualData} {Mtop : ℝ → ℝ} {S0 : ℕ}
    (hid : ∀ x, Mtop x = highBGRow D x) (h : HighDualJointAverageBound D S0) :
    EPM2TopBound Mtop S0 :=
  scalarBudget_congr hid h

/-! ## 2. The abstract counting firewall -/

/-- **Atomwise bounds do not control a growing sum.**  For every atom tolerance `b > 0` and every
target `T` there are finitely many frequencies whose coefficients are all bounded by `b` while
their sum exceeds `T`. -/
theorem atomwise_does_not_control_sum (b T : ℝ) (hb : 0 < b) :
    ∃ (F : Finset ℤ) (c : ℤ → ℝ), (∀ n ∈ F, |c n| ≤ b) ∧ T ≤ ∑ n ∈ F, c n := by
  refine ⟨Finset.Icc (1 : ℤ) (⌈T / b⌉₊ : ℤ), fun _ => b, fun n _ => by
    rw [abs_of_pos hb], ?_⟩
  rw [Finset.sum_const, Int.card_Icc]
  have hcard : ((⌈T / b⌉₊ : ℤ) + 1 - 1).toNat = ⌈T / b⌉₊ := by
    simp
  rw [hcard, nsmul_eq_mul]
  have hceil : T / b ≤ (⌈T / b⌉₊ : ℝ) := Nat.le_ceil _
  calc T = (T / b) * b := by field_simp
    _ ≤ (⌈T / b⌉₊ : ℝ) * b := by nlinarith

/-! ## 3. The theorem-DAG firewall: atoms ⇏ joint average -/

/-- The witness data: `⌊x⌋` frequencies placed strictly above the low cutoff, each carrying the
*budgeted* coefficient `x/(log x)²`. -/
noncomputable def atomWitness : DualData where
  freq := fun x => Finset.Icc ((bgLowCutoff x : ℤ) + 1) ((bgLowCutoff x : ℤ) + (⌊x⌋₊ : ℤ))
  coef := fun x _ => x / (Real.log x) ^ 2

theorem atomWitness_high_row (x : ℝ) :
    highBGRow atomWitness x = (⌊x⌋₊ : ℝ) * (x / (Real.log x) ^ 2) := by
  show ∑ n ∈ (Finset.Icc ((bgLowCutoff x : ℤ) + 1) ((bgLowCutoff x : ℤ) + (⌊x⌋₊ : ℤ))).filter
      (fun n => ¬ n.natAbs ≤ bgLowCutoff x), x / (Real.log x) ^ 2
    = (⌊x⌋₊ : ℝ) * (x / (Real.log x) ^ 2)
  rw [Finset.filter_true_of_mem (fun n hn => ?_), Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
  · congr 1
    have hcast : ((bgLowCutoff x : ℤ) + (⌊x⌋₊ : ℤ) + 1 - ((bgLowCutoff x : ℤ) + 1))
        = (⌊x⌋₊ : ℤ) := by ring
    rw [hcast, Int.toNat_natCast]
  · rw [Finset.mem_Icc] at hn
    intro hle
    have h1 : (n.natAbs : ℤ) ≤ (bgLowCutoff x : ℤ) := by exact_mod_cast hle
    rw [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at h1
    omega

/-- Each fixed frequency of the witness is budgeted. -/
theorem atomWitness_atoms : FixedFrequencyAtomBound atomWitness 0 := by
  intro n
  refine ⟨1, one_pos, fun x hx => ?_⟩
  have hlog : 1 ≤ Real.log x := one_le_log_of_three_le hx
  have hpos : (0 : ℝ) < (Real.log x) ^ 2 := by positivity
  have hx0 : (0 : ℝ) < x := by linarith
  have hval : (0 : ℝ) ≤ x / (Real.log x) ^ 2 := by positivity
  show |x / (Real.log x) ^ 2| ≤ 1 * x / (Real.log x) ^ 2
  rw [abs_of_nonneg hval, one_mul]

/-- The witness violates the joint-average bound: the number of frequencies grows. -/
theorem atomWitness_not_joint : ¬ HighDualJointAverageBound atomWitness 0 := by
  rintro ⟨C, hC, hb⟩
  set x : ℝ := max 3 (C + 1) with hxdef
  have hx3 : 3 ≤ x := le_max_left _ _
  have hxC : C + 1 ≤ x := le_max_right _ _
  have hlog : 1 ≤ Real.log x := one_le_log_of_three_le hx3
  have hpos : (0 : ℝ) < (Real.log x) ^ 2 := by positivity
  have hx0 : (0 : ℝ) < x := by linarith
  have hq : (0 : ℝ) < x / (Real.log x) ^ 2 := by positivity
  have hrow : (⌊x⌋₊ : ℝ) * (x / (Real.log x) ^ 2) ≤ C * x / (Real.log x) ^ 2 := by
    have h := hb x hx3
    have hbeta : |(⌊x⌋₊ : ℝ) * (x / (Real.log x) ^ 2)| ≤ C * x / (Real.log x) ^ (0 + 2) := by
      simpa only [atomWitness_high_row x] using h
    have habs : |(⌊x⌋₊ : ℝ) * (x / (Real.log x) ^ 2)| = (⌊x⌋₊ : ℝ) * (x / (Real.log x) ^ 2) :=
      abs_of_nonneg (by positivity)
    rw [habs] at hbeta
    simpa using hbeta
  have hCle : (⌊x⌋₊ : ℝ) ≤ C := by
    have hC' : C * x / (Real.log x) ^ 2 = C * (x / (Real.log x) ^ 2) := by ring
    rw [hC'] at hrow
    exact le_of_mul_le_mul_right (by linarith [hrow]) hq
  have hfloor : x - 1 < (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  linarith

/-- **The firewall.**  A proposition asserting only a fixed-frequency atom bound is *not* enough
to derive the high-frequency owner: the witness satisfies `FixedFrequencyAtomBound` and violates
`HighDualJointAverageBound`.  An additional averaging hypothesis is mandatory. -/
theorem atoms_do_not_imply_joint :
    ∃ D : DualData, FixedFrequencyAtomBound D 0 ∧ ¬ HighDualJointAverageBound D 0 :=
  ⟨atomWitness, atomWitness_atoms, atomWitness_not_joint⟩

/-- The high-frequency owner is not discharged. -/
theorem highDualJointAverageBound_open : ∃ D : DualData, ¬ HighDualJointAverageBound D 0 :=
  ⟨atomWitness, atomWitness_not_joint⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
