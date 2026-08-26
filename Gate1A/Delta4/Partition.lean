/-
# Gate-1A Δv4 §25 — the complete clean-block partition

The clean full-conductor main contribution splits into exactly five sectors:

```
A.  Δ_out ≠ 0
B.  Δ_out = 0,  Z = 0, L ≠ 0, r ∤ L
C.  Δ_out = 0,  Z = 0, L ≠ 0, r ∣ L
D.  Δ_out = 0,  L = 0
E.  Δ_out = 0,  Z ≠ 0, L ≠ 0
```

This file proves that the five sectors are **exhaustive** and **pairwise
disjoint**, so that no contribution can disappear between coordinate systems.
The classifier is literal and total; every branch is attained.
-/
import Mathlib

namespace Gate1A

namespace Delta4

/-- The five clean-block sectors of §25. -/
inductive CleanSector
  /-- A: nonzero outer curvature. -/
  | curvature
  /-- B: `Z = 0`, `L ≠ 0`, `r ∤ L` — the regular one-zero axis. -/
  | axisRegular
  /-- C: `Z = 0`, `L ≠ 0`, `r ∣ L` — the true local zero. -/
  | axisTrueZero
  /-- D: `L = 0` — the `h = 0` firewall. -/
  | firewall
  /-- E: `Z ≠ 0`, `L ≠ 0` — the generic projective sector. -/
  | generic
  deriving DecidableEq, Repr

/-- The literal classifier of a clean state, from its curvature `Δ`, its PB
row coordinate `Z`, its graph coordinate `L` and the moving prime `r`. -/
def classify (Delta Z L : ℤ) (r : ℕ) : CleanSector :=
  if Delta ≠ 0 then CleanSector.curvature
  else if L = 0 then CleanSector.firewall
  else if Z = 0 then
    (if (r : ℤ) ∣ L then CleanSector.axisTrueZero else CleanSector.axisRegular)
  else CleanSector.generic

/-- **§25 exhaustiveness.**  Every clean state is classified. -/
theorem classify_total (Delta Z L : ℤ) (r : ℕ) :
    classify Delta Z L r = CleanSector.curvature ∨
    classify Delta Z L r = CleanSector.axisRegular ∨
    classify Delta Z L r = CleanSector.axisTrueZero ∨
    classify Delta Z L r = CleanSector.firewall ∨
    classify Delta Z L r = CleanSector.generic := by
  unfold classify
  split_ifs <;> simp

/-- **§25 sector A.** -/
theorem classify_curvature {Delta Z L : ℤ} {r : ℕ} (h : Delta ≠ 0) :
    classify Delta Z L r = CleanSector.curvature := by
  simp [classify, h]

/-- **§25 sector B.** -/
theorem classify_axisRegular {Delta Z L : ℤ} {r : ℕ} (hD : Delta = 0) (hZ : Z = 0)
    (hL : L ≠ 0) (hr : ¬ (r : ℤ) ∣ L) :
    classify Delta Z L r = CleanSector.axisRegular := by
  simp [classify, hD, hZ, hL, hr]

/-- **§25 sector C.** -/
theorem classify_axisTrueZero {Delta Z L : ℤ} {r : ℕ} (hD : Delta = 0) (hZ : Z = 0)
    (hL : L ≠ 0) (hr : (r : ℤ) ∣ L) :
    classify Delta Z L r = CleanSector.axisTrueZero := by
  simp [classify, hD, hZ, hL, hr]

/-- **§25 sector D.** -/
theorem classify_firewall {Delta Z L : ℤ} {r : ℕ} (hD : Delta = 0) (hL : L = 0) :
    classify Delta Z L r = CleanSector.firewall := by
  simp [classify, hD, hL]

/-- **§25 sector E.** -/
theorem classify_generic {Delta Z L : ℤ} {r : ℕ} (hD : Delta = 0) (hZ : Z ≠ 0)
    (hL : L ≠ 0) :
    classify Delta Z L r = CleanSector.generic := by
  simp [classify, hD, hZ, hL]

/-- **§25 disjointness.**  The classifier is a function, so the five sectors
are pairwise disjoint; concretely, no state is in two sectors at once. -/
theorem classify_disjoint (Delta Z L : ℤ) (r : ℕ) (s t : CleanSector)
    (hs : classify Delta Z L r = s) (ht : classify Delta Z L r = t) : s = t := by
  rw [← hs, ← ht]

/-- Each sector is actually attained, so the partition is not vacuous. -/
theorem classify_sectors_nonvacuous :
    classify 1 0 0 3 = CleanSector.curvature ∧
    classify 0 0 1 3 = CleanSector.axisRegular ∧
    classify 0 0 3 3 = CleanSector.axisTrueZero ∧
    classify 0 1 0 3 = CleanSector.firewall ∧
    classify 0 1 1 3 = CleanSector.generic := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end Delta4

end Gate1A
