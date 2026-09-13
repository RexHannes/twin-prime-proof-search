/-
# Gate1B / R11 / Frontier / … / ReciprocityBG : a nondegenerate row-realisation fixture  (B14)

Append-only module; all values are kernel-computed, nothing analytic is claimed.

`RowIdentification.lean` realises the exact bridge `epM2RowIdentification` (and hence
`epM2Realisation`) on explicit canonical data.  This module checks that the realisation is **not
an identification of the zero object**: for the explicit cutoffs `I = (0,3] × (0,1]`, source
support `Z = {1}`, unit source coefficient and unit outer weight, on the chart box
`E₀ = {1}`, `S₀ = {1,2}`, the realised family is the nonzero constant `−5`.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.RowIdentification

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Finset ArithmeticFunction
open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. The fixture data -/

/-- The fixture cutoffs `I₁ = (0,3]`, `I₂ = (0,1]`, so `Q_max = 3`. -/
def Ifix : Cutoffs := ⟨0, 3, 0, 1⟩

/-- The fixture source support. -/
def Zfix : Finset ℕ := {1}

/-- The fixture source coefficient (constant `1`; no analytic property is used). -/
def betaFix : ℕ → ℝ := fun _ => 1

/-- The fixture outer weight (constant `1`). -/
def Wfix : ℕ → ℝ := fun _ => 1

theorem Ioc_three : (Finset.Ioc 0 3 : Finset ℕ) = {1, 2, 3} := by decide

/-! ## 2. The truncated Möbius coefficient of the fixture -/

theorem lam_fix_one : lam Ifix 1 = 1 := by
  simp [lam, Ifix, Cutoffs.box, Cutoffs.I1, Cutoffs.I2, Ioc_three]

theorem lam_fix_two : lam Ifix 2 = 0 := by
  simp [lam, Ifix, Cutoffs.box, Cutoffs.I1, Cutoffs.I2, Ioc_three]

theorem lam_fix_three : lam Ifix 3 = -1 := by
  simp [lam, Ifix, Cutoffs.box, Cutoffs.I1, Cutoffs.I2, Ioc_three,
    moebius_apply_prime (by norm_num : Nat.Prime 3)]
  decide

theorem lam_fix_four : lam Ifix 4 = 0 := by
  simp [lam, Ifix, Cutoffs.box, Cutoffs.I1, Cutoffs.I2, Ioc_three]

theorem divisors_three : (3 : ℕ).divisors = {1, 3} := by decide

theorem divisors_four : (4 : ℕ).divisors = {1, 2, 4} := by decide

theorem Fsum_fix_three : Fsum Ifix 3 = 0 := by
  rw [Fsum, divisors_three]
  norm_num [lam_fix_one, lam_fix_three]

theorem Fsum_fix_four : Fsum Ifix 4 = 1 := by
  rw [Fsum, divisors_four]
  norm_num [lam_fix_one, lam_fix_two, lam_fix_four]

/-! ## 3. The fixture row values -/

theorem divRow_fix (s : ℕ) : divRow Ifix Zfix betaFix 1 s = ((Fsum Ifix (s + 2) : ℚ) : ℝ) := by
  unfold divRow rowOp Zfix betaFix
  rw [Finset.sum_singleton]
  simp

theorem divRow_fix_one : divRow Ifix Zfix betaFix 1 1 = 0 := by
  rw [divRow_fix]
  norm_num [Fsum_fix_three]

theorem divRow_fix_two : divRow Ifix Zfix betaFix 1 2 = 1 := by
  rw [divRow_fix]
  norm_num [Fsum_fix_four]

/-! ## 4. The fixture packet, its kernel mean, and nondegeneracy -/

/-- The fixture chart box `E₀ × S₀ = {1} × {1,2}`. -/
theorem chart_fix : (({1} : Finset ℕ) ×ˢ ({1, 2} : Finset ℕ)) = {(1, 1), (1, 2)} := by decide

theorem packet_fix :
    ((({1} : Finset ℕ) ×ˢ ({1, 2} : Finset ℕ)).image pairIdx)
      = {pairIdx (1, 1), pairIdx (1, 2)} := by
  rw [chart_fix]
  rfl

theorem pairIdx_ne : pairIdx (1, 1) ≠ pairIdx (1, 2) := by
  intro h
  have := pairIdx_injective h
  simp at this

/-- The kernel mean of the fixture packet is `1/2`. -/
theorem rowCentering_fix :
    rowCentering Ifix Zfix betaFix {1} {1, 2} = 1 / 2 := by
  unfold rowCentering kernelMean
  rw [packet_fix, Finset.sum_pair pairIdx_ne, Finset.card_pair pairIdx_ne,
    canonicalRowKernel_pairIdx, canonicalRowKernel_pairIdx, divRow_fix_one, divRow_fix_two]
  norm_num

/-- **The realised family is nonzero.**  For the fixture the centered row value at `(e,s) = (1,2)`
is `1/2 ≠ 0`, so the identification of `RowIdentification.lean` identifies a nonzero object. -/
theorem rowDataClosed_fix_ne_zero (x : ℝ) :
    (rowDataClosed Ifix Zfix betaFix Wfix {1} {1, 2}).epM2Family x ≠ 0 := by
  refine rowDataClosed_ne_zero Ifix Zfix betaFix Wfix {1} {1, 2} x
    (fun p _ => by norm_num [Wfix]) (p0 := (1, 2)) (by decide) (by norm_num [Wfix]) ?_
  rw [← rowCoefficientIdentification, rowCentering_fix, divRow_fix_two]
  norm_num

/-- The exact value of the fixture family: `−10 · ((0 − ½)² + (1 − ½)²) = −5`. -/
theorem rowDataClosed_fix_value (x : ℝ) :
    (rowDataClosed Ifix Zfix betaFix Wfix {1} {1, 2}).epM2Family x = -5 := by
  rw [rowDataClosed_epM2Family_eq, hbCoeff_five_two, chart_fix,
    Finset.sum_pair (by decide : ((1, 1) : ℕ × ℕ) ≠ (1, 2)),
    ← rowCoefficientIdentification, ← rowCoefficientIdentification, rowCentering_fix,
    divRow_fix_one, divRow_fix_two]
  norm_num [Wfix]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
