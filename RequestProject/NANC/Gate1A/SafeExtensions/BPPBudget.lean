/-
# NANC Gate 1A v9.3/v9.4 — the controlling BPP exponent ledger (exact ℚ / ℝ)

Frozen exponents: `M = X^{1/3}`, `R = X^a`, `L = X^b`, `H = X^{a + 2b - 2/3}`.

* **Controlling one-root comparison** `M · R^{-1/4} ≤ H` is exactly

      (5/4)·a + 2·b − 1 ≥ 0,          (`bppGateMargin`)

  with the frozen vertices giving margins **1/72, 1/24, 1/32**.

* The **older** comparison `M · R^{-1/2} ≤ H`, i.e. `(3/2)a + 2b − 1 ≥ 0`, with
  margins `1/12, 1/9, 5/48`, belongs to the *retracted* `R^{-1}` family-energy
  promotion and is banked here **only** as the obsolete ledger
  (`obsoleteR1Margin`); the two ledgers are never mixed.

* **Recombination error.**  With `U = L/H` and `D·H = L²`,

      (U^{-2} M² L⁴)/(M H L⁴) = M/D,

  whose exponent is `a − 1/3`, i.e. spare margin `1/3 − a`: **1/18, 1/18, 1/24**
  at the three vertices.  The weaker `U^{-1}` certificate gives `M/L`, with
  margins `0, −1/72, 0`: it is *negative at V2*, which is exactly why `U^{-2}`
  is the controlling error certificate.

* **PB one-sided budget** `MK·(MH)²/(R L⁴) = 1` under `MK = L²/H`, `M²H = R L²`.

* **Root depth.**  `∑_r ‖A_r‖ ≤ sqrt(#rows)·sqrt(∑_r T_r)` when `‖A_r‖² ≤ T_r`,
  and `sqrt(R^{-1/2}) = R^{-1/4}` — the one and only square root taken.

Everything is exact arithmetic; no analytic estimate is asserted.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

/-! ## 1. Frozen exponents and the controlling gate margin -/

/-- `M = X^{1/3}`. -/
def mExp : ℚ := 1 / 3

/-- `H = X^{a + 2b - 2/3}`. -/
def hExp (a b : ℚ) : ℚ := a + 2 * b - 2 / 3

/-- The controlling one-root gate margin: `hExp - (mExp - a/4) = (5/4)a + 2b - 1`. -/
def bppGateMargin (a b : ℚ) : ℚ := (5 / 4) * a + 2 * b - 1

/-- The controlling comparison `M·R^{-1/4} ≤ H` is exactly `bppGateMargin ≥ 0`. -/
theorem bppGateMargin_eq (a b : ℚ) : hExp a b - (mExp - a / 4) = bppGateMargin a b := by
  unfold hExp mExp bppGateMargin; ring

/-- The obsolete (retracted) `R^{-1/2}`-operator margin `(3/2)a + 2b - 1`. -/
def obsoleteR1Margin (a b : ℚ) : ℚ := (3 / 2) * a + 2 * b - 1

theorem obsoleteR1Margin_eq (a b : ℚ) : hExp a b - (mExp - a / 2) = obsoleteR1Margin a b := by
  unfold hExp mExp obsoleteR1Margin; ring

/-- Vertex `V₁ = (5/18, 1/3)`. -/
def bppV1 : ℚ × ℚ := (5 / 18, 1 / 3)

/-- Vertex `V₂ = (5/18, 25/72)`. -/
def bppV2 : ℚ × ℚ := (5 / 18, 25 / 72)

/-- Vertex `V₃ = (7/24, 1/3)`. -/
def bppV3 : ℚ × ℚ := (7 / 24, 1 / 3)

theorem bpp_gate_margin_V1 : bppGateMargin bppV1.1 bppV1.2 = 1 / 72 := by
  norm_num [bppGateMargin, bppV1]

theorem bpp_gate_margin_V2 : bppGateMargin bppV2.1 bppV2.2 = 1 / 24 := by
  norm_num [bppGateMargin, bppV2]

theorem bpp_gate_margin_V3 : bppGateMargin bppV3.1 bppV3.2 = 1 / 32 := by
  norm_num [bppGateMargin, bppV3]

/-- All three controlling margins are strictly positive. -/
theorem bpp_gate_margins_pos :
    0 < bppGateMargin bppV1.1 bppV1.2 ∧ 0 < bppGateMargin bppV2.1 bppV2.2 ∧
      0 < bppGateMargin bppV3.1 bppV3.2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [bpp_gate_margin_V1, bpp_gate_margin_V2, bpp_gate_margin_V3]

/-- The obsolete ledger, banked for comparison only (**not** controlling). -/
theorem obsolete_margins :
    obsoleteR1Margin bppV1.1 bppV1.2 = 1 / 12 ∧
      obsoleteR1Margin bppV2.1 bppV2.2 = 1 / 9 ∧
      obsoleteR1Margin bppV3.1 bppV3.2 = 5 / 48 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [obsoleteR1Margin, bppV1, bppV2, bppV3]

/-- The two ledgers are genuinely different at every frozen vertex. -/
theorem ledgers_not_interchangeable :
    bppGateMargin bppV1.1 bppV1.2 ≠ obsoleteR1Margin bppV1.1 bppV1.2 ∧
      bppGateMargin bppV2.1 bppV2.2 ≠ obsoleteR1Margin bppV2.1 bppV2.2 ∧
      bppGateMargin bppV3.1 bppV3.2 ≠ obsoleteR1Margin bppV3.1 bppV3.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [bppGateMargin, obsoleteR1Margin, bppV1, bppV2, bppV3]

/-! ## 2. Recombination error: `U^{-2}` is controlling -/

/-- **`U^{-2}` recombination-error identity.**  With `U = L/H` and `D·H = L²`,
the ratio of the `U^{-2}` error energy to the normalized target is exactly
`M/D`. -/
theorem recombinationError_U2_budget (M H L D U : ℝ) (hM : M ≠ 0) (hH : H ≠ 0) (hL : L ≠ 0)
    (hD : D ≠ 0) (hU : U = L / H) (hDH : D * H = L ^ 2) :
    (U ^ (-2 : ℤ) * M ^ 2 * L ^ 4) / (M * H * L ^ 4) = M / D := by
  subst hU
  have hUne : L / H ≠ 0 := div_ne_zero hL hH
  have hexp : ((L / H) ^ (-2 : ℤ)) = H ^ 2 / L ^ 2 := by
    rw [zpow_neg, zpow_two, div_mul_div_comm]
    field_simp
  rw [hexp]
  have hL2 : (L : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  field_simp
  nlinarith [hDH, sq_nonneg L, sq_nonneg H]

/-- The `U^{-2}` error spare exponent is `1/3 - a`. -/
def errorMarginU2 (a : ℚ) : ℚ := 1 / 3 - a

/-- The weaker `U^{-1}` error spare exponent is `1/3 - b`. -/
def errorMarginU1 (b : ℚ) : ℚ := 1 / 3 - b

theorem errorMarginU2_vertices :
    errorMarginU2 bppV1.1 = 1 / 18 ∧ errorMarginU2 bppV2.1 = 1 / 18 ∧
      errorMarginU2 bppV3.1 = 1 / 24 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [errorMarginU2, bppV1, bppV2, bppV3]

/-- **Why `U^{-1}` is not the controlling certificate**: its spare margin is
`0, -1/72, 0` — negative at `V₂`. -/
theorem errorMarginU1_fails_at_V2 :
    errorMarginU1 bppV1.2 = 0 ∧ errorMarginU1 bppV2.2 = -(1 / 72) ∧
      errorMarginU1 bppV3.2 = 0 ∧ errorMarginU1 bppV2.2 < 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [errorMarginU1, bppV1, bppV2, bppV3]

/-! ## 3. PB one-sided nuclear budget -/

/-- **PB one-sided budget identity.**  `MK·(M H)²/(R L⁴) = 1` under
`MK = L²/H` and `M² H = R L²`. -/
theorem pb_oneSided_budget_eq_one (MK M H L R : ℝ) (hL : L ≠ 0) (hR : R ≠ 0)
    (hMK : MK = L ^ 2 / H) (hbudget : M ^ 2 * H = R * L ^ 2) :
    MK * (M * H) ^ 2 / (R * L ^ 4) = 1 := by
  subst hMK
  field_simp
  nlinarith [hbudget, sq_nonneg L, sq_nonneg H, sq_nonneg M]

/-! ## 4. Root depth: exactly one square root -/

/-- **Outer four-cycle root depth.**  Finite Cauchy over the family index. -/
theorem outerFourCycle_rootDepth {Row : Type*} [Fintype Row] (op T : Row → ℝ)
    (hop : ∀ r, 0 ≤ op r) (hT : ∀ r, (op r) ^ 2 ≤ T r) :
    ∑ r, op r ≤ Real.sqrt (Fintype.card Row) * Real.sqrt (∑ r, T r) := by
  classical
  have hsum_nonneg : 0 ≤ ∑ r, op r := Finset.sum_nonneg fun r _ => hop r
  have hcauchy : (∑ r, op r) ^ 2 ≤ (Fintype.card Row : ℝ) * ∑ r, (op r) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Row)) (f := op)
    simpa [Finset.card_univ] using this
  have hTsum : ∑ r, (op r) ^ 2 ≤ ∑ r, T r := Finset.sum_le_sum fun r _ => hT r
  have hcard : (0 : ℝ) ≤ (Fintype.card Row : ℝ) := by positivity
  have hchain : (∑ r, op r) ^ 2 ≤ (Fintype.card Row : ℝ) * ∑ r, T r :=
    hcauchy.trans (mul_le_mul_of_nonneg_left hTsum hcard)
  calc ∑ r, op r = Real.sqrt ((∑ r, op r) ^ 2) := (Real.sqrt_sq hsum_nonneg).symm
    _ ≤ Real.sqrt ((Fintype.card Row : ℝ) * ∑ r, T r) := Real.sqrt_le_sqrt hchain
    _ = Real.sqrt (Fintype.card Row) * Real.sqrt (∑ r, T r) := Real.sqrt_mul hcard _

/-- **The one root.**  An `R^{-1/2}` family-energy ratio becomes an `R^{-1/4}`
variance/operator ratio — and no further root is taken. -/
theorem oneRoot_energy_to_operator {R : ℝ} (hR : 0 < R) :
    Real.sqrt (R ^ (-(1 : ℝ) / 2)) = R ^ (-(1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
  norm_num

end TwinPrimeProject.NANC.Gate1A.V94
