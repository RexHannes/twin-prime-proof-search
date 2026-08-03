import Mathlib

/-!
# Deficit and exponent arithmetic (§§7,11,12,13,14,16)

All statements here are exact real-exponent identities / inequalities and are
`LEAN_PROVED` (or `LEAN_PROVED_CORE` for the conditional interfaces, whose
analytic inputs are explicit hypotheses).  None of the analytic counting
estimates are asserted; only the exponent arithmetic is proved.
-/

namespace Banking.Deficit

open Real

/-! ## Exponent comparisons for the reported controlled P1 strata (§11). -/

/-- `2μ+1 < μ+4/3 ↔ μ < 1/3` (near-degenerate stratum below the target). -/
theorem near_degenerate_below (μ : ℝ) : (2 * μ + 1 < μ + 4 / 3) ↔ (μ < 1 / 3) := by
  constructor <;> intro h <;> linarith

/-- `μ+1 < μ+4/3` (exact-diagonal and degenerate strata, unconditional). -/
theorem exact_diagonal_below (μ : ℝ) : μ + 1 < μ + 4 / 3 := by linarith

/-- `2μ+1/3 < μ+4/3 ↔ μ < 1` (divisibility-pinned stratum). -/
theorem divisibility_pinned_below (μ : ℝ) :
    (2 * μ + 1 / 3 < μ + 4 / 3) ↔ (μ < 1) := by
  constructor <;> intro h <;> linarith

/-! ## P1 generic deficit (§7, §12). -/

/-- `P1_GENERIC_DEFICIT`: `(3μ+2) − (μ+4/3) = 2μ+2/3`. -/
theorem p1_generic_deficit (μ : ℝ) : (3 * μ + 2) - (μ + 4 / 3) = 2 * μ + 2 / 3 := by
  ring

/-! ## Square-root-wall route deficits (§14) — exponent arithmetic only. -/

/-- `BALANCED_P1_DEFICIT` value `2μ+2/3`. -/
noncomputable def p1Deficit (μ : ℝ) : ℝ := 2 * μ + 2 / 3
/-- `BALANCED_P2_DEFICIT` value `μ+1/3`. -/
noncomputable def p2Deficit (μ : ℝ) : ℝ := μ + 1 / 3
/-- `BALANCED_P3_DEFICIT` per-tuple value `1/12 + 3μ/4`. -/
noncomputable def p3Deficit (μ : ℝ) : ℝ := 1 / 12 + 3 * μ / 4
/-- `BALANCED_ADDITIVE_DIVISOR_SURPLUS` value `4μ/3`. -/
noncomputable def additiveDivisorSurplus (μ : ℝ) : ℝ := 4 * μ / 3

/-- `P3` deficit identity (§27.9):
`(5/12 − μ/4) − (1/3 − μ) = 1/12 + 3μ/4`. -/
theorem p3_deficit_identity (μ : ℝ) :
    (5 / 12 - μ / 4) - (1 / 3 - μ) = 1 / 12 + 3 * μ / 4 := by ring

theorem p3_deficit_eq (μ : ℝ) :
    (5 / 12 - μ / 4) - (1 / 3 - μ) = p3Deficit μ := by unfold p3Deficit; ring

/-- `BALANCED_P4_SATURATION`: available `8/3` strictly exceeds required `8/3 − δ`
for `δ > 0`. -/
theorem p4_saturation_gap (δ : ℝ) (hδ : 0 < δ) : 8 / 3 - δ < 8 / 3 := by linarith

/-! ## Localization conditional consequence (§13). -/

/-- Third-term exponent under the `Ξ_gen` hypothesis `|Ξ| ≤ X^{μ+4/3−δ}`:
`X^{μ/2+1/3} · Ξ^{1/2} ≤ X^{μ+1−δ/2}`. -/
theorem localization_third_term
    (X μ δ Xi : ℝ) (hX : 1 ≤ X) (hXinn : 0 ≤ Xi)
    (hXi : Xi ≤ X ^ (μ + 4 / 3 - δ)) :
    X ^ (μ / 2 + 1 / 3) * Xi ^ (1 / 2 : ℝ) ≤ X ^ (μ + 1 - δ / 2) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have h1 : Xi ^ (1 / 2 : ℝ) ≤ (X ^ (μ + 4 / 3 - δ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hXinn hXi (by norm_num)
  have h2 : (X ^ (μ + 4 / 3 - δ)) ^ (1 / 2 : ℝ) = X ^ ((μ + 4 / 3 - δ) / 2) := by
    rw [← Real.rpow_mul (le_of_lt hX0)]; ring_nf
  have h3 : X ^ (μ / 2 + 1 / 3) * X ^ ((μ + 4 / 3 - δ) / 2) = X ^ (μ + 1 - δ / 2) := by
    rw [← Real.rpow_add hX0]; ring_nf
  calc X ^ (μ / 2 + 1 / 3) * Xi ^ (1 / 2 : ℝ)
      ≤ X ^ (μ / 2 + 1 / 3) * (X ^ (μ + 4 / 3 - δ)) ^ (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.rpow_pos_of_pos hX0 _))
    _ = X ^ (μ + 1 - δ / 2) := by rw [h2, h3]

/-- `PRIMITIVE_FORM_C_LOCALIZATION`, conditional consequence (§13).

If the (provisional) localization bound holds and `|Ξ_gen| ≤ X^{μ+4/3−δ}`, then
`|𝔠_prim|` is bounded by the two structural terms plus `X^{μ+1−δ/2}`.  The
localization inequality is a *hypothesis* (`hloc`), never an axiom.

Status: `LEAN_PROVED_CORE` (arithmetic; analytic inputs are hypotheses). -/
theorem primitive_formC_localization_conditional
    (X μ δ Xi Cprim : ℝ) (hX : 1 ≤ X) (hXinn : 0 ≤ Xi)
    (hXi : Xi ≤ X ^ (μ + 4 / 3 - δ))
    (hloc : Cprim ≤ X ^ (μ + 5 / 6) + X ^ (3 * μ / 2 + 5 / 6)
              + X ^ (μ / 2 + 1 / 3) * Xi ^ (1 / 2 : ℝ)) :
    Cprim ≤ X ^ (μ + 5 / 6) + X ^ (3 * μ / 2 + 5 / 6) + X ^ (μ + 1 - δ / 2) := by
  have hthird := localization_third_term X μ δ Xi hX hXinn hXi
  linarith [hloc, hthird]

/-- All three localization exponents lie strictly below the target `μ+1`, for
`0 < μ < 1/3` and `δ > 0`.  This is the "final admissible saving" bookkeeping. -/
theorem localization_exponents_below_target
    (μ δ : ℝ) (hμ0 : 0 < μ) (hμ : μ < 1 / 3) (hδ : 0 < δ) :
    μ + 5 / 6 < μ + 1 ∧ 3 * μ / 2 + 5 / 6 < μ + 1 ∧ μ + 1 - δ / 2 < μ + 1 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## Fourth-moment conditional saving (§16). -/

/-- Abstract Cauchy–Schwarz for a continuous linear operator on a real inner
product space: `|⟨Kv, v⟩| ≤ ‖v‖² ‖K‖`.  `LEAN_PROVED`. -/
theorem operator_quadratic_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : E →L[ℝ] E) (v : E) :
    |(inner ℝ (K v) v : ℝ)| ≤ ‖v‖ ^ 2 * ‖K‖ := by
  calc |(inner ℝ (K v) v : ℝ)| ≤ ‖K v‖ * ‖v‖ := abs_real_inner_le_norm (K v) v
    _ ≤ (‖K‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (K.le_opNorm v) (norm_nonneg v)
    _ = ‖v‖ ^ 2 * ‖K‖ := by ring

/-- `PRIMITIVE_FOURTH_MOMENT_SAVING`, conditional consequence (§16).

Given the operator-fourth-moment inequality `‖K‖⁴ ≤ tr((KK*)²)` (as hypothesis
`h1`) and the (open) fourth-moment saving `tr((KK*)²) ≤ X^{8/3−δ}` (hypothesis
`h2`), the operator norm satisfies `‖K‖ ≤ X^{2/3 − δ/4}`.

Status: `LEAN_PROVED_CORE` (arithmetic; analytic inputs are hypotheses). -/
theorem fourth_moment_operator_saving
    (X nK tr δ : ℝ) (hX : 1 ≤ X)
    (h1 : nK ^ 4 ≤ tr) (h2 : tr ≤ X ^ (8 / 3 - δ)) :
    nK ≤ X ^ (2 / 3 - δ / 4) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hpow : (X ^ (2 / 3 - δ / 4)) ^ 4 = X ^ (8 / 3 - δ) := by
    rw [← Real.rpow_natCast (X ^ (2 / 3 - δ / 4)) 4, ← Real.rpow_mul (le_of_lt hX0)]
    congr 1; push_cast; ring
  have hb : nK ^ 4 ≤ (X ^ (2 / 3 - δ / 4)) ^ 4 := by rw [hpow]; linarith
  exact le_of_pow_le_pow_left₀ (by norm_num)
    (le_of_lt (Real.rpow_pos_of_pos hX0 _)) hb

end Banking.Deficit
