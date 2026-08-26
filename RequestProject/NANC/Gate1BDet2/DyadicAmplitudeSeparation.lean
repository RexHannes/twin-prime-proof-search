import RequestProject.NANC.Gate1BDet2.SmallMeasureCorrelation

/-!
# Gate 1B / determinant-2 bank, Module 8 (Phase B): dyadic amplitude separation

Deterministic, purely measure-theoretic content underlying the amplitude
layering of the minor-spectrum reduction.  No number theory, and **no** PMS45
claim is made.

For `F` with `∫ ‖F‖² ≤ 1` the dyadic amplitude layers

  `E_j(F) = {x : 2^j < ‖F x‖ ≤ 2^(j+1)}`

satisfy the Chebyshev bound `μ(E_j(F)) ≤ 2^(-2j)`, and two layers of two such
functions correlate at most like `4 · 2^(-|j-k|)`.

## Note on the tail statement

Summing `2^(-|j-k|)` over *all* pairs `(j,k) ∈ ℤ × ℤ` with `|j-k| ≥ L` diverges
(each difference class is infinite).  The honest deterministic tail statement is
therefore the one proved below, over a *finite* index family of layer pairs,
with the explicit constant `C' = 4 · (number of pairs)`; the underlying scalar
geometric series `∑_{d ≥ L} 4 · 2^(-d) = 8 · 2^(-L)` is banked separately.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

open MeasureTheory ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The dyadic amplitude layer `E_j(F) = {x : 2^j < ‖F x‖ ≤ 2^(j+1)}`. -/
def ampLayer (F : X → ℂ) (j : ℤ) : Set X :=
  {x | (2 : ℝ) ^ j < ‖F x‖ ∧ ‖F x‖ ≤ (2 : ℝ) ^ (j + 1)}

theorem measurableSet_ampLayer {F : X → ℂ} (hF : Measurable F) (j : ℤ) :
    MeasurableSet (ampLayer F j) := by
  have h : Measurable fun x => ‖F x‖ := hF.norm
  exact (measurableSet_lt measurable_const h).inter (measurableSet_le h measurable_const)

/-! ## 1. Chebyshev bound for a single layer -/

/-- **Chebyshev layer bound (`ℝ≥0∞` form).**  If `∫ ‖F‖² ≤ 1` then
`μ(E_j(F)) ≤ 2^(-2j)`. -/
theorem measure_ampLayer_le {mu : Measure X} {F : X → ℂ} (hFm : Measurable F)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂mu ≤ 1) (j : ℤ) :
    mu (ampLayer F j) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-2 * j)) := by
  have hc : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hSm : MeasurableSet (ampLayer F j) := measurableSet_ampLayer hFm j
  have hpt : ∀ x ∈ ampLayer F j,
      ENNReal.ofReal (((2 : ℝ) ^ j) ^ 2) ≤ ‖F x‖ₑ ^ 2 := by
    intro x hx
    have h1 : (2 : ℝ) ^ j ≤ ‖F x‖ := hx.1.le
    have h2 : ENNReal.ofReal ((2 : ℝ) ^ j) ≤ ‖F x‖ₑ := by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal h1
    calc ENNReal.ofReal (((2 : ℝ) ^ j) ^ 2)
        = (ENNReal.ofReal ((2 : ℝ) ^ j)) ^ 2 := ENNReal.ofReal_pow hc.le 2
      _ ≤ ‖F x‖ₑ ^ 2 := by gcongr
  have key : ENNReal.ofReal (((2 : ℝ) ^ j) ^ 2) * mu (ampLayer F j) ≤ 1 := by
    calc ENNReal.ofReal (((2 : ℝ) ^ j) ^ 2) * mu (ampLayer F j)
        = ∫⁻ _ in ampLayer F j, ENNReal.ofReal (((2 : ℝ) ^ j) ^ 2) ∂mu :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in ampLayer F j, ‖F x‖ₑ ^ 2 ∂mu := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hSm]
          exact Filter.Eventually.of_forall hpt
      _ ≤ ∫⁻ x, ‖F x‖ₑ ^ 2 ∂mu := setLIntegral_le_lintegral _ _
      _ ≤ 1 := hF
  have hinv : mu (ampLayer F j) ≤ (ENNReal.ofReal (((2 : ℝ) ^ j) ^ 2))⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]; rwa [mul_comm] at key
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ j) ^ 2 := by positivity
  have hrew : (ENNReal.ofReal (((2 : ℝ) ^ j) ^ 2))⁻¹
      = ENNReal.ofReal ((2 : ℝ) ^ (-2 * j)) := by
    rw [← ENNReal.ofReal_inv_of_pos hpos]
    congr 1
    rw [← zpow_natCast ((2:ℝ) ^ j) 2, ← zpow_mul, ← zpow_neg]
    norm_num [mul_comm]
  rwa [hrew] at hinv

/-- The layer has finite measure. -/
theorem measure_ampLayer_ne_top {mu : Measure X} {F : X → ℂ} (hFm : Measurable F)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂mu ≤ 1) (j : ℤ) : mu (ampLayer F j) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (measure_ampLayer_le hFm hF j)

/-- **Chebyshev layer bound (real form).** -/
theorem measureReal_ampLayer_le {mu : Measure X} {F : X → ℂ} (hFm : Measurable F)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂mu ≤ 1) (j : ℤ) :
    mu.real (ampLayer F j) ≤ (2 : ℝ) ^ (-2 * j) :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (measure_ampLayer_le hFm hF j)

/-! ## 2. Correlation of two amplitude layers -/

/-- **Amplitude-unbalanced layers are negligible.**  For `F, G` with
`∫ ‖F‖² ≤ 1`, `∫ ‖G‖² ≤ 1`,

  `‖∫_{E_j(F) ∩ E_k(G)} F · conj G‖ ≤ 4 · 2^(-|j-k|)`. -/
theorem layer_correlation_bound {mu : Measure X} {F G : X → ℂ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂mu ≤ 1) (hG : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂mu ≤ 1) (j k : ℤ) :
    ‖∫ x in ampLayer F j ∩ ampLayer G k, F x * (starRingEnd ℂ) (G x) ∂mu‖
      ≤ 4 * (2 : ℝ) ^ (-|j - k|) := by
  set E := ampLayer F j ∩ ampLayer G k with hE
  have hfin : mu E < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (lt_top_iff_ne_top.mpr (measure_ampLayer_ne_top hFm hF j))
  have hA : ∀ x ∈ E, ‖F x‖ ≤ (2 : ℝ) ^ (j + 1) := fun x hx => hx.1.2
  have hB : ∀ x ∈ E, ‖G x‖ ≤ (2 : ℝ) ^ (k + 1) := fun x hx => hx.2.2
  have hmain := norm_setIntegral_mul_conj_le hfin hA hB
  -- the amplitude product
  have hprod : (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (k + 1) = 4 * (2 : ℝ) ^ (j + k) := by
    rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    rw [show j + 1 + (k + 1) = (j + k) + 2 by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    norm_num [mul_comm]
  rcases le_total j k with hjk | hjk
  · have hlayer : mu.real E ≤ (2 : ℝ) ^ (-2 * k) := by
      refine le_trans ?_ (measureReal_ampLayer_le hGm hG k)
      exact measureReal_mono Set.inter_subset_right (measure_ampLayer_ne_top hGm hG k)
    have habs : -|j - k| = (-2 * k) + (j + k) := by
      rw [abs_of_nonpos (by omega : j - k ≤ 0)]; ring
    calc ‖∫ x in E, F x * (starRingEnd ℂ) (G x) ∂mu‖
        ≤ mu.real E * ((2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (k + 1)) := hmain
      _ = mu.real E * (4 * (2 : ℝ) ^ (j + k)) := by rw [hprod]
      _ ≤ (2 : ℝ) ^ (-2 * k) * (4 * (2 : ℝ) ^ (j + k)) := by
          have : (0:ℝ) ≤ 4 * (2 : ℝ) ^ (j + k) := by positivity
          exact mul_le_mul_of_nonneg_right hlayer this
      _ = 4 * ((2 : ℝ) ^ (-2 * k) * (2 : ℝ) ^ (j + k)) := by ring
      _ = 4 * (2 : ℝ) ^ (-2 * k + (j + k)) := by
          rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      _ = 4 * (2 : ℝ) ^ (-|j - k|) := by rw [← habs]
  · have hlayer : mu.real E ≤ (2 : ℝ) ^ (-2 * j) := by
      refine le_trans ?_ (measureReal_ampLayer_le hFm hF j)
      exact measureReal_mono Set.inter_subset_left (measure_ampLayer_ne_top hFm hF j)
    have habs : -|j - k| = (-2 * j) + (j + k) := by
      rw [abs_of_nonneg (by omega : 0 ≤ j - k)]; ring
    calc ‖∫ x in E, F x * (starRingEnd ℂ) (G x) ∂mu‖
        ≤ mu.real E * ((2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (k + 1)) := hmain
      _ = mu.real E * (4 * (2 : ℝ) ^ (j + k)) := by rw [hprod]
      _ ≤ (2 : ℝ) ^ (-2 * j) * (4 * (2 : ℝ) ^ (j + k)) := by
          have : (0:ℝ) ≤ 4 * (2 : ℝ) ^ (j + k) := by positivity
          exact mul_le_mul_of_nonneg_right hlayer this
      _ = 4 * ((2 : ℝ) ^ (-2 * j) * (2 : ℝ) ^ (j + k)) := by ring
      _ = 4 * (2 : ℝ) ^ (-2 * j + (j + k)) := by
          rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      _ = 4 * (2 : ℝ) ^ (-|j - k|) := by rw [← habs]

/-! ## 3. Geometric tail -/

/-- **Scalar geometric tail.**  `∑_{d = L}^{∞} 4 · 2^(-d) = 8 · 2^(-L)`. -/
theorem geometric_tail (L : ℕ) :
    ∑' d : ℕ, 4 * (2 : ℝ) ^ (-(L + d : ℤ)) = 8 * (2 : ℝ) ^ (-(L : ℤ)) := by
  have hsum : ∑' d : ℕ, ((1:ℝ)/2) ^ d = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hterm : ∀ d : ℕ, 4 * (2 : ℝ) ^ (-(L + d : ℤ))
      = (4 * (2 : ℝ) ^ (-(L : ℤ))) * ((1:ℝ)/2) ^ d := by
    intro d
    have e1 : (2 : ℝ) ^ (-(L + d : ℤ)) = (2 : ℝ) ^ (-(L : ℤ)) * (2 : ℝ) ^ (-(d : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      congr 1
      ring
    have e2 : (2 : ℝ) ^ (-(d : ℤ)) = ((1:ℝ)/2) ^ d := by
      rw [one_div, inv_pow, zpow_neg, zpow_natCast]
    rw [e1, e2]
    ring
  calc ∑' d : ℕ, 4 * (2 : ℝ) ^ (-(L + d : ℤ))
      = ∑' d : ℕ, (4 * (2 : ℝ) ^ (-(L : ℤ))) * ((1:ℝ)/2) ^ d := by
        exact tsum_congr hterm
    _ = (4 * (2 : ℝ) ^ (-(L : ℤ))) * ∑' d : ℕ, ((1:ℝ)/2) ^ d := by
        rw [tsum_mul_left]
    _ = 8 * (2 : ℝ) ^ (-(L : ℤ)) := by rw [hsum]; ring

/-- **Finite amplitude-unbalanced tail.**  Over a *finite* family `S` of layer
pairs, all of which are amplitude-unbalanced by at least `L`, the total
correlation mass is at most `C' · 2^(-L)` with the explicit constant
`C' = 4 · |S|`. -/
theorem layer_tail_bound {mu : Measure X} {F G : X → ℂ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂mu ≤ 1) (hG : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂mu ≤ 1)
    (L : ℤ) (S : Finset (ℤ × ℤ)) (hS : ∀ p ∈ S, L ≤ |p.1 - p.2|) :
    ∑ p ∈ S, ‖∫ x in ampLayer F p.1 ∩ ampLayer G p.2,
        F x * (starRingEnd ℂ) (G x) ∂mu‖
      ≤ (4 * S.card) * (2 : ℝ) ^ (-L) := by
  have hbound : ∀ p ∈ S, ‖∫ x in ampLayer F p.1 ∩ ampLayer G p.2,
      F x * (starRingEnd ℂ) (G x) ∂mu‖ ≤ 4 * (2 : ℝ) ^ (-L) := by
    intro p hp
    refine le_trans (layer_correlation_bound hFm hGm hF hG p.1 p.2) ?_
    have : (2 : ℝ) ^ (-|p.1 - p.2|) ≤ (2 : ℝ) ^ (-L) :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (neg_le_neg (hS p hp))
    linarith
  calc ∑ p ∈ S, ‖∫ x in ampLayer F p.1 ∩ ampLayer G p.2,
        F x * (starRingEnd ℂ) (G x) ∂mu‖
      ≤ ∑ _p ∈ S, 4 * (2 : ℝ) ^ (-L) := Finset.sum_le_sum hbound
    _ = (4 * S.card) * (2 : ℝ) ^ (-L) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end Gate1BDet2
end TwinPrimeProject
