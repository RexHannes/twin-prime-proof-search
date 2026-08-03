import Mathlib

/-!
# Spectral criticality: singular-value lower bound (§6)

`SHORT_WINDOW_SINGULAR_VALUE_LOWER_BOUND`.

The linear-algebra content of §6 is the elementary singular-value energy
inequality: if `σ₁, …, σ_r` are the singular values of a matrix `A` (so that
`‖A‖_HS² = ∑ σ_j²` and `‖A‖_op = max_j σ_j`), then

`‖A‖_op ≥ ‖A‖_HS / √(rank A)`.

We prove the underlying real-analysis inequalities unconditionally
(`sum_sq_le_card_mul_sq`, `op_ge_hs_div_sqrt_card`), bundle the SVD data of a
matrix into `SpectralData` (whose two identities `‖A‖_HS² = ∑ σ²` and
`σ_j ≤ ‖A‖_op` are the *separate* analytic/SVD input, exactly as required by the
brief), and derive both the clean bound `op ≥ hs / √rank`
(`SpectralData.op_ge_hs_div_sqrt_rank`) and the calibrated consequence
`op ≥ √c · p / √Q` from `hs² ≥ c p²` and `rank ≤ Q`
(`short_window_singular_value_lower_bound`).

Status: `LEAN_PROVED` (linear-algebra core).  The Hilbert–Schmidt hypothesis
`‖A‖_HS² ≥ c p²` for the Kloosterman matrix is a *separate* analytic input,
tracked as `ARBITRARY_LAMBDA_SW_SPECTRALLY_CRITICAL_INTERIOR` in the ledger.
-/

open scoped BigOperators

namespace PrimeShortWindow.Spectral

/-- Energy bound: the sum of squares of nonnegative reals bounded by `op` is at
most `(card) · op²`. -/
theorem sum_sq_le_card_mul_sq {ι} [Fintype ι] (σ : ι → ℝ) (op : ℝ)
    (hop : ∀ j, σ j ≤ op) (hσ : ∀ j, 0 ≤ σ j) :
    ∑ j, (σ j) ^ 2 ≤ (Fintype.card ι) * op ^ 2 := by
  calc ∑ j, (σ j) ^ 2 ≤ ∑ _j : ι, op ^ 2 := by
          apply Finset.sum_le_sum; intro j _; nlinarith [hop j, hσ j]
    _ = (Fintype.card ι) * op ^ 2 := by rw [Finset.sum_const, Finset.card_univ]; ring

/-- Operator-norm lower bound in terms of singular values:
`√(∑ σ_j²) / √(card) ≤ op` where `op = max σ_j`. -/
theorem op_ge_hs_div_sqrt_card {ι} [Fintype ι] [Nonempty ι] (σ : ι → ℝ) (op : ℝ)
    (hop : ∀ j, σ j ≤ op) (hσ : ∀ j, 0 ≤ σ j) :
    Real.sqrt (∑ j, (σ j) ^ 2) / Real.sqrt (Fintype.card ι) ≤ op := by
  have hop0 : 0 ≤ op := le_trans (hσ (Classical.arbitrary ι)) (hop (Classical.arbitrary ι))
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hcard)]
  calc Real.sqrt (∑ j, (σ j) ^ 2) ≤ Real.sqrt ((Fintype.card ι) * op ^ 2) :=
        Real.sqrt_le_sqrt (sum_sq_le_card_mul_sq σ op hop hσ)
    _ = Real.sqrt (Fintype.card ι) * op := by
        rw [Real.sqrt_mul (le_of_lt hcard), Real.sqrt_sq hop0]
    _ = op * Real.sqrt (Fintype.card ι) := by ring

/-- Singular-value decomposition data of a matrix (the analytic/SVD input):
`σ` are the `r = rank` nonzero singular values, `hs = ‖A‖_HS`, `op = ‖A‖_op`,
with the two SVD identities `hs² = ∑ σ_j²` and `σ_j ≤ op`. -/
structure SpectralData (r : ℕ) where
  σ : Fin r → ℝ
  σ_nonneg : ∀ j, 0 ≤ σ j
  hs : ℝ
  op : ℝ
  hs_nonneg : 0 ≤ hs
  /-- `‖A‖_HS² = ∑ σ_j²` (SVD input). -/
  hs_sq_eq : hs ^ 2 = ∑ j, (σ j) ^ 2
  /-- `‖A‖_op = max_j σ_j`, in particular each `σ_j ≤ ‖A‖_op` (SVD input). -/
  op_ge : ∀ j, σ j ≤ op

/-- The banked spectral bound `op ≥ hs / √rank`. -/
theorem SpectralData.op_ge_hs_div_sqrt_rank {r : ℕ} (hr : 0 < r) (D : SpectralData r) :
    D.hs / Real.sqrt r ≤ D.op := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hcard : (Fintype.card (Fin r) : ℝ) = r := by simp
  have h := op_ge_hs_div_sqrt_card D.σ D.op D.op_ge D.σ_nonneg
  rw [hcard] at h
  have : Real.sqrt (∑ j, (D.σ j) ^ 2) = D.hs := by
    rw [← D.hs_sq_eq, Real.sqrt_sq D.hs_nonneg]
  rwa [this] at h

/-- **SHORT_WINDOW_SINGULAR_VALUE_LOWER_BOUND.**  If the Hilbert–Schmidt energy
is `≥ c p²` and the rank is `≤ Q`, then the operator norm is `≥ √c · p / √Q`. -/
theorem short_window_singular_value_lower_bound {r : ℕ} (hr : 0 < r) (D : SpectralData r)
    (p Q c : ℝ) (hp : 0 ≤ p) (hc : 0 ≤ c) (hQ : 0 < Q)
    (hHS : c * p ^ 2 ≤ D.hs ^ 2) (hrank : (r : ℝ) ≤ Q) :
    Real.sqrt c * p / Real.sqrt Q ≤ D.op := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hbound := D.op_ge_hs_div_sqrt_rank hr
  -- `hs ≥ √c · p`
  have hhs_lb : Real.sqrt c * p ≤ D.hs := by
    have : Real.sqrt (c * p ^ 2) ≤ D.hs := by
      rw [← Real.sqrt_sq D.hs_nonneg]; exact Real.sqrt_le_sqrt hHS
    rwa [Real.sqrt_mul hc, Real.sqrt_sq hp] at this
  have hcp0 : 0 ≤ Real.sqrt c * p := mul_nonneg (Real.sqrt_nonneg c) hp
  -- `√r ≤ √Q`
  have hsqrt_le : Real.sqrt r ≤ Real.sqrt Q := Real.sqrt_le_sqrt hrank
  have hsr_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
  have hsq_pos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  calc Real.sqrt c * p / Real.sqrt Q
      ≤ Real.sqrt c * p / Real.sqrt r := by gcongr
    _ ≤ D.hs / Real.sqrt r := by gcongr
    _ ≤ D.op := hbound

end PrimeShortWindow.Spectral
