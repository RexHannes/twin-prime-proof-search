/-
# NANC Gate 1A v9 — PMLS / GPMLS normalization bridge (finite, symbolic)

Two independent pieces, both exact:

* `outerP_cauchy` — if `tildeC e = ∑_p b_p · U e p` and `∑_p |b_p|² ≤ L·B`, then

      ∑_e |tildeC e|² ≤ L·B·∑_{e,p} |U e p|².

  This reuses the already-banked finite Cauchy–Schwarz inequality
  `Gate1B.SafeExtensions.physicalOuterCauchy`; no new analytic input.

* the **symbolic budget bridge** — exact identities between the abstract
  nonnegative budget parameters `H, L, M`:

      fixed-(r,k) target      = H·L³
      global GPMLS target     = M·H·L³
      outer-p Cauchy cost     = L
      normalized covariance   = M·H·L⁴
      physical H⁻¹ squares to H⁻²
      physical target         = M·L⁴/H.

**FIREWALL.**  No asymptotic theorem, no `X^{o(1)}`, and no bound on any actual
Gate source is proved here: `L, B, H, M` are free nonnegative parameters.
-/
import Gate1B.SafeExtensions.PhysicalSecondMoment

namespace TwinPrimeProject.NANC.Gate1A.V9

open Finset

/-- **Outer-`p` Cauchy step.**  Exact finite inequality for a source of the form
`tildeC e = ∑_p b_p · U e p` with `p`-mass at most `L·B`. -/
theorem outerP_cauchy {E P : Type*} (sE : Finset E) (sP : Finset P)
    (b : P → ℂ) (U : E → P → ℂ) (L B : ℝ)
    (hb : ∑ p ∈ sP, ‖b p‖ ^ 2 ≤ L * B) :
    ∑ e ∈ sE, ‖∑ p ∈ sP, b p * U e p‖ ^ 2
      ≤ L * B * ∑ e ∈ sE, ∑ p ∈ sP, ‖U e p‖ ^ 2 := by
  have hterm : ∀ e ∈ sE, ‖∑ p ∈ sP, b p * U e p‖ ^ 2
      ≤ L * B * ∑ p ∈ sP, ‖U e p‖ ^ 2 := by
    intro e _
    have hcs := Gate1B.SafeExtensions.physicalOuterCauchy sP b (fun p => U e p)
    have hU : (0 : ℝ) ≤ ∑ p ∈ sP, ‖U e p‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact hcs.trans (mul_le_mul_of_nonneg_right hb hU)
  calc ∑ e ∈ sE, ‖∑ p ∈ sP, b p * U e p‖ ^ 2
      ≤ ∑ e ∈ sE, L * B * ∑ p ∈ sP, ‖U e p‖ ^ 2 := Finset.sum_le_sum hterm
    _ = L * B * ∑ e ∈ sE, ∑ p ∈ sP, ‖U e p‖ ^ 2 := by rw [Finset.mul_sum]

/-- Fixed-`(r,k)` PMLS target. -/
def pmlsFixedTarget (H L : ℝ) : ℝ := H * L ^ 3

/-- Global GPMLS target (one factor `M` for the `m`-family). -/
def gpmlsGlobalTarget (M H L : ℝ) : ℝ := M * H * L ^ 3

/-- Normalized covariance target after paying the outer-`p` Cauchy cost `L`. -/
def gpmlsNormalizedTarget (M H L : ℝ) : ℝ := M * H * L ^ 4

/-- Physical target after the `H⁻¹` normalization, whose square is `H⁻²`. -/
noncomputable def gpmlsPhysicalTarget (M H L : ℝ) : ℝ := M * L ^ 4 / H

/-- **PMLS → normalized gate budget.**  The global target times the outer-`p`
Cauchy cost `L` is exactly the normalized covariance target. -/
theorem pmls_to_normalizedGateBudget (M H L : ℝ) :
    gpmlsGlobalTarget M H L * L = gpmlsNormalizedTarget M H L := by
  unfold gpmlsGlobalTarget gpmlsNormalizedTarget; ring

/-- The global target is `M` copies of the fixed-`(r,k)` target. -/
theorem gpmls_global_eq_M_mul_fixed (M H L : ℝ) :
    gpmlsGlobalTarget M H L = M * pmlsFixedTarget H L := by
  unfold gpmlsGlobalTarget pmlsFixedTarget; ring

/-- **GPMLS → physical gate budget.**  The physical `H⁻¹` normalization squares
to `H⁻²`, turning the normalized target `M·H·L⁴` into `M·L⁴/H`. -/
theorem gpmls_to_physicalGateBudget (M H L : ℝ) (hH : H ≠ 0) :
    gpmlsNormalizedTarget M H L * (1 / H) ^ 2 = gpmlsPhysicalTarget M H L := by
  unfold gpmlsNormalizedTarget gpmlsPhysicalTarget
  field_simp

end TwinPrimeProject.NANC.Gate1A.V9
