import RequestProject.NANC.Gate01Consolidation.AnalyticInterfaces
import RequestProject.NANC.Gate01Consolidation.ProductModeObstruction

/-!
# Overclaim kill tests

Compile-time propositions making explicit that none of the banked finite
identities implies any analytic conclusion.  Each kill is a *proved* statement:
either an explicit counterexample, or a display of the exact extra hypothesis
that a conclusion needs.

* **Kill 1** — E-separation does not bound anything: with the zero mode exactly
  zero, the centered progression mass can still be arbitrarily large
  (`kill1_eseparation_gives_no_bound`).
* **Kill 2** — CRT-CENTER does not make the double-centered mode small: at
  `y = 0` the mixed mode equals `(1−1/d)(1−1/p)`, bounded away from `0`
  (`kill2_crt_center_gives_no_smallness`).
* **Kill 3** — vanishing one-coordinate projections do not kill the mixed mode
  (`zero_projections_not_imply_zero_mixed_mode`, BANK J).
* **Kill 4** — the `4|5` variables lying above `√Q` does not bound the
  dispersion (`kill4_threshold_gives_no_dispersion_bound`).
* **Kill 5** — the direct Gauss reassembly identity does not bound the phase
  sum (`kill5_gauss_identity_gives_no_bound`).

None of these is a no-go theorem for the corresponding analytic estimate; they
refute only the *formal implications*.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-- **Kill 1.**  From E-separation alone (even with the zero mode exactly zero)
no bound on `C_q − E` follows: for every target size `M` there are finite data
with vanishing zero mode and `‖C_q − E‖ = M`. -/
theorem kill1_eseparation_gives_no_bound (M : ℝ) (hM : 0 ≤ M) :
    ∃ (S : Finset ℕ) (q : ℕ) (c : ℕ → ℂ) (E : ℂ),
      0 < q ∧ fullSum S c / (q : ℂ) - E = 0 ∧ ‖congrSum S q c - E‖ = M := by
  refine ⟨{0, 1}, 2, fun x => if x = 0 then (M : ℂ) else -(M : ℂ), 0, by norm_num, ?_, ?_⟩
  · unfold fullSum
    norm_num
  · have hfil : ({0, 1} : Finset ℕ).filter (fun x => 2 ∣ x + 2) = {0} := by decide
    rw [congrSum, hfil]
    simp [abs_of_nonneg hM]

/-- **Kill 2.**  The CRT centering identity gives no smallness: at `y = 0` the
double-centered mixed mode is `(1 − 1/d)(1 − 1/p)`, which for `d, p ≥ 2` is at
least `1/4`. -/
theorem kill2_crt_center_gives_no_smallness {d p : ℕ} (hd : 2 ≤ d) (hp : 2 ≤ p) :
    rho d 0 * rho p 0 = (1 - 1 / (d : ℝ)) * (1 - 1 / (p : ℝ)) ∧
      1 / 4 ≤ rho d 0 * rho p 0 := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hdpos : (0 : ℝ) < d := by linarith
  have hppos : (0 : ℝ) < p := by linarith
  have hval : rho d 0 * rho p 0 = (1 - 1 / (d : ℝ)) * (1 - 1 / (p : ℝ)) := by
    unfold rho
    simp
  refine ⟨hval, ?_⟩
  rw [hval]
  have h1 : 1 / (d : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hd0
  have h2 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp0
  nlinarith [one_div_pos.mpr hdpos, one_div_pos.mpr hppos]

/-- **Kill 4.**  The threshold facts `√Q < X^{4/9}`, `√Q < X^{5/9}` say nothing
about the size of the dispersion: for every `M` there are finite data whose
`4|5` dispersion has absolute value `M`, while the threshold inequalities hold
unconditionally. -/
theorem kill4_threshold_gives_no_dispersion_bound (M : ℝ) (hM : 0 ≤ M) :
    (expSqrtQ < expU ∧ expSqrtQ < expV) ∧
    ∃ (Qset Uset Vset : Finset ℕ) (xi a b MT : ℕ → ℝ),
      |fourFiveDispersion Qset Uset Vset xi a b MT| = M := by
  refine ⟨fourFive_crosses_completion_threshold,
    {1}, {1}, {1}, fun _ => M, fun _ => 1, fun _ => 1, fun _ => 0, ?_⟩
  unfold fourFiveDispersion
  norm_num [abs_of_nonneg hM]

/-- **Kill 5.**  The Gauss reassembly identity removes the characters but bounds
nothing: a family of unit-modulus physical phases can have phase sum of size
exactly `n`. -/
theorem kill5_gauss_identity_gives_no_bound (n : ℕ) :
    ∃ (F : Finset ℕ) (phase : ℕ → ℂ),
      (∀ i ∈ F, ‖phase i‖ = 1) ∧ ‖∑ i ∈ F, phase i‖ = (n : ℝ) := by
  refine ⟨Finset.range n, fun _ => 1, fun i _ => by simp, ?_⟩
  simp

end Gate01Consolidation
end TwinPrimeProject
