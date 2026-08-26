/-
# Gate 1B v8.2 — capacity budget compilers

Deterministic compilers: each theorem takes an analytic estimate **as an
explicit hypothesis** and returns the corresponding budget conclusion.  No
compiler inhabits its own hypothesis, and no compiler is applied to a
constructed inhabitant anywhere in this project.
-/
import Mathlib
import Gate1B.SafeAlgebra.QK5CapacityMargins
import Gate1B.SafeAlgebra.GBetaSourceMassCapacity

namespace Gate1B.SafeExtensions

open Gate1B.SafeAlgebra

/-- **PV medium-range budget compiler.**  Given the analytic estimate
`S ≤ C² Y⁵ / Q` and the exponent check `C² Y⁵ / Q ≤ budget`, the source is
bounded by the recorded budget. -/
theorem pvMedium_of_analyticHyp {S C Y Q budget : ℝ}
    (hanalytic : S ≤ C ^ 2 * Y ^ 5 / Q)
    (hbudget : C ^ 2 * Y ^ 5 / Q ≤ budget) : S ≤ budget :=
  hanalytic.trans hbudget

/-- **Overlap budget compiler.**  If the source splits into a large-sieve part
and a PV part, each within its recorded budget, the total is within the sum. -/
theorem overlap_of_ls_and_pv_hypotheses {S S_LS S_PV bLS bPV : ℝ}
    (hsplit : S = S_LS + S_PV) (hLS : S_LS ≤ bLS) (hPV : S_PV ≤ bPV) :
    S ≤ bLS + bPV := by
  rw [hsplit]
  exact add_le_add hLS hPV

/-- **Axis budget compiler.**  An axis bound with the recorded exponent yields
the axis budget. -/
theorem axisBudget_of_axisBound {S T X : ℝ} (haxis : S ≤ T)
    (hT : T ≤ X ^ ((axisBudgetExponent : ℚ) : ℝ)) :
    S ≤ X ^ ((axisBudgetExponent : ℚ) : ℝ) := haxis.trans hT

/-- **GCD budget compiler.**  Per-stratum source-mass bounds plus a Schur row
budget give the stratified total. -/
theorem gcdBudget_of_sourceMassAndSchur {ι : Type*} (s : Finset ι) (m : ι → ℝ) (b : ℝ)
    (hm : ∀ i ∈ s, m i ≤ b) (budget : ℝ) (hbudget : (s.card : ℝ) * b ≤ budget) :
    ∑ i ∈ s, m i ≤ budget :=
  (gcdBetaMass_of_strata_bounds s m b hm).trans hbudget

/-- **A compiler cannot inhabit its own hypothesis.**  The premise of
`pvMedium_of_analyticHyp` is a genuine input: there are data for which it
fails. -/
theorem capacityCompiler_not_self_inhabiting :
    ∃ S C Y Q : ℝ, 0 < Q ∧ ¬ (S ≤ C ^ 2 * Y ^ 5 / Q) := by
  refine ⟨1, 0, 0, 1, by norm_num, ?_⟩
  norm_num

end Gate1B.SafeExtensions
