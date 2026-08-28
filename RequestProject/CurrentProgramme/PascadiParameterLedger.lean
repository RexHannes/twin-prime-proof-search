import Mathlib.Tactic
import RequestProject.CurrentProgramme.FactorialEulerPolarization

/-!
# Phase J4 / J5 · Pascadi parameter ledger and the balanced-seven interfaces

## J4 — `PASCADI-PROOF-PARAMETER-NOGO`

This is an **audit of the supplied proof parameters**, and emphatically *not* a
claim that "the Pascadi theorem is impossible".  What is proved is exact
rational arithmetic:

* `eta_le_of_constraint`  : `3/5 ≤ 5/8 - 100 η  ⟹  η ≤ 1/4000`;
* `one_seventh_gt`        : `1/7 > 1/4000`;
* `pascadi_parameter_nogo`: no `η` satisfies `η ≥ 1/7` and `3/5 ≤ 5/8 - 100η`
                            simultaneously.

## J5 — the current balanced-seven open interfaces

`FactorialOmega7SignedEndpointInput` and `MuLogComparisonLowCondMatch` are kept
**UNINHABITED**; only the deterministic compiler between them is proved.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Pascadi

/-! ## 1. The parameter no-go -/

/-- **J4.**  The supplied constraint `3/5 ≤ 5/8 - 100η` forces `η ≤ 1/4000`. -/
theorem eta_le_of_constraint {eta : ℚ} (h : (3 : ℚ) / 5 ≤ 5 / 8 - 100 * eta) :
    eta ≤ 1 / 4000 := by linarith

/-- `1/7` exceeds the admissible ceiling `1/4000`. -/
theorem one_seventh_gt : (1 : ℚ) / 4000 < 1 / 7 := by norm_num

/-- **J4, `PASCADI-PROOF-PARAMETER-NOGO`.**  No `η` satisfies both the
smooth-number requirement `η ≥ 1/7` and the supplied dispersion constraint
`3/5 ≤ 5/8 - 100η`.

This audits the *supplied proof parameters*; it says nothing about whether the
underlying theorem is true by other parameters. -/
theorem pascadi_parameter_nogo :
    ¬ ∃ eta : ℚ, (1 : ℚ) / 7 ≤ eta ∧ (3 : ℚ) / 5 ≤ 5 / 8 - 100 * eta := by
  rintro ⟨eta, h1, h2⟩
  have h3 : eta ≤ 1 / 4000 := eta_le_of_constraint h2
  have h4 : (1 : ℚ) / 4000 < 1 / 7 := one_seventh_gt
  linarith

/-- The no-go is a *parameter* statement: relaxing the dispersion constant makes
the system satisfiable, so nothing structural is being claimed. -/
theorem nogo_is_parameter_specific :
    ∃ eta : ℚ, (1 : ℚ) / 7 ≤ eta ∧ (3 : ℚ) / 5 ≤ 5 / 8 - (1 : ℚ) / 10 * eta := by
  refine ⟨1 / 7, le_refl _, by norm_num⟩

/-! ## 2. Balanced-seven open interfaces (J5) -/

/-- **UNINHABITED (J5).**  `AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45`.

The signed endpoint estimate for the factorial `Ω = 7` source.  The algebraic
input it consumes — the factorial–Euler polarization — *is* proved
(`FactorialEuler.factorialEulerPolarization_seven`); the analytic endpoint
estimate is not. -/
structure FactorialOmega7SignedEndpointInput where
  /-- The signed endpoint quantity for the `Ω = 7` factorial source. -/
  endpointQuantity : ℝ
  /-- Its target level. -/
  level : ℝ
  /-- The estimate.  NOT PROVED. -/
  bound : |endpointQuantity| ≤ level

/-- **UNINHABITED (J5).**  `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`.

The `μ * log` comparison must match the low-conductor part of the physical
source.  This is a *source identity*, kept separate from the endpoint estimate
exactly as instructed. -/
structure MuLogComparisonLowCondMatch where
  /-- The `μ * log` comparison low-conductor term. -/
  comparisonLowCond : ℝ
  /-- The physical low-conductor term. -/
  physicalLowCond : ℝ
  /-- Match tolerance. -/
  tol : ℝ
  /-- The match.  NOT PROVED. -/
  matched : |comparisonLowCond - physicalLowCond| ≤ tol

/-- The balanced-seven modulus-average target. -/
def Balanced7ModulusAverageBound (quantity level : ℝ) : Prop := |quantity| ≤ level

/-- **J5, deterministic compiler.**  Factorial endpoint input plus comparison
input imply the balanced-seven modulus-average bound, provided the source
decomposition of the modulus-average quantity into endpoint plus comparison
defect is supplied.

The decomposition hypothesis `hsplit` is a *source* obligation and is exposed
explicitly; it is not proved. -/
theorem balanced7_modulusAverage_of_inputs
    (e : FactorialOmega7SignedEndpointInput) (c : MuLogComparisonLowCondMatch)
    {quantity : ℝ}
    (hsplit : quantity = e.endpointQuantity +
      (c.comparisonLowCond - c.physicalLowCond)) :
    Balanced7ModulusAverageBound quantity (e.level + c.tol) := by
  unfold Balanced7ModulusAverageBound
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add e.bound c.matched)

/-- **Counterguard.**  The compiler is not vacuous and its conclusion is not
automatic: there are data for which the balanced-seven bound fails. -/
theorem balanced7_not_automatic :
    ¬ Balanced7ModulusAverageBound 2 1 := by
  unfold Balanced7ModulusAverageBound; norm_num

/-! ## 3. Fixed-degree-seven block partitions (J6) -/

/-- Source-neutral block partitions of `7` used by the fixed-degree-seven
post-dispersion geometry. -/
def blocks_2221 : List ℕ := [2, 2, 2, 1]

/-- Source-neutral block partition `3+2+1+1`. -/
def blocks_3211 : List ℕ := [3, 2, 1, 1]

/-- Both listed block partitions really are partitions of `7`. -/
theorem blocks_sum_seven :
    blocks_2221.sum = 7 ∧ blocks_3211.sum = 7 := by
  constructor <;> decide

/-- Exact finite regrouping: the two partitions have different block
multisets, so a provider for one does not automatically serve the other. -/
theorem blocks_distinct : blocks_2221 ≠ blocks_3211 := by decide

end Pascadi
end CurrentProgramme
end TwinPrimeProject
