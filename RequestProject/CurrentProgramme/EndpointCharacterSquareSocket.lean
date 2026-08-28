import Mathlib
import RequestProject.CurrentProgramme.EndpointTwoStageCharacterForm

/-!
# Phase H · the current analytic socket

`ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45 : OPEN_ANALYTIC`.

This module contains the *exact* analytic interface which is now the controlling
frontier of the endpoint programme, namely a bound for

```
∑_{ℓ ∈ L}  1/φ(ℓ)  ∑_{χ ≠ χ₀}
  | ∑_{m,r,d,p} α(m) γ(r) χ(m) χ(r) μ(d) log p · W(…) · K_{mr,ℓ}(dp) |²
    ≤  desiredTarget
```

which is literally `TwoStageSourceData.TwoStageSquareBundle` of the previous
module.

**The interface is deliberately left uninhabited.**  Nothing in this file (or
anywhere else in the repository) constructs a term of
`EndpointCharTwistedFactorModSquareInput`; every downstream theorem takes such a
term as a *hypothesis*.  The firewall lemmas at the end of the file show the
interface is not automatic: for a negative target it is provably empty.

Budget metadata (`NaturalScaleBound` / `RequiredLogSavingBound`) is represented
by abstract positive parameters together with an explicit *strict improvement*
requirement, rather than by fake `log^{-A}` asymptotics.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace CharSquareSocket

open Finset CharacterCentering TwoStageChar

/-! ## 1. The analytic socket -/

/-- **`EndpointCharTwistedFactorModSquareInput`.**

The analytic input asserting that the character-twisted factor-mod square bundle
of the two-stage source data `data`, over the modulus family `L` and at the
frequency `k`, is at most `desiredTarget`.

`OPEN_ANALYTIC`: no inhabitant exists in this repository. -/
structure EndpointCharTwistedFactorModSquareInput where
  /-- The two-stage source data whose square bundle is being bounded. -/
  data : TwoStageSourceData
  /-- The modulus family `ℓ ∼ R`. -/
  L : Finset ℕ+
  /-- The frequency parameter. -/
  k : ℕ
  /-- The target for the square bundle. -/
  desiredTarget : ℝ
  /-- The analytic assertion itself. -/
  bound : data.TwoStageSquareBundle L k ≤ desiredTarget

/-! ## 2. Budget metadata -/

/-- Budget metadata for the endpoint square.

`natural` is the natural-scale (trivial / Parseval) size of the bundle;
`required` is the size actually needed downstream.  The content of the endpoint
problem is the *strict* inequality `required < natural`: an honest saving is
demanded, and no asymptotic `log^{-A}` notation is faked. -/
structure EndpointBudgets where
  /-- `NaturalScaleBound`: the size reachable by trivial/Parseval estimation. -/
  naturalBudget : ℝ
  /-- `RequiredLogSavingBound`: the size required downstream. -/
  requiredBudget : ℝ
  /-- The required budget is a genuine size. -/
  required_pos : 0 < requiredBudget
  /-- A strict improvement over the natural scale is demanded. -/
  strict_improvement : requiredBudget < naturalBudget

namespace EndpointBudgets

variable (b : EndpointBudgets)

theorem natural_pos : 0 < b.naturalBudget :=
  b.required_pos.trans b.strict_improvement

/-- The demanded saving factor is a genuine (strictly less than one) ratio. -/
theorem saving_ratio_lt_one : b.requiredBudget / b.naturalBudget < 1 :=
  (div_lt_one b.natural_pos).2 b.strict_improvement

/-- A budget pair carrying no improvement is impossible. -/
theorem no_trivial_budget (h : b.naturalBudget = b.requiredBudget) : False := by
  exact absurd h.symm b.strict_improvement.ne

end EndpointBudgets

/-- An input *at the required budget*: this is exactly the analytic statement the
programme needs, and it is the only place where a saving is ever assumed. -/
structure EndpointSquareAtRequiredBudget where
  /-- The budget metadata. -/
  budgets : EndpointBudgets
  /-- The analytic input, whose target is the required budget. -/
  input : EndpointCharTwistedFactorModSquareInput
  /-- The input's target is literally the required budget. -/
  target_eq : input.desiredTarget = budgets.requiredBudget

/-! ## 3. Firewalls: the socket is not automatic -/

/-- Any inhabitant of the socket forces a nonnegative target, since the bundle is
a sum of squares. -/
theorem charSquareInput_requires_nonneg_target
    (I : EndpointCharTwistedFactorModSquareInput) : 0 ≤ I.desiredTarget :=
  le_trans (I.data.twoStageSquareBundle_nonneg I.L I.k) I.bound

/-- **`charSquareInput_not_automatic`.**  There is a choice of data, modulus
family, frequency and target for which the socket is provably *empty*; hence no
compiler in this repository can manufacture its own analytic antecedent. -/
theorem charSquareInput_not_automatic :
    ∃ (S : TwoStageSourceData) (L : Finset ℕ+) (k : ℕ) (t : ℝ),
      IsEmpty {I : EndpointCharTwistedFactorModSquareInput //
        I.data = S ∧ I.L = L ∧ I.k = k ∧ I.desiredTarget = t} := by
  refine ⟨emptyTwoStage, {(3 : ℕ+)}, 0, -1, ?_⟩
  constructor
  rintro ⟨I, -, -, -, ht⟩
  have := charSquareInput_requires_nonneg_target I
  rw [ht] at this
  norm_num at this

/-- The socket does have *non-vacuous* content: for a sufficiently generous
target the corresponding statement is true (this is the natural-scale end), so
the interface is not empty for trivial reasons either.  We record this only for
the degenerate empty source, where the bundle is `0`. -/
theorem charSquareInput_nonvacuous_at_zero :
    emptyTwoStage.TwoStageSquareBundle {(3 : ℕ+)} 0 ≤ 0 :=
  le_of_eq emptyTwoStage_bundle

end CharSquareSocket
end CurrentProgramme
end TwinPrimeProject
