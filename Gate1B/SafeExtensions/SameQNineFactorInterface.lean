/-
# Gate 1B v8.3 — conditional nine-factor same-`q` Gram compiler

**Status: CONDITIONAL_FINITE (interface; deliberately uninhabited).**

An abstract datum carrying the nine factors of the same-`q` reassembly:

* seven source character transforms;
* the `h` dual correlation;
* the `k` dual correlation;
* the Gauss weights;
* the `β` weight.

Only the exact finite reassembly is proved: if a family `F` factorises through
the datum, its sum is the nine-factor sum.  **No analytic estimate is declared
and no inhabitant of the datum is constructed here** — every source and
analytic input remains an explicit hypothesis.
-/
import Mathlib
import Gate1B.SafeAlgebra.SameQCharacterGram

namespace Gate1B.SafeExtensions

open Finset

/-- The nine-factor same-`q` datum. -/
structure SameQNineFactorData (Ch : Type*) where
  /-- Seven source character transforms. -/
  sourceTransform : Fin 7 → Ch → ℂ
  /-- The `h` dual correlation. -/
  hDual : Ch → ℂ
  /-- The `k` dual correlation. -/
  kDual : Ch → ℂ
  /-- The Gauss weight. -/
  gaussWeight : Ch → ℂ
  /-- The `β` weight. -/
  betaWeight : Ch → ℂ

namespace SameQNineFactorData

variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] (Data : SameQNineFactorData Ch)

/-- The nine-factor term at a single character. -/
noncomputable def term (c : Ch) : ℂ :=
  (∏ i : Fin 7, Data.sourceTransform i c) * Data.hDual c * Data.kDual c *
    Data.gaussWeight c * Data.betaWeight c

/-- The assembled nine-factor sum. -/
noncomputable def total : ℂ := ∑ c : Ch, Data.term c

/-- **Exact reassembly.**  A family factorising through the datum sums to the
nine-factor total.  The factorisation is a hypothesis; nothing is estimated. -/
theorem sameQ_of_nuclear_factorisation (F : Ch → ℂ)
    (hfac : ∀ c : Ch, F c = (∏ i : Fin 7, Data.sourceTransform i c) * Data.hDual c *
      Data.kDual c * Data.gaussWeight c * Data.betaWeight c) :
    ∑ c : Ch, F c = Data.total := by
  unfold total term
  exact Finset.sum_congr rfl fun c _ => hfac c

/-- The nine labelled factors: seven source transforms plus the two dual
correlations (the Gauss and `β` weights are scalar weights, not factors). -/
theorem nine_factors : 7 + 1 + 1 = 9 := by norm_num

/-- Splitting one factor out of the nine-factor term is exact. -/
theorem term_split (c : Ch) :
    Data.term c
      = ((∏ i : Fin 7, Data.sourceTransform i c) * Data.hDual c * Data.kDual c) *
          (Data.gaussWeight c * Data.betaWeight c) := by
  unfold term; ring

end SameQNineFactorData

end Gate1B.SafeExtensions
