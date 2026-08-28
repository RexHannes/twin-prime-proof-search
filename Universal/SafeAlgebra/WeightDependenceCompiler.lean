/-
# Universal v13 — weight-dependence compiler

**Status: finite identities PROVED; the edge-dependent case is guarded.**

A weighted packet sum is `packetSum w f = ∑_e w(e) f(e)`.  The compiler treats
the three weight regimes of
`Universal.SafeExtensions.WeightType` separately:

* `common` — `packetSum` collapses to `c · ∑ f` (`packetSum_common`);
* `finiteTemplate` — `packetSum` splits into at most `#template` common-weight
  sums (`packetSum_finiteTemplate`);
* `edgeDependent` — only the trivial triangle bound is available
  (`packetSum_edgeDependent_le`).

The counterguard `edgeDependent_not_absorbed_by_common` shows the third case is
genuinely different: for a non-constant weight there is **no** scalar `c` with
`packetSum w f = c · ∑ f` for all `f`.  A common-weight theorem therefore may
not be applied to edge-dependent weights.
-/
import Mathlib
import Universal.SafeExtensions.SourceExactHighP3PacketDictionary

namespace Universal.SafeAlgebra

open Finset Universal.SafeExtensions

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The weighted packet sum. -/
noncomputable def packetSum (w f : E → ℂ) : ℂ := ∑ e : E, w e * f e

omit [DecidableEq E] in
/-- **Common weight.**  A constant weight factors out. -/
theorem packetSum_common (w f : E → ℂ) (c : ℂ) (hw : ∀ e : E, w e = c) :
    packetSum w f = c * ∑ e : E, f e := by
  unfold packetSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by rw [hw e]

omit [DecidableEq E] in
/-- **Finite template.**  A weight valued in a finite template splits into one
common-weight sum per template value. -/
theorem packetSum_finiteTemplate (w f : E → ℂ) (template : Finset ℂ)
    (hw : ∀ e : E, w e ∈ template) :
    packetSum w f
      = ∑ t ∈ template, t * ∑ e ∈ Finset.univ.filter (fun e => w e = t), f e := by
  classical
  unfold packetSum
  rw [← Finset.sum_fiberwise_of_maps_to (g := w) (fun e _ => hw e) (fun e => w e * f e)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [(Finset.mem_filter.mp he).2]

omit [DecidableEq E] in
/-- **Edge-dependent weight.**  Only the triangle bound is available. -/
theorem packetSum_edgeDependent_le (w f : E → ℂ) (Wmax : ℝ)
    (hw : ∀ e : E, ‖w e‖ ≤ Wmax) :
    ‖packetSum w f‖ ≤ Wmax * ∑ e : E, ‖f e‖ := by
  unfold packetSum
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hw e) (norm_nonneg _)

/-- **COUNTERGUARD.**  A non-constant (edge-dependent) weight cannot be absorbed
by any common-weight statement: no scalar `c` reproduces the packet sum for all
test functions. -/
theorem edgeDependent_not_absorbed_by_common :
    ¬ ∃ c : ℂ, ∀ f : Bool → ℂ,
        packetSum (fun e => if e then 1 else 0) f = c * ∑ e : Bool, f e := by
  rintro ⟨c, hc⟩
  have h1 := hc (fun e => if e then 1 else 0)
  have h2 := hc (fun e => if e then 0 else 1)
  simp [packetSum] at h1 h2
  rw [← h1] at h2
  norm_num at h2

end Universal.SafeAlgebra
