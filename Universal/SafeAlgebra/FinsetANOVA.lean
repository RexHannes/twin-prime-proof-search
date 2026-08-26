/-
# Universal safe algebra — the generic finite ANOVA (defect/model) expansion

Exact finite algebra over an arbitrary commutative semiring.  Nothing here is
asymptotic, analytic, or Gate-specific.

* `finset_prod_add_eq_sum_powerset` — for `f δ : ι → R` and a `Finset S`,

      ∏ i ∈ S, (f i + δ i) = ∑ J ∈ S.powerset, (∏ j ∈ J, δ j) * (∏ i ∈ S \ J, f i).

  `J` is the *defect* set and `S \ J` the *model* set.

* `mem_powerset_iff_subset` and `card_sdiff_of_subset` — the support/cardinality
  bookkeeping used downstream.

No `native_decide`, no `Fin 9` specialisation here: the theorem is proved in
full generality and specialised elsewhere.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R]

/-- **Generic finite ANOVA expansion.**  Splitting each factor as
`ν i = f i + δ i` expands the product over `S` into `2^{#S}` terms indexed by
the defect subset `J ⊆ S`. -/
theorem finset_prod_add_eq_sum_powerset (S : Finset ι) (f δ : ι → R) :
    ∏ i ∈ S, (f i + δ i)
      = ∑ J ∈ S.powerset, (∏ j ∈ J, δ j) * ∏ i ∈ S \ J, f i := by
  have h : ∏ i ∈ S, (δ i + f i)
      = ∑ J ∈ S.powerset, (∏ j ∈ J, δ j) * ∏ i ∈ S \ J, f i :=
    Finset.prod_add δ f S
  simpa [add_comm] using h

omit [DecidableEq ι] in
/-- The powerset membership condition is exactly subset-hood. -/
theorem mem_powerset_iff_subset (S J : Finset ι) : J ∈ S.powerset ↔ J ⊆ S :=
  Finset.mem_powerset

/-- Cardinality of the model (complementary) set. -/
theorem card_sdiff_of_subset {S J : Finset ι} (h : J ⊆ S) : (S \ J).card = S.card - J.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

end Universal.SafeAlgebra
