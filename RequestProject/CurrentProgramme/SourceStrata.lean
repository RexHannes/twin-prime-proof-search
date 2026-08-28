import RequestProject.CurrentProgramme.EndpointBilinear

/-!
# Current programme · source-neutral strata, defect-order census, recursion measure

Three source-*independent* banks that the current prompt asks for and that can
be proved without any missing literal source definition.  **Nothing here is an
estimate.**

1. **Phase A9 partition shape.**  The literal `β = μ_D * Λ_P` dictionary is
   absent (SOURCE BLOCKED), so the `z = d·p` rewriting cannot be performed.
   What *can* be banked now is the exact partition machinery the dictionary will
   plug into: an exhaustive, pairwise-disjoint finite stratification of the
   off-diagonal energy by an arbitrary label map, and its specialisation to the
   `p₁ = p₂` versus `p₁ ≠ p₂` split for an arbitrary prime label.  When the
   source arrives, only the label map has to be supplied.

2. **Phase D2 defect-order census.**  A five-row census type for
   `|J| = 5,4,3,2,1` together with a counterguard proving that a provider for
   `|J| = 5` does **not** formally entail providers for the lower orders.  No
   blanket monotonicity.

3. **Phase E/I proper-divisor recursion measure.**  The prompt requires a
   well-founded decrease before any recursive closure may be stated.  The
   measure is banked here; no recursive closure is stated.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Strata

open Finset

/-! ## 1. Exhaustive disjoint finite stratification (source-neutral) -/

/-- **Exhaustive disjoint partition of a finite sum by an arbitrary label map.**

This is the generic shape every stratum decomposition in the current programme
must take: the strata are the fibres of `strat`, they are pairwise disjoint and
they exhaust `S`, and the identity carries no estimate. -/
theorem sum_stratified {ι σ : Type*} [DecidableEq σ]
    (S : Finset ι) (strat : ι → σ) (T : Finset σ) (f : ι → ℂ)
    (hcov : ∀ i ∈ S, strat i ∈ T) :
    ∑ i ∈ S, f i = ∑ s ∈ T, ∑ i ∈ S.filter (fun i => strat i = s), f i :=
  (Finset.sum_fiberwise_of_maps_to hcov f).symm

/-- The strata really are pairwise disjoint. -/
theorem strata_disjoint {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (S : Finset ι) (strat : ι → σ) {s t : σ} (hst : s ≠ t) :
    Disjoint (S.filter (fun i => strat i = s)) (S.filter (fun i => strat i = t)) := by
  refine Finset.disjoint_left.mpr ?_
  intro i hi hi'
  rw [Finset.mem_filter] at hi hi'
  exact hst (hi.2 ▸ hi'.2 ▸ rfl)

/-- The strata really exhaust `S`. -/
theorem strata_cover {ι σ : Type*} [DecidableEq σ]
    (S : Finset ι) (strat : ι → σ) (T : Finset σ)
    (hcov : ∀ i ∈ S, strat i ∈ T) {i : ι} (hi : i ∈ S) :
    ∃ s ∈ T, i ∈ S.filter (fun i => strat i = s) :=
  ⟨strat i, hcov i hi, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩

/-! ## 2. Stratification of the endpoint off-diagonal energy

The off-diagonal index set is
`(congruentPairSet n U).filter (fun p => ¬ p.1 = p.2)`; we stratify *that*. -/

open EndpointBilinear

variable (n : ℕ)

/-- The off-diagonal index set, named. -/
def offdiagIndex (U : Finset ℤ) : Finset (ℤ × ℤ) :=
  (congruentPairSet n U).filter (fun p => ¬ p.1 = p.2)

/-- A single stratum of the off-diagonal energy, cut out by a label map. -/
noncomputable def offdiagStratum {σ : Type*} [DecidableEq σ]
    (U : Finset ℤ) (a4 Z : ℤ → ℂ) (strat : ℤ × ℤ → σ) (s : σ) : ℂ :=
  ∑ p ∈ (offdiagIndex n U).filter (fun p => strat p = s),
    (a4 p.1 * Z p.1) * (starRingEnd ℂ) (a4 p.2 * Z p.2)

/-- **Exact stratification of the off-diagonal energy.**  Identity only; no
stratum is bounded. -/
theorem offdiagEnergy_stratified {σ : Type*} [DecidableEq σ]
    (U : Finset ℤ) (a4 Z : ℤ → ℂ) (strat : ℤ × ℤ → σ) (T : Finset σ)
    (hcov : ∀ p ∈ offdiagIndex n U, strat p ∈ T) :
    offdiagEnergy n U a4 Z = ∑ s ∈ T, offdiagStratum n U a4 Z strat s :=
  sum_stratified _ strat T _ hcov

/-- **Phase A9 shape, source-neutral.**  For *any* prime-label map `plab`
(the literal `β = μ_D * Λ_P` dictionary would supply `plab z = p` from
`z = d·p`), the off-diagonal energy splits exactly and disjointly into the
`p₁ = p₂` and `p₁ ≠ p₂` strata.

This is a partition identity.  It becomes the physical `β`-split precisely when
the missing source dictionary supplies `plab`; until then no arithmetic content
is claimed. -/
theorem offdiagEnergy_prime_split (U : Finset ℤ) (a4 Z : ℤ → ℂ) (plab : ℤ → ℕ) :
    offdiagEnergy n U a4 Z
      = (∑ p ∈ (offdiagIndex n U).filter (fun p => plab p.1 = plab p.2),
            (a4 p.1 * Z p.1) * (starRingEnd ℂ) (a4 p.2 * Z p.2))
        + (∑ p ∈ (offdiagIndex n U).filter (fun p => ¬ plab p.1 = plab p.2),
            (a4 p.1 * Z p.1) * (starRingEnd ℂ) (a4 p.2 * Z p.2)) :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- Counterguard: the split is genuinely a *partition*, i.e. the two strata are
disjoint, so no term is double counted and none is dropped. -/
theorem prime_split_disjoint (U : Finset ℤ) (plab : ℤ → ℕ) :
    Disjoint ((offdiagIndex n U).filter (fun p => plab p.1 = plab p.2))
      ((offdiagIndex n U).filter (fun p => ¬ plab p.1 = plab p.2)) :=
  Finset.disjoint_filter_filter_not _ _ _

/-! ## 3. Phase D2 · defect-order census (no blanket monotonicity) -/

/-- The defect orders `|J| = 5,4,3,2,1`. -/
inductive DefectOrder
  | J5 | J4 | J3 | J2 | J1
  deriving DecidableEq, Repr, Inhabited

/-- All five orders. -/
def allDefectOrders : List DefectOrder :=
  [DefectOrder.J5, DefectOrder.J4, DefectOrder.J3, DefectOrder.J2, DefectOrder.J1]

/-- The census is over exactly five orders. -/
theorem allDefectOrders_length : allDefectOrders.length = 5 := rfl

/-- Every order appears in the census. -/
theorem allDefectOrders_complete : ∀ j : DefectOrder, j ∈ allDefectOrders := by
  intro j; cases j <;> decide

/-- **Counterguard: no blanket monotonicity.**

There is an assignment of "a provider exists" to the five orders which holds at
`|J| = 5` and fails at every lower order.  Hence closing `|J| = 5` cannot, as a
matter of logic, close `|J| = 4,3,2,1`: any such implication must come from a
*literal* source map, which this repository does not contain. -/
theorem no_blanket_monotonicity :
    ∃ P : DefectOrder → Prop,
      P DefectOrder.J5 ∧ ¬ P DefectOrder.J4 ∧ ¬ P DefectOrder.J3 ∧
      ¬ P DefectOrder.J2 ∧ ¬ P DefectOrder.J1 := by
  refine ⟨fun j => j = DefectOrder.J5, rfl, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Dually: a specialisation map, if it exists, must be exhibited.  This states
the *shape* of the only admissible upgrade, and is deliberately hypothesis-laden
rather than inhabited. -/
def SpecialisesFrom (source target : DefectOrder) (Prov : DefectOrder → Prop) : Prop :=
  Prov source → Prov target

/-- No specialisation map is inhabited here for any pair of distinct orders,
because none is derivable without the literal source decomposition. -/
theorem specialisation_not_automatic (source target : DefectOrder) (h : source ≠ target) :
    ∃ Prov : DefectOrder → Prop, ¬ SpecialisesFrom source target Prov := by
  refine ⟨fun j => j = source, ?_⟩
  intro hs
  exact h (hs rfl).symm

/-! ## 4. Phase E/I · proper-divisor recursion measure -/

/-- `d` is a proper divisor of `n`. -/
def ProperDvd (d n : ℕ) : Prop := d ∣ n ∧ d ≠ n ∧ 0 < n

/-- A proper divisor is strictly smaller. -/
theorem properDvd_lt {d n : ℕ} (h : ProperDvd d n) : d < n :=
  lt_of_le_of_ne (Nat.le_of_dvd h.2.2 h.1) h.2.1

/-- **The proper-divisor relation is well founded.**

This is the termination measure the prompt requires before any proper-divisor
recursion may be formalised.  Banking the measure does *not* state, and does not
imply, any recursive closure: the recursion's *content* still needs the missing
source packets. -/
theorem properDvd_wf : WellFounded ProperDvd :=
  Subrelation.wf properDvd_lt (invImage id Nat.lt_wfRel).wf

/-- The relation is irreflexive, so a recursion cannot stall on `n ↦ n`. -/
theorem properDvd_irrefl (n : ℕ) : ¬ ProperDvd n n := fun h => h.2.1 rfl

/-- `1` is a proper divisor of every `n ≥ 2`, so the recursion is nontrivial. -/
theorem one_properDvd {n : ℕ} (hn : 2 ≤ n) : ProperDvd 1 n :=
  ⟨one_dvd n, by omega, by omega⟩

end Strata
end CurrentProgramme
end TwinPrimeProject
