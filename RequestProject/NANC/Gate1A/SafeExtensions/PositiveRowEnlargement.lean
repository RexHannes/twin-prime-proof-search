/-
# NANC Gate 1A v9.4 — positive principal compression / row enlargement

The clean-P3 row set is replaced by a larger, *self-contained* row set `E♯`
whose defining predicate must **not** refer to the clean-P3 factor.  Because
every row energy is non-negative, enlarging the row set only increases the
energy, so any bound proved for `E♯` transfers to the clean-P3 rows.

This is pure finite positivity; no analytic input.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

variable {Row : Type*} [Fintype Row]

/-- A **positive row enlargement**: the clean-P3 predicate implies the `E♯`
predicate, and the `E♯` predicate is given independently (it is a field of the
structure, so it cannot mention the clean-P3 factor unless one deliberately
supplies such a predicate). -/
structure PositiveRowEnlargement (Row : Type*) [Fintype Row] where
  /-- The clean-P3 row predicate. -/
  cleanP3 : Row → Prop
  /-- The enlarged, self-contained row predicate. -/
  esharp : Row → Prop
  [cleanDec : DecidablePred cleanP3]
  [esharpDec : DecidablePred esharp]
  /-- Every clean-P3 row is an `E♯` row. -/
  enlarges : ∀ r, cleanP3 r → esharp r

attribute [instance] PositiveRowEnlargement.cleanDec PositiveRowEnlargement.esharpDec

namespace PositiveRowEnlargement

variable (P : PositiveRowEnlargement Row)

/-- The clean-P3 row set. -/
def cleanRows : Finset Row := univ.filter P.cleanP3

/-- The enlarged row set. -/
def esharpRows : Finset Row := univ.filter P.esharp

theorem cleanRows_subset_esharpRows : P.cleanRows ⊆ P.esharpRows := by
  intro r hr
  simp only [cleanRows, esharpRows, mem_filter, mem_univ, true_and] at *
  exact P.enlarges r hr

/-- **Positive principal compression.**  Any energy bound proved for the
enlarged row set `E♯` transfers to the clean-P3 rows. -/
theorem cleanP3_energy_le_esharp_energy (e : Row → ℝ) (he : ∀ r, 0 ≤ e r) :
    ∑ r ∈ P.cleanRows, e r ≤ ∑ r ∈ P.esharpRows, e r :=
  sum_le_sum_of_subset_of_nonneg P.cleanRows_subset_esharpRows fun r _ _ => he r

/-- Transfer of an explicit bound. -/
theorem cleanP3_energy_le_of_esharp_bound (e : Row → ℝ) (he : ∀ r, 0 ≤ e r) (B : ℝ)
    (hB : ∑ r ∈ P.esharpRows, e r ≤ B) : ∑ r ∈ P.cleanRows, e r ≤ B :=
  (P.cleanP3_energy_le_esharp_energy e he).trans hB

end PositiveRowEnlargement

/-! ## Firewall

The compression is *only* valid in the positive direction.  A lower bound for
`E♯` says nothing about the clean-P3 rows, and an `E♯` predicate that secretly
mentions the clean-P3 factor would reintroduce exactly the circularity the
enlargement is meant to remove.  Both facts are recorded by the countermodel
below: dropping a row can strictly decrease the energy. -/

/-- Enlargement is strictly one-directional: the enlarged energy can be
strictly larger, so no reverse inequality holds in general. -/
theorem rowEnlargement_not_reversible :
    ¬ (∀ (s t : Finset (Fin 2)) (e : Fin 2 → ℝ), s ⊆ t → (∀ r, 0 ≤ e r) →
        ∑ r ∈ t, e r ≤ ∑ r ∈ s, e r) := by
  intro h
  have := h ∅ univ (fun _ => 1) (empty_subset _) (fun _ => zero_le_one)
  norm_num at this

end TwinPrimeProject.NANC.Gate1A.V94
