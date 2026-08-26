import Mathlib
import RequestProject.ThreeFormSieveInput

/-!
# Finite max-jump forest and orphan-sea combinatorics

The graph is represented by a finite parent map whose rank strictly increases
along every nontrivial arc.  This gives acyclicity without any analytic input.
-/

namespace Erdos461A

open scoped BigOperators

structure RankedParentForest (V : Type*) [Fintype V] [DecidableEq V] where
  parent : V → V
  rank : V → ℕ
  increases : ∀ v, parent v ≠ v → rank v < rank (parent v)

/-- Every vertex has at most one outgoing arc, by construction. -/
theorem maxJumpOutdegreeAtMostOne {V : Type*} [Fintype V] [DecidableEq V]
    (G : RankedParentForest V) (v w₁ w₂ : V)
    (h₁ : G.parent v = w₁) (h₂ : G.parent v = w₂) : w₁ = w₂ := by
  rw [← h₁, h₂]

/-- No nontrivial iterate can return to its starting point when rank strictly
increases at every step. -/
theorem rankedParentNoDirectedCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : RankedParentForest V) (v : V) (k : ℕ) (hk : 0 < k)
    (hsteps : ∀ i < k, G.parent^[i + 1] v ≠ G.parent^[i] v) :
    G.parent^[k] v ≠ v := by
  by_contra hcycle
  -- If G.parent^[k] v = v, then rank must have increased k times but ended up back at rank v
  -- This is impossible because rank is a natural number and strictly increases each step
  -- Key: rank strictly increases at each step
  have hirf : ∀ i < k, G.rank (G.parent^[i] v) < G.rank (G.parent^[i + 1] v) := by
    intro i hi
    rw [Function.iterate_succ_apply']
    apply G.increases
    have := hsteps i hi
    simp [Function.iterate_succ_apply'] at this
    exact this
  -- By transitivity, rank at step k > rank at step 0
  have hmono : ∀ i j, i < j → j ≤ k → G.rank (G.parent^[i] v) < G.rank (G.parent^[j] v) := by
    intro i j hij hjk
    induction hij with
    | refl => exact hirf i (Nat.lt_of_succ_le hjk)
    | step _ ih => exact lt_trans (ih (Nat.le_of_succ_le hjk)) (hirf _ (Nat.lt_of_succ_le hjk))
  -- Now apply with i = 0, j = k
  have hkpos : 0 < k := hk
  have hle : k ≤ k := Nat.le_refl k
  have hcontra : G.rank (G.parent^[0] v) < G.rank (G.parent^[k] v) := hmono 0 k hkpos hle
  simp [Function.iterate_zero] at hcontra
  rw [hcycle] at hcontra
  exact lt_irrefl _ hcontra

/-- If `L` leaf-to-root paths cover `E` edges and each has length at most `ell`,
then `E ≤ L*ell`. -/
theorem orphanSeaCoverBound (E L ell : ℕ)
    (pathLength : Fin L → ℕ) (hcover : E ≤ ∑ i, pathLength i)
    (hlen : ∀ i, pathLength i ≤ ell) : E ≤ L * ell := by
  calc
    E ≤ ∑ i, pathLength i := hcover
    _ ≤ ∑ _i : Fin L, ell := Finset.sum_le_sum fun i _ => hlen i
    _ = L * ell := by simp

/-- Conditional orphan-sea conclusion.  `L` counts occurrences (vertices), not
distinct labels.  The only analytic dependence is the explicit sieve input. -/
theorem conditionalOrphanSea
    (_sieve : OPEN_ANALYTIC_INPUT_threeFormUpperSieve)
    (edgeCount orphanCount ell target : ℕ)
    (hcover : edgeCount ≤ orphanCount * ell)
    (hedges : target ≤ edgeCount) : target ≤ orphanCount * ell :=
  le_trans hedges hcover

end Erdos461A
