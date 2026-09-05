/-
# Gate1B / R11 : canonical source layer

This file records the **canonical** (explicitly defined) R11 source object together with
its purely combinatorial label layer and its rational exponent metadata.

FIREWALL (see `Gate1B/R11/Bank.lean`): nothing in this file, and nothing anywhere in the
`Gate1B.R11` namespace, asserts that this canonical source coincides with any historical or
"full physical" R11 source.  The canonical source is a *definition*, not a recovery claim.

Nothing here is analytic: no prime number theory, no support/length statements are proved
from the rational metadata.
-/
import Mathlib

namespace Gate1B.R11

open Finset ArithmeticFunction

/-! ## 1. Label layer: one distinguished coordinate and ten large coordinates -/

/-- Labels for the eleven R11 coordinates: one distinguished coordinate `p0` and ten
large coordinates `large 0, …, large 9`.  Analytic support lengths are metadata and are
deliberately *not* part of this structure. -/
structure R11Labels where
  p0 : ℕ
  large : Fin 10 → ℕ

namespace R11Labels

variable (L : R11Labels)

/-- All eleven coordinates are prime. -/
def AllPrime : Prop := Nat.Prime L.p0 ∧ ∀ i, Nat.Prime (L.large i)

/-- All eleven coordinates are odd. -/
def AllOdd : Prop := Odd L.p0 ∧ ∀ i, Odd (L.large i)

/-- The ten large coordinates are pairwise distinct. -/
def LargeDistinct : Prop := Function.Injective L.large

/-- The distinguished coordinate differs from every large coordinate. -/
def P0Fresh : Prop := ∀ i, L.p0 ≠ L.large i

/-- Admissible labels: eleven distinct odd primes, with `p0` distinguished. -/
def Admissible : Prop := L.AllPrime ∧ L.AllOdd ∧ L.LargeDistinct ∧ L.P0Fresh

/-- The eleven coordinates as a single indexed family. -/
def atoms : Fin 11 → ℕ := Fin.cases L.p0 L.large

@[simp] theorem atoms_zero : L.atoms 0 = L.p0 := rfl

@[simp] theorem atoms_succ (i : Fin 10) : L.atoms i.succ = L.large i := rfl

/-- Combinatorics is isolated from primality: distinctness of the large coordinates plus
freshness of `p0` is exactly what makes the eleven atoms pairwise distinct. -/
theorem atoms_injective (hd : L.LargeDistinct) (hf : L.P0Fresh) :
    Function.Injective L.atoms := by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ j => exact absurd hab (hf j)
  | succ i =>
      induction b using Fin.cases with
      | zero => exact absurd hab.symm (hf i)
      | succ j => exact congrArg Fin.succ (hd hab)

theorem atoms_injective_of_admissible (h : L.Admissible) : Function.Injective L.atoms :=
  L.atoms_injective h.2.2.1 h.2.2.2

theorem atoms_prime_of_admissible (h : L.Admissible) (i : Fin 11) : Nat.Prime (L.atoms i) := by
  induction i using Fin.cases with
  | zero => exact h.1.1
  | succ j => exact h.1.2 j

end R11Labels

/-! ## 2. Möbius sign of a squarefree product of distinct primes -/

/-- The Möbius function of a product of distinct primes is `(-1)` to the number of primes. -/
theorem moebius_prod_primes (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    moebius (∏ p ∈ s, p) = (-1) ^ s.card := by
  have hcop : (↑s : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun n : ℕ => n)) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (h i hi) (h j hj)).mpr hij
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod (fun n : ℕ => n) s hcop,
    Finset.prod_congr rfl fun p hp => ArithmeticFunction.moebius_apply_prime (h p hp)]
  simp

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hprime : a.Prime := h a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime := fun p hp => h p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
        Nat.Coprime.prod_right fun p hp =>
          (Nat.coprime_primes hprime (hs p hp)).mpr (by rintro rfl; exact ha hp)
      exact (Nat.squarefree_mul hcop).mpr ⟨hprime.squarefree, ih hs⟩

/-! ## 3. Cross-group collision decomposition (§5)

The free grouped `5|4|2` convolution forbids collisions *inside* each group but permits
equal atoms *across* groups.  There are exactly `4*4 + 4*2 + 4*2 = 32` cross-group
coordinate pairs. -/

/-- The number of cross-group coordinate pairs in the `4|4|2` allocation. -/
theorem crossGroupPairs_count : 4 * 4 + 4 * 2 + 4 * 2 = 32 := by norm_num

section Collision

variable {R : Type*} [CommRing R]

/-- Squarefreeness indicator of a natural number, valued in the coefficient ring. -/
noncomputable def sfIndicator (R : Type*) [CommRing R] (n : ℕ) : R :=
  if Squarefree n then 1 else 0

@[simp] theorem sfIndicator_of_squarefree {n : ℕ} (h : Squarefree n) :
    sfIndicator R n = 1 := if_pos h

@[simp] theorem sfIndicator_of_not_squarefree {n : ℕ} (h : ¬ Squarefree n) :
    sfIndicator R n = 0 := if_neg h

/-- The collision remainder attached to a free grouped source. -/
noncomputable def Ecoll (OmegaFree : ℕ → R) (n : ℕ) : R :=
  (1 - sfIndicator R n) * OmegaFree n

/-- **Exact collision decomposition (unconditional).**  If the squarefree-sector source
agrees with the free grouped source on squarefree arguments and vanishes elsewhere, then it
is exactly the free source minus the collision remainder.  No analytic input whatsoever. -/
theorem omegaSquarefree_eq_free_sub_collision
    (OmegaFree OmegaSquarefree : ℕ → R)
    (hsf : ∀ n, Squarefree n → OmegaSquarefree n = OmegaFree n)
    (hns : ∀ n, ¬ Squarefree n → OmegaSquarefree n = 0) (n : ℕ) :
    OmegaSquarefree n = OmegaFree n - Ecoll OmegaFree n := by
  by_cases h : Squarefree n
  · rw [hsf n h, Ecoll, sfIndicator_of_squarefree h]; ring
  · rw [hns n h, Ecoll, sfIndicator_of_not_squarefree h]; ring

/-- Summed form of the exact collision decomposition. -/
theorem sum_omegaSquarefree_eq (s : Finset ℕ)
    (OmegaFree OmegaSquarefree : ℕ → R)
    (hsf : ∀ n, Squarefree n → OmegaSquarefree n = OmegaFree n)
    (hns : ∀ n, ¬ Squarefree n → OmegaSquarefree n = 0) :
    ∑ n ∈ s, OmegaSquarefree n
      = (∑ n ∈ s, OmegaFree n) - ∑ n ∈ s, Ecoll OmegaFree n := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ =>
    omegaSquarefree_eq_free_sub_collision OmegaFree OmegaSquarefree hsf hns n

end Collision

/-- **Conditional** collision wrapper.  The analytic estimate `Ecoll = O_A(X log^{-A} X)`
is *not* proved here; it is taken as the explicit hypothesis `hcoll`.  The combinatorial
decomposition it is applied to (above) is unconditional. -/
theorem canonical_source_from_free_of_collision_bound
    (s : Finset ℕ) (OmegaFree OmegaSquarefree : ℕ → ℝ) (eps : ℝ)
    (hsf : ∀ n, Squarefree n → OmegaSquarefree n = OmegaFree n)
    (hns : ∀ n, ¬ Squarefree n → OmegaSquarefree n = 0)
    (hcoll : |∑ n ∈ s, Ecoll OmegaFree n| ≤ eps) :
    |(∑ n ∈ s, OmegaSquarefree n) - ∑ n ∈ s, OmegaFree n| ≤ eps := by
  rw [sum_omegaSquarefree_eq s OmegaFree OmegaSquarefree hsf hns]
  simpa [abs_sub_comm] using hcoll

/-! ## 4. Canonical source metadata: exact rational exponent identities (§6)

These are *definitions plus rational arithmetic*.  No analytic support statement is derived
from them anywhere in this development. -/

/-- Exponent centre of the distinguished coordinate `p0`. -/
def p0Center : ℚ := 9 / 100

/-- Exponent centre of each of the ten large coordinates. -/
def largeCenter : ℚ := 91 / 1000

theorem centers_sum_to_one : p0Center + 10 * largeCenter = 1 := by
  unfold p0Center largeCenter; norm_num

theorem p0_plus_four_large : p0Center + 4 * largeCenter = 227 / 500 := by
  unfold p0Center largeCenter; norm_num

theorem four_large : 4 * largeCenter = 91 / 250 := by unfold largeCenter; norm_num

theorem two_large : 2 * largeCenter = 91 / 500 := by unfold largeCenter; norm_num

theorem six_large : 6 * largeCenter = 273 / 500 := by unfold largeCenter; norm_num

theorem split_227_273 : (227 : ℚ) / 500 + 273 / 500 = 1 := by norm_num

/-- The Bézout-shift exponent gap (§11 metadata); a rational identity only. -/
theorem gap_23_250 : (273 : ℚ) / 500 - 227 / 500 = 23 / 250 := by norm_num

end Gate1B.R11
