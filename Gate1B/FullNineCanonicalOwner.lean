import Gate1B.CanonicalR9Comparison

/-!
# Gate 1B · full-nine first-remainder owner identity (append-only)

**Exact algebra only.**  This module proves the full-nine canonical
first-remainder telescope, the uniqueness and disjointness of first-remainder
ownership, the occupancy-symmetrisation firewall, and the explicit separation
of the prime-power owner.  No analytic leaf closure is encoded here, and the
prime-power analytic saving is *not* formalised: it is exposed as the interface
`PrimePowerCorrectionBound`.

## Contents

* §1 the general telescope `P_j = (∏_{i<j} m_i)(∏_{i≥j} π_i)` with
  `P_0 = ∏ π`, `P_n = ∏ m`, and the exact step
  `P_{j-1} − P_j = (∏_{i<j} m_i) ε_j (∏_{i>j} π_i)`;
* §2 the boxed nine-coordinate identity
  `fullNine_canonical_firstRemainder_telescope`;
* §3 the `ρ`/`e^{pp}` owner split (`fullNine_owner_split`), each owner counted
  exactly once;
* §4 unique first-remainder ownership (`firstRemainder_owner_unique`) and the
  disjoint fibre partition of labelled expansion terms;
* §5 the occupancy/factorial symmetrisation firewall
  (`occupancySum_preserves_firstRemainder_identity`);
* §6 `PrimePowerCorrectionBound` as an explicit, never-inhabited interface.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FullNineOwner

open Finset

/-! ## 1. The general telescope -/

section Telescope

variable {R : Type*} [CommRing R]

/-- `P_j := (∏_{i<j} m_i) · (∏_{j ≤ i < n} π_i)`. -/
def partialModelProduct (m pi : ℕ → R) (n j : ℕ) : R :=
  (∏ i ∈ range j, m i) * (∏ i ∈ Ico j n, pi i)

@[simp] theorem partialModelProduct_zero (m pi : ℕ → R) (n : ℕ) :
    partialModelProduct m pi n 0 = ∏ i ∈ range n, pi i := by
  rw [partialModelProduct, Finset.range_zero, Finset.prod_empty, one_mul,
    ← Finset.range_eq_Ico]

@[simp] theorem partialModelProduct_top (m pi : ℕ → R) (n : ℕ) :
    partialModelProduct m pi n n = ∏ i ∈ range n, m i := by
  simp [partialModelProduct]

/-- **Exact telescope step.**  For `j < n`,

`P_j − P_{j+1} = (∏_{i<j} m_i) · (π_j − m_j) · (∏_{j<i<n} π_i)`. -/
theorem partialModelProduct_step (m pi : ℕ → R) {n j : ℕ} (hj : j < n) :
    partialModelProduct m pi n j - partialModelProduct m pi n (j + 1)
      = (∏ i ∈ range j, m i) * (pi j - m j) * (∏ i ∈ Ico (j + 1) n, pi i) := by
  have hsplit : ∏ i ∈ Ico j n, pi i = pi j * ∏ i ∈ Ico (j + 1) n, pi i :=
    Finset.prod_eq_prod_Ico_succ_bot hj _
  simp only [partialModelProduct, hsplit, Finset.prod_range_succ]
  ring

/-- **General first-remainder telescope.**  If `π_i = m_i + ε_i` then

`∏_{i<n} π_i − ∏_{i<n} m_i = ∑_{j<n} (∏_{i<j} m_i) ε_j (∏_{j<i<n} π_i)`. -/
theorem prod_sub_prod_firstRemainder_telescope (m pi eps : ℕ → R) (n : ℕ)
    (hpi : ∀ i, pi i = m i + eps i) :
    (∏ i ∈ range n, pi i) - (∏ i ∈ range n, m i)
      = ∑ j ∈ range n, (∏ i ∈ range j, m i) * eps j * (∏ i ∈ Ico (j + 1) n, pi i) := by
  have key : ∀ j ∈ range n,
      partialModelProduct m pi n j - partialModelProduct m pi n (j + 1)
        = (∏ i ∈ range j, m i) * eps j * (∏ i ∈ Ico (j + 1) n, pi i) := by
    intro j hj
    rw [partialModelProduct_step m pi (Finset.mem_range.mp hj)]
    have : pi j - m j = eps j := by rw [hpi j]; ring
    rw [this]
  rw [← Finset.sum_congr rfl key,
    Finset.sum_range_sub' (fun j => partialModelProduct m pi n j) n,
    partialModelProduct_zero, partialModelProduct_top]

end Telescope

/-! ## 2. The boxed full-nine identity -/

section FullNine

variable {R : Type*} [CommRing R]

/-- `P_j` for the nine-coordinate family. -/
def P (mcan pi : ℕ → R) (j : ℕ) : R := partialModelProduct mcan pi 9 j

@[simp] theorem P_zero (mcan pi : ℕ → R) : P mcan pi 0 = ∏ i ∈ range 9, pi i :=
  partialModelProduct_zero mcan pi 9

@[simp] theorem P_nine (mcan pi : ℕ → R) : P mcan pi 9 = ∏ i ∈ range 9, mcan i :=
  partialModelProduct_top mcan pi 9

/-- `P_{j-1} − P_j = (∏_{i<j} m^{can}) ε_j (∏_{i>j} π_i)` for `1 ≤ j ≤ 9`. -/
theorem P_step (mcan pi eps : ℕ → R) (hpi : ∀ i, pi i = mcan i + eps i)
    {j : ℕ} (hj : j < 9) :
    P mcan pi j - P mcan pi (j + 1)
      = (∏ i ∈ range j, mcan i) * eps j * (∏ i ∈ Ico (j + 1) 9, pi i) := by
  rw [P, P, partialModelProduct_step mcan pi hj]
  have : pi j - mcan j = eps j := by rw [hpi j]; ring
  rw [this]

/-- **BOXED (§8 of the specification).**

```
∏_{i=1}^9 π_i − ∏_{i=1}^9 m_i^{can}
  = ∑_{j=1}^9 (∏_{i<j} m_i^{can}) (ρ_j − e_j^{pp}) (∏_{i>j} π_i).
```

Exact identity; the coordinates are indexed by `0,…,8`. -/
theorem fullNine_canonical_firstRemainder_telescope (mcan pi rho e : ℕ → R)
    (hpi : ∀ i, pi i = mcan i + (rho i - e i)) :
    (∏ i ∈ range 9, pi i) - (∏ i ∈ range 9, mcan i)
      = ∑ j ∈ range 9,
          (∏ i ∈ range j, mcan i) * (rho j - e j) * (∏ i ∈ Ico (j + 1) 9, pi i) :=
  prod_sub_prod_firstRemainder_telescope mcan pi (fun i => rho i - e i) 9 hpi

/-! ## 3. The `ρ` owner and the prime-power owner, each counted once -/

/-- The broad-major remainder owner at coordinate `j`. -/
def ownerRho (mcan pi rho : ℕ → R) (j : ℕ) : R :=
  (∏ i ∈ range j, mcan i) * rho j * (∏ i ∈ Ico (j + 1) 9, pi i)

/-- The prime-power owner at coordinate `j`. -/
def ownerPP (mcan pi e : ℕ → R) (j : ℕ) : R :=
  (∏ i ∈ range j, mcan i) * e j * (∏ i ∈ Ico (j + 1) 9, pi i)

/-- **Owner split.**  Each telescope term is exactly the broad-major owner
minus the prime-power owner; the prime-power correction is therefore counted
exactly once, at exactly one coordinate. -/
theorem fullNine_owner_split (mcan pi rho e : ℕ → R)
    (hpi : ∀ i, pi i = mcan i + (rho i - e i)) :
    (∏ i ∈ range 9, pi i) - (∏ i ∈ range 9, mcan i)
      = (∑ j ∈ range 9, ownerRho mcan pi rho j)
        - ∑ j ∈ range 9, ownerPP mcan pi e j := by
  rw [fullNine_canonical_firstRemainder_telescope mcan pi rho e hpi,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [ownerRho, ownerPP]
  ring

end FullNine

/-! ## 4. Unique first-remainder ownership -/

/-- **Unique owner.**  A labelled expansion term with at least one non-model
coordinate has a unique smallest such coordinate: the first remainder occurs at
exactly one place. -/
theorem firstRemainder_owner_unique (S : Finset ℕ) (hS : S.Nonempty) :
    ∃! j, j ∈ S ∧ ∀ i ∈ S, j ≤ i := by
  refine ⟨S.min' hS, ⟨S.min'_mem hS, fun i hi => S.min'_le i hi⟩, ?_⟩
  rintro j ⟨hjS, hj⟩
  exact le_antisymm (hj _ (S.min'_mem hS)) (S.min'_le j hjS)

/-- The owner index of a labelled expansion term, recorded as the set `S` of
its non-model coordinates (`0` on the model term, which owns no remainder). -/
noncomputable def ownerOf (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then S.min' h else 0

theorem ownerOf_mem {S : Finset ℕ} (hS : S.Nonempty) : ownerOf S ∈ S := by
  simp [ownerOf, hS, S.min'_mem]

theorem ownerOf_le {S : Finset ℕ} (hS : S.Nonempty) {i : ℕ} (hi : i ∈ S) :
    ownerOf S ≤ i := by
  simp only [ownerOf, dif_pos hS]
  exact S.min'_le i hi

theorem ownerOf_lt_of_subset_range {n : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hsub : S ⊆ range n) : ownerOf S < n :=
  Finset.mem_range.mp (hsub (ownerOf_mem hS))

/-- **Disjoint ownership.**  Distinct owners have disjoint term fibres. -/
theorem owner_fibres_disjoint {j j' : ℕ} (hjj : j ≠ j')
    (T : Finset (Finset ℕ)) :
    Disjoint (T.filter fun S => ownerOf S = j) (T.filter fun S => ownerOf S = j') := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro S hS hS'
  have h1 := (Finset.mem_filter.mp hS).2
  have h2 := (Finset.mem_filter.mp hS').2
  exact hjj (h1 ▸ h2 ▸ rfl)

/-- **Ownership partition.**  Every labelled expansion term with a non-model
coordinate is counted exactly once, in the fibre of its unique owner. -/
theorem firstRemainder_ownership_partition {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : Finset ℕ → M) :
    ∑ j ∈ range n,
        ∑ S ∈ ((range n).powerset.filter fun S => S.Nonempty) with ownerOf S = j, F S
      = ∑ S ∈ (range n).powerset.filter (fun S => S.Nonempty), F S := by
  classical
  refine Finset.sum_fiberwise_of_maps_to ?_ F
  intro S hS
  have h1 := Finset.mem_filter.mp hS
  exact Finset.mem_range.mpr
    (ownerOf_lt_of_subset_range h1.2 (Finset.mem_powerset.mp h1.1))

/-! ## 5. Occupancy / factorial symmetrisation firewall -/

/-- **Symmetrisation firewall.**  Finite occupancy summation with arbitrary
(in particular factorial) normalising coefficients preserves the linear
telescoping identity, with no hidden multiplicity and no double counting: the
`j`-th owner of the summed identity is exactly the weighted sum of the `j`-th
owners. -/
theorem occupancySum_preserves_firstRemainder_identity {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] (fam : Finset ι) (c A B : ι → R) (T : ι → ℕ → R)
    (n : ℕ) (h : ∀ o ∈ fam, A o - B o = ∑ j ∈ range n, T o j) :
    ∑ o ∈ fam, c o * (A o - B o) = ∑ j ∈ range n, ∑ o ∈ fam, c o * T o j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o ho => ?_
  rw [h o ho, Finset.mul_sum]

/-! ## 6. Prime-power correction: interface only -/

/-- **Interface, never inhabited here.**  The analytic prime-power saving
(`X^{-1/18+o(1)}` in the research bank) is *not* a theorem of this repository.
Any consumer must be handed this structure explicitly. -/
structure PrimePowerCorrectionBound where
  /-- The budget assigned to the prime-power owner. -/
  budget : ℝ
  /-- The (unproved) obligation that the prime-power owner respects its
  budget. -/
  owned : Prop

/-- The prime-power owner appears in the telescope exactly once per coordinate
and with the explicit sign `−1`; nothing about its size is asserted. -/
theorem primePower_owner_explicit {R : Type*} [CommRing R] (mcan pi rho e : ℕ → R)
    (hpi : ∀ i, pi i = mcan i + (rho i - e i)) :
    (∏ i ∈ range 9, pi i) - (∏ i ∈ range 9, mcan i)
        + ∑ j ∈ range 9, ownerPP mcan pi e j
      = ∑ j ∈ range 9, ownerRho mcan pi rho j := by
  rw [fullNine_owner_split mcan pi rho e hpi]
  ring

end FullNineOwner
end CurrentProgramme
end TwinPrimeProject
