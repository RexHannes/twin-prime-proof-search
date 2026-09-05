/-
# Gate1B / R11 : the 5|4|2 allocation combinatorics (§3, §4)

The ten large atoms are split into ordered groups of sizes `4 | 4 | 2`.  There are exactly
`C(10,4) * C(6,4) = 3150 = 10!/(4!·4!·2!)` such ordered allocations, and for a
multiplicative representation-blind atom weight the grouped products always recombine to the
full product, so the normalized average over allocations is the full weight.

The internal factorial normalization is recorded exactly: the outer CARD5 coefficient is
`252`, **not** `252 * 3150`.
-/
import Gate1B.R11.Card5

namespace Gate1B.R11

set_option maxRecDepth 40000

open Finset

/-! ## 1. The ordered 4|4|2 allocations -/

/-- Ordered `4|4|2` allocations of the ten large atoms, recorded by their first two groups;
the third group is the complement `univ \ (A ∪ B)`, of size `2`. -/
def Alloc442 : Finset (Finset (Fin 10) × Finset (Fin 10)) :=
  (Finset.univ.powersetCard 4).biUnion fun A =>
    ((Finset.univ \ A).powersetCard 4).image (Prod.mk A)

theorem choose_ten_four : Nat.choose 10 4 = 210 := by decide

theorem choose_six_four : Nat.choose 6 4 = 15 := by decide

theorem choose_mul_choose_442 : Nat.choose 10 4 * Nat.choose 6 4 = 3150 := by decide

/-- **The `4|4|2` allocation count is exactly 3150.** -/
theorem card_Alloc442 : Alloc442.card = 3150 := by
  rw [Alloc442, Finset.card_biUnion]
  · have key : ∀ A ∈ (Finset.univ.powersetCard 4 : Finset (Finset (Fin 10))),
        (((Finset.univ \ A).powersetCard 4).image (Prod.mk A)).card = 15 := by
      intro A hA
      have hcard : A.card = 4 := (Finset.mem_powersetCard.mp hA).2
      have h6 : (Finset.univ \ A).card = 6 := by
        rw [Finset.card_univ_diff, hcard]; rfl
      rw [Finset.card_image_of_injective _ (fun x y h => (Prod.mk.injEq A x A y ▸ h).2),
        Finset.card_powersetCard, h6]
      decide
    rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ]
    rfl
  · intro A _ B _ hAB
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro x ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    exact hAB (congrArg Prod.fst hb).symm

/-- Membership in `Alloc442`: two disjoint four-element groups. -/
theorem mem_Alloc442 {P : Finset (Fin 10) × Finset (Fin 10)} (h : P ∈ Alloc442) :
    P.1.card = 4 ∧ P.2.card = 4 ∧ Disjoint P.1 P.2 := by
  simp only [Alloc442, Finset.mem_biUnion, Finset.mem_image, Finset.mem_powersetCard] at h
  obtain ⟨X, ⟨-, hX4⟩, Y, ⟨hYsub, hY4⟩, hEq⟩ := h
  subst hEq
  exact ⟨hX4, hY4, Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_sdiff.mp (hYsub hb)).2 ha⟩

/-- The residual group of an allocation has exactly two atoms. -/
theorem card_residual_of_mem_Alloc442 {P : Finset (Fin 10) × Finset (Fin 10)}
    (h : P ∈ Alloc442) : (Finset.univ \ (P.1 ∪ P.2)).card = 2 := by
  obtain ⟨h1, h2, hdisj⟩ := mem_Alloc442 h
  rw [Finset.card_univ_diff, Finset.card_union_of_disjoint hdisj, h1, h2]
  rfl

/-! ## 2. Recombination and normalization -/

variable {R : Type*} [CommRing R]

/-- For any allocation the three grouped products recombine to the full atom product. -/
theorem grouped_prod_recombines (F : Fin 10 → R) {P : Finset (Fin 10) × Finset (Fin 10)}
    (h : P ∈ Alloc442) :
    (∏ i ∈ P.1, F i) * (∏ i ∈ P.2, F i) * ∏ i ∈ Finset.univ \ (P.1 ∪ P.2), F i
      = ∏ i, F i := by
  obtain ⟨-, -, hdisj⟩ := mem_Alloc442 h
  rw [← Finset.prod_union hdisj, mul_comm, Finset.prod_sdiff (Finset.subset_univ _)]

/-- **`factor542` normalization, integral form.**  Summing the grouped weight over all
ordered `4|4|2` allocations gives exactly `3150` copies of the full atom weight. -/
theorem factor542_normalization_mul (F : Fin 10 → R) :
    ∑ P ∈ Alloc442,
        (∏ i ∈ P.1, F i) * (∏ i ∈ P.2, F i) * ∏ i ∈ Finset.univ \ (P.1 ∪ P.2), F i
      = 3150 * ∏ i, F i := by
  rw [Finset.sum_congr rfl fun P hP => grouped_prod_recombines F hP, Finset.sum_const,
    card_Alloc442, nsmul_eq_mul]
  norm_num

/-- **`factor542` normalization, averaged form** over a field of characteristic zero
(division is performed only after casting, never in `ℕ`). -/
theorem factor542_normalization {K : Type*} [Field K] [CharZero K] (F : Fin 10 → K) :
    (1 / 3150 : K) * ∑ P ∈ Alloc442,
        (∏ i ∈ P.1, F i) * (∏ i ∈ P.2, F i) * ∏ i ∈ Finset.univ \ (P.1 ∪ P.2), F i
      = ∏ i, F i := by
  rw [factor542_normalization_mul]
  field_simp

/-! ## 3. Internal factorial normalization (§4) -/

theorem factorial_ten_split : Nat.factorial 10 = 3150 * (Nat.factorial 4 * Nat.factorial 4 *
    Nat.factorial 2) := by decide

theorem factorial_quotient_eq_3150 :
    Nat.factorial 10 / (Nat.factorial 4 * Nat.factorial 4 * Nat.factorial 2) = 3150 := by decide

/-- The four normalization factors `1/4!`, `1/4!`, `1/2!`, `1/3150` consume exactly `10!`:
they do **not** create an extra `10!` multiplicity. -/
theorem factorial_normalization_no_extra_multiplicity :
    (1 / (Nat.factorial 4 : ℚ)) * (1 / (Nat.factorial 4 : ℚ)) * (1 / (Nat.factorial 2 : ℚ))
        * (1 / 3150) * (Nat.factorial 10 : ℚ) = 1 := by
  norm_num [Nat.factorial]

/-- **Outer coefficient ledger.**  The total CARD5 `l1` coefficient is `252`, not
`252 * 3150`. -/
theorem card5_outer_coefficient_ledger :
    card5Coefficient = 252 ∧ card5Coefficient ≠ 252 * 3150 := by
  refine ⟨rfl, ?_⟩
  rw [card5Coefficient]
  decide

theorem ratio_252_3150 : (252 : ℚ) / 3150 = 2 / 25 := by norm_num

end Gate1B.R11
