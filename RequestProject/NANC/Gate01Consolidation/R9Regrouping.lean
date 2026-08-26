import RequestProject.R9ConvolutionAlgebra

/-!
# BANK N / O / P / Q — the nine-block family, the 4|5 regrouping and multiplicity

Only the **combinatorics** of nine labelled prime-block slots is formalised.
No primality distribution and no analytic input occurs.

* **BANK N.**  Slots `Fin 9`, subsets `J`, formal exponent mass `|J|/9` and
  complementary mass `(9−|J|)/9`; the eight binary splits `1|8, …, 8|1` all
  exist (`exists_block_split`).
* **BANK O.**  From the `2|7` representation `m = p₁p₂`, `n = p₃⋯p₉`, splitting
  `n = n₂ n₅` and setting `u = m n₂`, `v = n₅` gives **REGROUP-PROD** `u v = m n`
  and **REGROUP-CONG** `m n ≡ −2 (q) ↔ u v ≡ −2 (q)`; the formal exponents are
  `u = X^{4/9}`, `v = X^{5/9}` (exact rational arithmetic, no asymptotics).
* **BANK P.**  Convention A (labelled disjoint boxes): the slot of a factor is
  unique, so a slot-respecting tuple is determined by its multiset of factors
  (`labelledBlockRegroupingInjective`).  Convention B (symmetric
  ordered-distinct convolution) reuses the project's existing
  `r9BlockConvolutionDecomposition`; the only new statement is that a fixed
  nonzero multiplicative constant does not change rational exponent bookkeeping
  (`constant_does_not_change_exponent`).
* **BANK Q.**  Among *pure nine-block binary partitions* the imbalance
  `|2j−9|/9` is minimised exactly at `j = 4, 5`, with value `1/9`
  (`blockImbalance_min`).  Nothing is claimed about regroupings that involve
  other variables.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-! ## BANK N — nine labelled block slots -/

/-- The formal exponent mass of one block. -/
def blockMass : ℚ := 1 / 9

/-- The formal exponent mass carried by a set of slots. -/
def massOf (J : Finset (Fin 9)) : ℚ := (J.card : ℚ) / 9

theorem massOf_eq_card_mul_blockMass (J : Finset (Fin 9)) :
    massOf J = (J.card : ℚ) * blockMass := by
  unfold massOf blockMass; ring

/-- The mass of a `j`-element slot set is `j/9`, that of its complement
`(9−j)/9`, and the two add up to `1`. -/
theorem massOf_compl (J : Finset (Fin 9)) :
    massOf Jᶜ = (9 - (J.card : ℚ)) / 9 ∧ massOf J + massOf Jᶜ = 1 := by
  have hcard : (Jᶜ).card = 9 - J.card := by
    rw [Finset.card_compl]
    simp
  have hle : J.card ≤ 9 := by
    have := Finset.card_le_univ J
    simpa using this
  constructor
  · rw [massOf, hcard]
    congr 1
    have : ((9 - J.card : ℕ) : ℚ) = 9 - (J.card : ℚ) := by
      have : ((9 - J.card : ℕ) : ℤ) = 9 - (J.card : ℤ) := by omega
      exact_mod_cast this
    exact this
  · rw [massOf, massOf, hcard]
    have : ((9 - J.card : ℕ) : ℚ) = 9 - (J.card : ℚ) := by
      have : ((9 - J.card : ℕ) : ℤ) = 9 - (J.card : ℤ) := by omega
      exact_mod_cast this
    rw [this]
    ring

/-- Every binary split `j | 9−j` of the nine labelled blocks is realised. -/
theorem exists_block_split (j : ℕ) (hj : j ≤ 9) :
    ∃ J : Finset (Fin 9), J.card = j ∧ massOf J = (j : ℚ) / 9
      ∧ massOf Jᶜ = (9 - (j : ℚ)) / 9 := by
  obtain ⟨J, -, hJcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin 9)))
    (n := j) (by simpa using hj)
  refine ⟨J, hJcard, by rw [massOf, hJcard], ?_⟩
  rw [(massOf_compl J).1, hJcard]

/-- The multiplicative splitting of the nine slot values along `J` and `Jᶜ`. -/
theorem prod_split (x : Fin 9 → ℕ) (J : Finset (Fin 9)) :
    (∏ i ∈ J, x i) * (∏ i ∈ Jᶜ, x i) = ∏ i, x i :=
  Finset.prod_mul_prod_compl J x

/-! ## BANK O — the 4|5 regrouping -/

/-- **REGROUP-PROD.**  Regrouping the `2|7` factorisation `m n` as
`u = m n₂`, `v = n₅` with `n = n₂ n₅` preserves the product. -/
theorem regroup_prod (m n n₂ n₅ : ℕ) (hn : n = n₂ * n₅) :
    (m * n₂) * n₅ = m * n := by
  subst hn; ring

/-- **REGROUP-CONG.**  Consequently the shifted congruence is unchanged. -/
theorem regroup_cong (q m n n₂ n₅ : ℕ) (hn : n = n₂ * n₅) :
    (q ∣ m * n + 2) ↔ (q ∣ (m * n₂) * n₅ + 2) := by
  rw [regroup_prod m n n₂ n₅ hn]

/-- Formal exponent of the regrouped left variable `u = m n₂`
(two `m`-blocks plus two `n`-blocks). -/
def expU : ℚ := 4 / 9

/-- Formal exponent of the regrouped right variable `v = n₅` (five blocks). -/
def expV : ℚ := 5 / 9

theorem expU_eq : expU = 2 * blockMass + 2 * blockMass := by unfold expU blockMass; norm_num

theorem expV_eq : expV = 5 * blockMass := by unfold expV blockMass; norm_num

theorem expU_add_expV : expU + expV = 1 := by unfold expU expV; norm_num

/-- The `2|7` short variable exponent. -/
def expTwoSeven : ℚ := 2 / 9

theorem expTwoSeven_lt_expU : expTwoSeven < expU := by unfold expTwoSeven expU; norm_num

/-! ## BANK P — multiplicity conventions -/

/-- **Convention A.**  With nine pairwise disjoint labelled boxes, a factor
determines its slot. -/
theorem labelled_slot_unique {I : Fin 9 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j)) {x : ℕ} {i j : Fin 9}
    (hi : x ∈ I i) (hj : x ∈ I j) : i = j := by
  by_contra hne
  exact (Finset.disjoint_left.mp (hdisj i j hne) hi) hj

/-- **LabelledBlockRegroupingInjective.**  Under Convention A a slot-respecting
tuple is determined by the multiset of its entries: the regrouping has
multiplicity one. -/
theorem labelledBlockRegroupingInjective {I : Fin 9 → Finset ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j)) {x y : Fin 9 → ℕ}
    (hx : ∀ i, x i ∈ I i) (hy : ∀ i, y i ∈ I i)
    (hmul : Multiset.map x Finset.univ.val = Multiset.map y Finset.univ.val) :
    x = y := by
  funext i
  have hxmem : x i ∈ Multiset.map x Finset.univ.val :=
    Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩
  rw [hmul] at hxmem
  obtain ⟨j, -, hxy⟩ := Multiset.mem_map.mp hxmem
  have hij : i = j := labelled_slot_unique hdisj (hx i) (hxy ▸ hy j)
  rw [← hij] at hxy
  exact hxy.symm

/-- **Convention B.**  A fixed nonzero multiplicative constant (a symmetrisation
factor `κ`) does not change rational exponent bookkeeping: it only rescales the
implied constant. -/
theorem constant_does_not_change_exponent (kappa : ℝ) (hk : kappa ≠ 0) (S g : ℕ → ℝ) :
    (∃ C > 0, ∀ X, |kappa * S X| ≤ C * g X) ↔ (∃ C > 0, ∀ X, |S X| ≤ C * g X) := by
  have hkpos : 0 < |kappa| := abs_pos.mpr hk
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C / |kappa|, div_pos hC hkpos, fun X => ?_⟩
    have h := hbound X
    rw [abs_mul] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hkpos]
    calc |S X| * |kappa| = |kappa| * |S X| := by ring
      _ ≤ C * g X := h
  · rintro ⟨C, hC, hbound⟩
    refine ⟨|kappa| * C, mul_pos hkpos hC, fun X => ?_⟩
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbound X) (le_of_lt hkpos)

/-! ## BANK Q — the optimal pure nine-block binary split -/

/-- The imbalance of the pure binary split `j | 9−j`. -/
def blockImbalance (j : ℕ) : ℚ := |(2 * (j : ℚ) - 9)| / 9

theorem blockImbalance_four : blockImbalance 4 = 1 / 9 := by
  unfold blockImbalance; norm_num

theorem blockImbalance_five : blockImbalance 5 = 1 / 9 := by
  unfold blockImbalance; norm_num

/-- **BLOCK-PARITY.**  Among the pure nine-block binary partitions
`j = 1, …, 8` the imbalance is at least `1/9`, with equality exactly for
`j = 4` and `j = 5`. -/
theorem blockImbalance_min (j : ℕ) (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    1 / 9 ≤ blockImbalance j ∧ (blockImbalance j = 1 / 9 ↔ (j = 4 ∨ j = 5)) := by
  interval_cases j <;> constructor <;> simp [blockImbalance] <;> norm_num

end Gate01Consolidation
end TwinPrimeProject
