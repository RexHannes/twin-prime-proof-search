import Mathlib

/-!
# Factorability subset-sum polytope (§9)

`FACTORABILITY_SUBSET_SUM_POLYTOPE`.

For a dyadic exponent vector `β : Fin k → ℝ` with `∑ β_i = 1/3`, the set of
achievable *grouped factorization scales* is

`𝒫(β) = { ∑_{i ∈ I} β_i : I ⊆ [k] }`,

realized here as a `Finset ℝ` (hence automatically finite).  We prove:

1. `mem_polytope`: every grouped factor exponent `∑_{i∈I} β_i` lies in `𝒫(β)`;
2. `mem_polytope_iff`: `𝒫(β)` is *exactly* the set of subset sums — no other
   scale is available without further coefficient identities;
3. `exists_block`: some single block has size `≥ 1/(3k)`
   (pigeonhole on the mean);
4. `one_sixth_not_automatic`, `one_eighth_not_automatic`,
   `one_twelfth_not_automatic`: with the indivisible witness `k = 1`,
   `β = (1/3)`, none of `1/6, 1/8, 1/12` lie in `𝒫(β)` — so generic
   well-factorability at these scales is *not* automatic;
5. `polytope_indivisible_one`: the `k = 1`, `β₁ = 1/3` case gives
   `𝒫(β) = {0, 1/3}` (the admissible indivisible case).

Status: `LEAN_PROVED`.
-/

open scoped BigOperators

namespace PrimeShortWindow.Factorability

/-- The achievable factorization-scale set `𝒫(β) = { ∑_{i∈I} β_i : I ⊆ [k] }`. -/
noncomputable def polytope (k : ℕ) (β : Fin k → ℝ) : Finset ℝ :=
  (Finset.univ.powerset).image (fun I => ∑ i ∈ I, β i)

/-- (1) Every genuine grouped factor exponent `∑_{i∈I} β_i` belongs to `𝒫(β)`. -/
theorem mem_polytope {k : ℕ} (β : Fin k → ℝ) (I : Finset (Fin k)) :
    (∑ i ∈ I, β i) ∈ polytope k β := by
  unfold polytope; rw [Finset.mem_image]
  exact ⟨I, by simp, rfl⟩

/-- (2) `𝒫(β)` is *exactly* the set of subset sums: no other scale follows
without further coefficient identities. -/
theorem mem_polytope_iff {k : ℕ} (β : Fin k → ℝ) (x : ℝ) :
    x ∈ polytope k β ↔ ∃ I : Finset (Fin k), (∑ i ∈ I, β i) = x := by
  unfold polytope; rw [Finset.mem_image]
  constructor
  · rintro ⟨I, _, h⟩; exact ⟨I, h⟩
  · rintro ⟨I, h⟩; exact ⟨I, by simp, h⟩

/-- (3) A block of size at least `1/(3k)` exists (pigeonhole: `max ≥ mean`). -/
theorem exists_block {k : ℕ} (β : Fin k → ℝ) (hk : 0 < k) (hsum : ∑ i, β i = 1 / 3) :
    ∃ i, (1 : ℝ) / (3 * k) ≤ β i := by
  by_contra h
  push_neg at h
  have hlt : ∑ i, β i < ∑ _i : Fin k, (1 : ℝ) / (3 * k) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk)
    · intro i _; exact h i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum, nsmul_eq_mul] at hlt
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  field_simp at hlt
  linarith

/-- (5) The indivisible case `k = 1`, `β₁ = 1/3`: `𝒫(β) = {0, 1/3}`. -/
theorem polytope_indivisible_one (x : ℝ) :
    x ∈ polytope 1 (![(1 : ℝ) / 3]) ↔ x = 0 ∨ x = 1 / 3 := by
  unfold polytope; rw [Finset.mem_image]
  constructor
  · rintro ⟨I, _, rfl⟩
    have hI : I = ∅ ∨ I = {0} := by
      have hsub : I ⊆ {0} := fun x _ => by fin_cases x; simp
      rwa [Finset.subset_singleton_iff] at hsub
    rcases hI with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩
    · exact ⟨{0}, Finset.mem_powerset.mpr (Finset.subset_univ _), by simp⟩

/-- (4a) `1/6` is not automatically an available scale. -/
theorem one_sixth_not_automatic : (1 : ℝ) / 6 ∉ polytope 1 (![(1 : ℝ) / 3]) := by
  rw [polytope_indivisible_one]; push_neg; constructor <;> norm_num

/-- (4b) `1/8` is not automatically an available scale. -/
theorem one_eighth_not_automatic : (1 : ℝ) / 8 ∉ polytope 1 (![(1 : ℝ) / 3]) := by
  rw [polytope_indivisible_one]; push_neg; constructor <;> norm_num

/-- (4c) `1/12` is not automatically an available scale. -/
theorem one_twelfth_not_automatic : (1 : ℝ) / 12 ∉ polytope 1 (![(1 : ℝ) / 3]) := by
  rw [polytope_indivisible_one]; push_neg; constructor <;> norm_num

/-- Summary witness for §9(4): there is an admissible `β` (with `∑ β = 1/3`)
whose polytope contains none of `1/6, 1/8, 1/12`; hence generic
well-factorability at these scales is refuted. -/
theorem generic_wellfactorability_refuted :
    ∃ (k : ℕ) (β : Fin k → ℝ), (∑ i, β i = 1 / 3) ∧
      (1 : ℝ) / 6 ∉ polytope k β ∧ (1 : ℝ) / 8 ∉ polytope k β ∧
      (1 : ℝ) / 12 ∉ polytope k β :=
  ⟨1, ![(1 : ℝ) / 3], by simp, one_sixth_not_automatic, one_eighth_not_automatic,
    one_twelfth_not_automatic⟩

end PrimeShortWindow.Factorability
