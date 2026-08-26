import RequestProject.HalfSieveFiniteModel

namespace HalfSieve

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma subsetMass_compl (x : ι → ℝ) (hsum : ∑ i, x i = 1) (s : Finset ι) :
    subsetMass x sᶜ = 1 - subsetMass x s := by
  unfold subsetMass
  have h := Finset.sum_add_sum_compl s x
  linarith

lemma subsetSign_compl (s : Finset ι) :
    (-1 : ℝ) ^ (sᶜ).card =
      (-1 : ℝ) ^ Fintype.card ι * (-1 : ℝ) ^ s.card := by
  have h : sᶜ.card + s.card = Fintype.card ι := Finset.card_compl_add_card s
  rw [← h, pow_add]
  have hsq : (-1 : ℝ) ^ s.card * (-1 : ℝ) ^ s.card = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [mul_assoc, hsq, mul_one]

lemma halfKernel_boundary_weight_zero (x : ι → ℝ) (s : Finset ι)
    (h : subsetMass x s = (1 / 2 : ℝ)) :
    (-1 : ℝ) ^ s.card * (1 - 2 * subsetMass x s) = 0 := by
  rw [h]; norm_num

lemma halfKernel_singleton (x : ι → ℝ) (hsum : ∑ i, x i = 1)
    (hcard : Fintype.card ι = 1) : halfKernel x = 1 := by
  unfold halfKernel
  -- Get the unique element
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨i, hi⟩
  -- Rewrite the powerset sum
  have hpow : Finset.univ.powerset = {∅, {i}} := by
    ext s
    simp only [Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton, Finset.subset_iff]
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · by_cases hse : s = ∅
      · exact Or.inl hse
      · have hne : s.Nonempty := Finset.nonempty_of_ne_empty hse
        have := Classical.choose_spec hne
        rw [hi (Classical.choose hne)] at this
        exact Or.inr (Finset.eq_singleton_iff_unique_mem.mpr ⟨this, fun k _ => hi k⟩)
    · rcases hs with rfl | rfl <;> simp
  rw [hpow, Finset.sum_insert, Finset.sum_singleton]
  · simp [subsetMass]
    have hxi : x i = 1 := by
      have h' : ∑ j ∈ Finset.univ, x j = 1 := hsum
      rw [Finset.sum_eq_single i (fun j _ hji => ?_) (by simp)] at h'
      · exact h'
      · exact absurd (hi j) hji
    norm_num [hxi]
  · simp

end HalfSieve
