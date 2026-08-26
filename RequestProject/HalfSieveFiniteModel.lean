import RequestProject.Main

namespace HalfSieve

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def subsetMass (x : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, x i

def cutoffSum (x : ι → ℝ) (γ : ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.powerset, if subsetMass x s ≤ γ then (-1 : ℝ) ^ s.card else 0

def fullCutoffMass (x : ι → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.powerset, (-1 : ℝ) ^ s.card * (1 - subsetMass x s)

def halfKernel (x : ι → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.powerset,
    if subsetMass x s ≤ (1 / 2 : ℝ) then
      (-1 : ℝ) ^ s.card * (1 - 2 * subsetMass x s) else 0

lemma alternatingSubsetCount :
    (∑ s ∈ (Finset.univ : Finset ι).powerset, (-1 : ℝ) ^ s.card) =
      if Fintype.card ι = 0 then 1 else 0 := by
  have h := Finset.sum_powerset (α := ι) (s := Finset.univ) (f := fun s => (-1 : ℝ) ^ s.card)
  rw [h]
  -- Now we need to simplify: ∑ j in range (n+1), ∑ t ∈ powersetCard j univ, (-1) ^ t.card
  -- For each j, the inner sum is (n.choose j) * (-1)^j
  let s : Finset ι := Finset.univ
  have h2 : ∀ j : ℕ, j ∈ Finset.range (s.card + 1) → ∑ t ∈ s.powersetCard j, (-1 : ℝ) ^ t.card = Nat.choose s.card j * (-1 : ℝ) ^ j := by
    intro j hj
    have : ∀ t ∈ s.powersetCard j, t.card = j := by
      intro t ht
      exact (Finset.mem_powersetCard.mp ht).2
    rw [Finset.sum_congr rfl (fun t ht => by rw [this t ht]), Finset.sum_const, Finset.card_powersetCard]
    ring
  rw [Finset.sum_congr rfl (fun j hj => h2 j hj)]
  have h3 : (Finset.univ : Finset ι).card = Fintype.card ι := by simp
  rw [h3]
  have hbinom : (1 + (-1 : ℝ)) ^ Fintype.card ι = ∑ j ∈ Finset.range (Fintype.card ι + 1), (Fintype.card ι).choose j * (-1 : ℝ) ^ j := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro m _
    simp [mul_comm]
  rw [← hbinom]
  cases hFintype : Fintype.card ι <;> simp [hFintype]

lemma alternatingWeightedCoordinate (x : ι → ℝ) (i : ι) :
    (∑ s ∈ (Finset.univ : Finset ι).powerset,
      (-1 : ℝ) ^ s.card * (if i ∈ s then x i else 0)) =
      if Fintype.card ι = 1 then -x i else 0 := by
  have h : (∑ s ∈ Finset.univ.powerset, (-1 : ℝ) ^ s.card * (if i ∈ s then x i else 0)) =
           x i * ∑ s ∈ Finset.univ.powerset, (-1 : ℝ) ^ s.card * (if i ∈ s then 1 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> ring
  rw [h]
  -- The sum ∑ s ∈ powerset, (-1)^s.card * (if i ∈ s then 1 else 0) is the alternating sum over subsets containing i
  -- This equals (-1) times the alternating sum over subsets of ι \ {i}
  -- The alternating sum over a set's powerset is (1-1)^|S| = 0 if |S| > 0, 1 if |S| = 0
  have altSum_powerset : ∀ (S : Finset ι), (∑ s ∈ S.powerset, (-1 : ℝ) ^ s.card) = (1 + -1 : ℝ) ^ S.card := by
    intro S
    have h1 : (1 + -1 : ℝ) ^ S.card = ((-1 + 1) : ℝ) ^ S.card := by ring
    rw [h1, add_pow]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_powersetCard]
    simp [Finset.sum_const, smul_eq_mul]
    ring
  -- Now we need to relate the sum over subsets containing i to the complement
  -- The sum over subsets containing i equals (-1) * (alternating sum over subsets of ι \ {i})
  let S := Finset.univ.erase i
  have hS_card : S.card = Fintype.card ι - 1 := by
    simp [S]
  -- The sum over subsets containing i equals (-1) times the alternating sum over subsets of S
  have sum_containing_i : (∑ s ∈ Finset.univ.powerset, (-1 : ℝ) ^ s.card * (if i ∈ s then 1 else 0)) =
      -∑ t ∈ S.powerset, (-1 : ℝ) ^ t.card := by
    -- First, simplify the if-then-else with multiplication
    have heq : ∀ s : Finset ι, (-1 : ℝ) ^ s.card * (if i ∈ s then 1 else 0) =
        if i ∈ s then (-1 : ℝ) ^ s.card else 0 := by
      intro s; split_ifs <;> simp
    simp_rw [heq]
    -- Now filter to subsets containing i
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    -- Use bijection between {s ∈ powerset | i ∈ s} and S.powerset
    rw [neg_eq_neg_one_mul, ← Finset.sum_neg_distrib]
    let T := Finset.filter (fun s => i ∈ s) Finset.univ.powerset
    apply Finset.sum_bij' (fun (s : Finset ι) (hs : s ∈ T) => Finset.erase s i)
                          (fun (t : Finset ι) (ht : t ∈ S.powerset) => Insert.insert i t)
    · -- Forward: s ∈ T implies s.erase i ∈ S.powerset
      intro s hs
      simp only [T, Finset.mem_filter, Finset.mem_powerset] at hs
      simp only [S, Finset.mem_powerset]
      exact Finset.erase_subset_erase _ (hs.1)
    · -- Backward: t ∈ S.powerset implies insert i t ∈ T
      intro t ht
      simp only [T, Finset.mem_filter, Finset.mem_powerset]
      simp only [S, Finset.mem_powerset] at ht
      refine ⟨Finset.insert_subset_iff.mpr ⟨Finset.mem_univ i, ?_⟩, Finset.mem_insert_self i t⟩
      exact Finset.Subset.trans ht (Finset.erase_subset _ _)
    · -- Left inverse: insert i (s.erase i) = s for s ∈ T
      intro s hs
      simp only [T, Finset.mem_filter, Finset.mem_powerset] at hs
      simp [hs.2]
    · -- Right inverse: (insert i t).erase i = t for t ∈ S.powerset
      intro t ht
      simp only [Finset.mem_powerset] at ht ⊢
      rw [Finset.erase_insert]
      by_cases hi : i ∈ t <;> simp [hi]
      have : i ∉ S := by simp [S]
      exact this (ht hi)
    · -- Value equality: (-1)^s.card = -(-1)^(s.erase i).card for s ∈ T
      intro s hs
      simp only [T, Finset.mem_filter, Finset.mem_powerset] at hs
      have hcard : s.card ≥ 1 := Finset.card_pos.mpr ⟨i, hs.2⟩
      rw [Finset.card_erase_of_mem hs.2]
      simp only [neg_one_mul]
      have heq : (-1 : ℝ) ^ s.card = (-1 : ℝ) * (-1) ^ (s.card - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hcard, pow_add]
        simp
      rw [heq]
      ring
  rw [sum_containing_i, altSum_powerset S]
  -- (1 + -1) = 0, so we need 0 ^ S.card
  simp only [add_neg_cancel]
  -- Need to handle: x i * -(0 ^ S.card) = if Fintype.card ι = 1 then -x i else 0
  have hne : Nonempty ι := ⟨i⟩
  cases' hc : Fintype.card ι with n
  · -- n = 0: contradiction since i : ι
    exfalso
    have : Fintype.card ι > 0 := Fintype.card_pos
    omega
  · -- n + 1
    cases n with
    | zero =>
      -- card ι = 1
      simp_all [hS_card]
    | succ m =>
      -- card ι = m + 2 > 1
      simp [hS_card, hc]

lemma fullCutoffMass_eq_primeIndicator (x : ι → ℝ)
    (hcard : 0 < Fintype.card ι) (hsum : ∑ i, x i = 1) :
    fullCutoffMass x = if Fintype.card ι = 1 then 1 else 0 := by
  unfold fullCutoffMass
  -- Expand: (-1)^s.card * (1 - subsetMass x s) = (-1)^s.card - (-1)^s.card * subsetMass x s
  simp_rw [mul_sub]
  -- Split the sum
  rw [Finset.sum_sub_distrib]
  -- Simplify * 1
  simp_rw [mul_one]
  -- First sum is alternatingSubsetCount
  rw [alternatingSubsetCount]
  -- Since hcard : 0 < Fintype.card ι, we have Fintype.card ι ≠ 0
  simp [Nat.pos_iff_ne_zero.mp hcard]
  -- Now need to show: - ∑ s, (-1)^s.card * subsetMass x s = if Fintype.card ι = 1 then 1 else 0
  -- Unfold subsetMass and reorder sums
  unfold subsetMass
  -- Transform ∑ s, (-1)^s.card * ∑ i ∈ s, x i = ∑ s, ∑ i ∈ s, (-1)^s.card * x i
  simp_rw [Finset.mul_sum]
  -- First convert ∑ i ∈ s, f i to ∑ i, (if i ∈ s then f i else 0)
  -- Then swap the sums
  have step1 : ∀ s : Finset ι, ∑ i ∈ s, (-1 : ℝ) ^ s.card * x i =
               ∑ i : ι, (if i ∈ s then (-1 : ℝ) ^ s.card * x i else 0) := by
    intro s
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  simp_rw [step1]
  -- Swap order of summation
  rw [← Finset.sum_comm]
  -- Now match alternatingWeightedCoordinate
  have step2 : ∀ i : ι, ∑ s : Finset ι, (if i ∈ s then (-1 : ℝ) ^ s.card * x i else 0) =
               ∑ s : Finset ι, (-1 : ℝ) ^ s.card * (if i ∈ s then x i else 0) := by
    intro i
    congr 1 with s
    split_ifs <;> ring
  simp_rw [step2]
  -- Convert sum over Finset ι to sum over powerset
  rw [← Finset.powerset_univ (α := ι)]
  -- Apply alternatingWeightedCoordinate
  simp_rw [alternatingWeightedCoordinate]
  -- Simplify: -∑ i, (if card = 1 then -x i else 0) = if card = 1 then 1 else 0
  split_ifs with h1
  · -- case Fintype.card ι = 1
    simp [h1, hsum]
  · -- case Fintype.card ι ≠ 1
    simp [h1]

end

end HalfSieve
