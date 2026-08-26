import RequestProject.HalfSieveParityProjection

namespace HalfSieve

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def polynomialKernel (P : ℝ → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.powerset,
    if subsetMass x s ≤ (1 / 2 : ℝ) then (-1 : ℝ) ^ s.card * P (subsetMass x s)
    else 0

def polynomialWeight (P : ℝ → ℝ) (t : ℝ) : ℝ := -deriv P t

lemma polynomialKernel_add (P R : ℝ → ℝ) (x : ι → ℝ) :
    polynomialKernel (fun t => P t + R t) x = polynomialKernel P x + polynomialKernel R x := by
  simp [polynomialKernel]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext s
  split_ifs <;> ring

lemma polynomialKernel_smul (c : ℝ) (P : ℝ → ℝ) (x : ι → ℝ) :
    polynomialKernel (fun t => c * P t) x = c * polynomialKernel P x := by
  simp [polynomialKernel]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h <;> ring

lemma polynomialKernel_boundary_zero (P : ℝ → ℝ) (x : ι → ℝ)
    (hP : P (1 / 2 : ℝ) = 0) (s : Finset ι)
    (hs : subsetMass x s = (1 / 2 : ℝ)) :
    (-1 : ℝ) ^ s.card * P (subsetMass x s) = 0 := by
  rw [hs, hP, mul_zero]

lemma polynomialKernel_singleton (P : ℝ → ℝ) (x : ι → ℝ)
    (hP0 : P 0 = 1) (hPhalf : P (1 / 2 : ℝ) = 0)
    (hsum : ∑ i, x i = 1) (hcard : Fintype.card ι = 1) :
    polynomialKernel P x = 1 := by
  -- When Fintype.card ι = 1, there's exactly one element, so powerset has 2 elements: ∅ and univ
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hcard
  -- The powerset consists of ∅ and {a}
  have hpow : Finset.univ.powerset = ({∅, Finset.univ} : Finset (Finset ι)) := by
    ext s
    simp [Finset.mem_insert, Finset.mem_singleton]
    by_cases hs : s = ∅ <;> simp [hs]
    -- s ≠ ∅, so s contains some element, which must be a
    obtain ⟨c, hc⟩ := Finset.nonempty_of_ne_empty hs
    have hac : a ∈ s := by rw [← ha c]; exact hc
    apply Finset.eq_univ_of_forall
    intro b
    rw [ha b]
    exact hac
  rw [polynomialKernel, hpow]
  simp [subsetMass]
  rw [Finset.sum_insert, Finset.sum_singleton]
  · simp [hP0, hsum]; norm_num
  · haveI : Nonempty ι := ⟨a⟩
    simp [Finset.mem_singleton]; exact Finset.univ_nonempty.ne_empty.symm

lemma polynomialKernel_support (P : ℝ → ℝ) (x : ι → ℝ) (s : Finset ι)
    (hs : (1 / 2 : ℝ) < subsetMass x s) :
    (if subsetMass x s ≤ (1 / 2 : ℝ) then
      (-1 : ℝ) ^ s.card * P (subsetMass x s) else 0) = 0 := by
  rw [if_neg (not_le.mpr hs)]

end

end HalfSieve
