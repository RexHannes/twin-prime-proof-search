import RequestProject.Main

namespace HalfSieve

/-- An algebraic uniqueness form: any kernel already known to be affine on the half
interval is fixed by the two endpoint normalizations. The differentiable three-variable
functional-equation route remains separate. -/
lemma exactHalfKernel_unique_affine (P : ℝ → ℝ) (a b : ℝ)
    (haffine : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), P t = a * t + b)
    (hzero : P 0 = 1) (hhalf : P (1 / 2) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), P t = 1 - 2 * t := by
  intro t ht
  have h0 := haffine 0 (by norm_num)
  have hh := haffine (1 / 2) (by norm_num)
  rw [hzero] at h0
  rw [hhalf] at hh
  rw [haffine t ht]
  norm_num at h0 hh ⊢
  have hb : b = 1 := h0.symm
  have ha : a = -2 := by linarith
  rw [ha, hb]
  ring

end HalfSieve
