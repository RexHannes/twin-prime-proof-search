import NANC.BasicSigns

namespace NANC

open scoped BigOperators

 theorem rho_one_cells_cancel {ι G : Type*} [DecidableEq ι] [AddCommGroup G]
    (U : Finset ι) (I : Finset ι → G) (ρ : Finset ι → Bool) :
    (∑ J ∈ U.powerset, (if ρ J then sgnCard J • I J else 0)) -
      (∑ J ∈ U.powerset, sgnCard J • I J) =
      -(∑ J ∈ U.powerset with ρ J = false, sgnCard J • I J) := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h : ρ J = true
  · simp [h]
  · simp [h]

 theorem rho_one_cells_cancel_shifted {ι G : Type*} [DecidableEq ι] [AddCommGroup G]
    (U : Finset ι) (I : Finset ι → G) (ρ : Finset ι → Bool) :
    (∑ J ∈ U.powerset, (if ρ J then sgnCard J • I J else 0)) -
      (∑ J ∈ U.powerset, sgnCard J • I J) =
      ∑ J ∈ U.powerset with ρ J = false, (-sgnCard J) • I J := by
  rw [rho_one_cells_cancel]
  simp only [Finset.sum_neg_distrib, neg_smul]

 theorem prime_reinjection_identity {P G : Type*} [Fintype P] [AddCommGroup G]
    (a b w : P → G) (hw : ∀ p, w p = a p - b p) :
    -(∑ p, w p) = (∑ p, b p) - ∑ p, a p := by
  simp_rw [hw]
  rw [Finset.sum_sub_distrib]
  abel

end NANC
