import RequestProject.Options
namespace TwinPrimeProject.NANC
open scoped BigOperators

theorem rho_one_cells_cancel {ι G : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] (I : ι → G) (sgn : ι → ℤ) (ρ : ι → ℤ)
    (hρ : ∀ j, ρ j = 1) :
    ∑ j, (sgn j * ρ j) • (I j) = ∑ j, (sgn j) • (I j) := by
  apply Finset.sum_congr rfl
  intro j _
  simp [hρ]

theorem rho_zero_residual_identity {ι G : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] (I : ι → G) (sgn : ι → ℤ) (ρ : ι → ℤ)
    (hρ : ∀ j, ρ j = 0 ∨ ρ j = 1) :
    (∑ j, (sgn j * ρ j) • (I j)) - ∑ j, (sgn j) • (I j) =
      -∑ j ∈ Finset.univ.filter (fun j => ρ j = 0), (sgn j) • (I j) := by
  classical
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rcases hρ j with h | h
  · simp [h]
  · simp [h]
end NANC
