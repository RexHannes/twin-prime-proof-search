import RequestProject.Options
namespace TwinPrimeProject.NANC
open scoped BigOperators

theorem variance_identity_finite {G : Type} [Fintype G] [Nonempty G]
    (A : G → ℝ) :
    (∑ c, (A c)^2) - (1 / Fintype.card G : ℝ) * (∑ c, A c)^2 =
      ∑ c, (A c - (1 / Fintype.card G : ℝ) * ∑ d, A d)^2 := by
  let n : ℝ := Fintype.card G
  let S : ℝ := ∑ c, A c
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ c, (A c * ((1/n)*S)) = S * ((1/n)*S) := by
    rw [Finset.sum_mul]
  have hsum2 : ∑ c, (2 * A c * ((1/n)*S)) = 2 * S * ((1/n)*S) := by
    calc
      _ = ∑ c, 2 * (A c * ((1/n)*S)) := by apply Finset.sum_congr rfl; intro i hi; ring
      _ = 2 * (∑ c, A c * ((1/n)*S)) := by
        exact (Finset.mul_sum (s := Finset.univ) (f := fun c => A c * ((1/n)*S)) 2).symm
      _ = _ := by rw [hsum]; ring
  have hconst : ∑ _c : G, ((1/n)*S)^2 = n * ((1/n)*S)^2 := by
    simp [n]
  change (∑ c, (A c)^2) - (1/n)*S^2 = ∑ c, (A c - (1/n)*S)^2
  simp_rw [sub_sq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [hsum2, hconst]
  dsimp [S]
  field_simp
  ring

end TwinPrimeProject.NANC
