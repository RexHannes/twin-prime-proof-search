import RequestProject.Options
namespace TwinPrimeProject.NANC
open scoped BigOperators

def cardSign {α : Type} (s : Finset α) : Int := (-1 : Int) ^ s.card

theorem cardSign_eq_one_or_neg_one {α : Type} (s : Finset α) :
    cardSign s = 1 ∨ cardSign s = -1 := by
  exact neg_one_pow_eq_or ℤ s.card

theorem cardSign_mul_of_disjoint {α : Type} [DecidableEq α]
    {s t : Finset α} (h : Disjoint s t) : cardSign (s ∪ t) = cardSign s * cardSign t := by
  simp [cardSign, Finset.card_union_of_disjoint h, pow_add]

theorem rho_minus_one_zero_if_one (n : ℕ) (ρ : ℤ) (hρ : ρ = 1) :
    (-1 : ℤ)^n * ρ - (-1 : ℤ)^n = 0 := by simp [hρ]

theorem rho_minus_one_neg_if_zero (n : ℕ) (ρ : ℤ) (hρ : ρ = 0) :
    (-1 : ℤ)^n * ρ - (-1 : ℤ)^n = -(-1 : ℤ)^n := by simp [hρ]
end NANC
