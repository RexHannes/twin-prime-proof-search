import Mathlib

namespace NANC

def sgnCard {α : Type*} (s : Finset α) : ℤ := (-1 : ℤ) ^ s.card

@[simp] theorem sgnCard_empty {α : Type*} : sgnCard (∅ : Finset α) = 1 := by simp [sgnCard]

 theorem sgnCard_disjoint_union {α : Type*} [DecidableEq α]
    (J K U : Finset α) (hJK : Disjoint J K) (hU : J ∪ K = U) :
    sgnCard J * sgnCard K = sgnCard U := by
  rw [← hU]
  simp [sgnCard, hJK, pow_add]

 theorem rho_sign_cancellation {α : Type*} (J : Finset α) (ρ : ℤ)
    (hρ : ρ = 0 ∨ ρ = 1) :
    sgnCard J * ρ - sgnCard J = if ρ = 1 then 0 else -sgnCard J := by
  rcases hρ with rfl | rfl <;> simp

end NANC
