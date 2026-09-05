/-
# Gate1B / R11 : CARD5 exact combinatorics (§2)

The CARD5 selector keeps the distinguished coordinate `p0` and chooses exactly five of the
ten large coordinates.  There are `C(10,5) = 252` such states; each selected divisor is a
product of exactly six distinct prime atoms, hence has Möbius sign `(-1)^6 = +1`.

The collapse theorem is stated for a *representation-blind* weight `Omega : R11Labels → R`,
i.e. a weight that does not depend on the selected five-subset: this is enforced by the type
of `Omega`, so no statement in which a selected-five label survives is formalized here.
-/
import Gate1B.R11.CanonicalSource

namespace Gate1B.R11

open Finset ArithmeticFunction

/-! ## 1. The selector set -/

/-- The CARD5 selector states: the five-element subsets of the ten large coordinates. -/
def card5Selectors : Finset (Finset (Fin 10)) := Finset.univ.powersetCard 5

theorem choose_ten_five : Nat.choose 10 5 = 252 := by decide

theorem card_card5Selectors : card5Selectors.card = 252 := by
  rw [card5Selectors, Finset.card_powersetCard, Finset.card_univ]
  rfl

theorem card5Selectors_card_eq {S : Finset (Fin 10)} (hS : S ∈ card5Selectors) : S.card = 5 :=
  (Finset.mem_powersetCard.mp hS).2

/-! ## 2. Each active state contributes Möbius sign `+1` -/

/-- The divisor selected by a CARD5 state: the distinguished atom together with the five
chosen large atoms. -/
def selectedDivisor (L : R11Labels) (S : Finset (Fin 10)) : ℕ :=
  L.p0 * ∏ i ∈ S, L.large i

/-- A CARD5 selected divisor is the product over a six-element set of distinct primes. -/
theorem selectedDivisor_eq_prod (L : R11Labels) (hd : L.LargeDistinct) (hf : L.P0Fresh)
    (S : Finset (Fin 10)) :
    selectedDivisor L S = ∏ p ∈ insert L.p0 (S.image L.large), p ∧
      (insert L.p0 (S.image L.large)).card = S.card + 1 := by
  have hnot : L.p0 ∉ S.image L.large := by
    simp only [Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact hf i hi.symm
  refine ⟨?_, ?_⟩
  · rw [selectedDivisor, Finset.prod_insert hnot, Finset.prod_image fun x _ y _ h => hd h]
  · rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hd]

/-- Every CARD5 selected divisor is squarefree with exactly six prime atoms. -/
theorem selectedDivisor_squarefree (L : R11Labels) (h : L.Admissible)
    {S : Finset (Fin 10)} (hS : S ∈ card5Selectors) :
    Squarefree (selectedDivisor L S) ∧ (selectedDivisor L S).primeFactors.card = 6 := by
  obtain ⟨hprod, hcard⟩ := selectedDivisor_eq_prod L h.2.2.1 h.2.2.2 S
  have hall : ∀ p ∈ insert L.p0 (S.image L.large), p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact h.1.1
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact h.1.2 i
  refine ⟨hprod ▸ squarefree_prod_primes _ hall, ?_⟩
  rw [hprod, Nat.primeFactors_prod hall, hcard, card5Selectors_card_eq hS]

/-- **The CARD5 Möbius sign is `+1`**: six distinct prime atoms, `(-1)^6 = 1`. -/
theorem moebius_selectedDivisor (L : R11Labels) (h : L.Admissible)
    {S : Finset (Fin 10)} (hS : S ∈ card5Selectors) :
    moebius (selectedDivisor L S) = 1 := by
  obtain ⟨hprod, hcard⟩ := selectedDivisor_eq_prod L h.2.2.1 h.2.2.2 S
  have hall : ∀ p ∈ insert L.p0 (S.image L.large), p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact h.1.1
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact h.1.2 i
  rw [hprod, moebius_prod_primes _ hall, hcard, card5Selectors_card_eq hS]
  decide

/-! ## 3. The CARD5 equal-`n` collapse -/

variable {R : Type*} [CommRing R]

/-- **CARD5 equal-`n` collapse.**  Summing a representation-blind weight (sign `+1` on every
active state) over the 252 CARD5 states multiplies it by exactly `252`.  `Omega` has type
`R11Labels → R`, so no selected-five label can survive on either side. -/
theorem card5_equal_n_collapse (Omega : R11Labels → R) (L : R11Labels) :
    ∑ _S ∈ card5Selectors, (1 : R) * Omega L = 252 * Omega L := by
  rw [Finset.sum_congr rfl fun _ _ => one_mul (Omega L), Finset.sum_const,
    card_card5Selectors, nsmul_eq_mul]
  norm_num

/-- The same collapse for a summand given a priori as a function of the state, under the
explicit representation-blindness hypothesis. -/
theorem card5_equal_n_collapse_of_blind (Omega : R11Labels → R) (L : R11Labels)
    (f : Finset (Fin 10) → R) (hblind : ∀ S ∈ card5Selectors, f S = Omega L) :
    ∑ S ∈ card5Selectors, f S = 252 * Omega L := by
  rw [Finset.sum_congr rfl hblind, Finset.sum_const, card_card5Selectors, nsmul_eq_mul]
  norm_num

/-- The outer CARD5 coefficient is `252`. -/
def card5Coefficient : ℕ := 252

theorem card5Coefficient_eq : card5Coefficient = Nat.choose 10 5 := by
  rw [card5Coefficient, choose_ten_five]

end Gate1B.R11
