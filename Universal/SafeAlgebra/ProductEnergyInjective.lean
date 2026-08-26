/-
# Universal safe algebra — ℓ² energy of a labelled product coefficient

Pure finite algebra.

* `l2Energy_pi_product` — the ℓ² energy of the product coefficient
  `x ↦ ∏ i, f i (x i)` on a finite labelled product is exactly the product of
  the coordinate energies.
* `l2Energy_product_of_injective` — if the labelled product is pushed forward by
  an **injective** product map, the pushed-forward energy is unchanged, so it is
  still the product of the coordinate energies.

No box norm is asserted: the coordinate energies are inputs.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]

/-- **Product energy on a labelled finite product.** -/
theorem l2Energy_pi_product (f : ∀ i, A i → ℂ) :
    ∑ x : (∀ i, A i), ‖∏ i, f i (x i)‖ ^ 2 = ∏ i, ∑ a : A i, ‖f i a‖ ^ 2 := by
  classical
  have hnorm : ∀ x : (∀ i, A i), ‖∏ i, f i (x i)‖ ^ 2 = ∏ i, ‖f i (x i)‖ ^ 2 := by
    intro x
    rw [norm_prod, ← Finset.prod_pow]
  calc ∑ x : (∀ i, A i), ‖∏ i, f i (x i)‖ ^ 2
      = ∑ x : (∀ i, A i), ∏ i, ‖f i (x i)‖ ^ 2 := by
        exact Finset.sum_congr rfl fun x _ => hnorm x
    _ = ∏ i, ∑ a : A i, ‖f i a‖ ^ 2 := by
        rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ]

/-- **Injective pushforward keeps the product energy.**  If `P` is injective and
`g` agrees with the product coefficient along `P`, the energy of `g` over the
image is the product of the coordinate energies. -/
theorem l2Energy_product_of_injective {B : Type*} [DecidableEq B]
    (P : (∀ i, A i) → B) (hP : Function.Injective P) (f : ∀ i, A i → ℂ) (g : B → ℂ)
    (hg : ∀ x, g (P x) = ∏ i, f i (x i)) :
    ∑ b ∈ (Finset.univ : Finset (∀ i, A i)).image P, ‖g b‖ ^ 2
      = ∏ i, ∑ a : A i, ‖f i a‖ ^ 2 := by
  classical
  rw [Finset.sum_image (fun x _ y _ h => hP h)]
  rw [← l2Energy_pi_product f]
  exact Finset.sum_congr rfl fun x _ => by rw [hg x]

/-- Failure of injectivity is a genuine hypothesis: a two-to-one product map can
collapse the energy. -/
theorem l2Energy_product_needs_injective :
    ∃ (P : (Fin 2 → Fin 2) → Fin 1) (f : Fin 2 → Fin 2 → ℂ) (g : Fin 1 → ℂ),
      (∀ x, g (P x) = ∏ i, f i (x i)) ∧
        ∑ b ∈ (Finset.univ : Finset (Fin 2 → Fin 2)).image P, ‖g b‖ ^ 2
          ≠ ∏ i, ∑ a : Fin 2, ‖f i a‖ ^ 2 := by
  classical
  refine ⟨fun _ => 0, fun _ _ => 1, fun _ => 1, fun x => by simp, ?_⟩
  rw [Finset.image_const Finset.univ_nonempty]
  norm_num

end Universal.SafeAlgebra
