/-
# Gate 1B v8.2 — seven-box product energy

A direct specialisation of `Universal.SafeAlgebra.l2Energy_pi_product` to a
labelled product of seven boxes: the ℓ² energy of a product coefficient is
exactly the product of the seven box energies.

**No box count and no box density is asserted.**  In particular nothing here
says anything of the shape `N_G ≍ Y⁷ / (log Y)⁷`; the box energies are inputs.
-/
import Mathlib
import Universal.SafeAlgebra.ProductEnergyInjective

namespace Gate1B.SafeAlgebra

open Finset

variable {A : Fin 7 → Type*} [∀ i, Fintype (A i)]

/-- **Seven-box factorisation of the ℓ² energy.** -/
theorem sevenBoxEnergy_factor (f : ∀ i, A i → ℂ) :
    ∑ x : (∀ i, A i), ‖∏ i, f i (x i)‖ ^ 2 = ∏ i, ∑ a : A i, ‖f i a‖ ^ 2 :=
  Universal.SafeAlgebra.l2Energy_pi_product f

/-- Seven-box energy under an injective product labelling. -/
theorem sevenBoxEnergy_of_injective {B : Type*} [DecidableEq B]
    (P : (∀ i, A i) → B) (hP : Function.Injective P) (f : ∀ i, A i → ℂ) (g : B → ℂ)
    (hg : ∀ x, g (P x) = ∏ i, f i (x i)) :
    ∑ b ∈ (Finset.univ : Finset (∀ i, A i)).image P, ‖g b‖ ^ 2
      = ∏ i, ∑ a : A i, ‖f i a‖ ^ 2 :=
  Universal.SafeAlgebra.l2Energy_product_of_injective P hP f g hg

end Gate1B.SafeAlgebra
