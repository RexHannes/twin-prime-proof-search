/-
# Gate 1B v8.2 — full-nine ANOVA algebra and critical-five product geometry

**FIREWALL.**  Everything in this file is an *algebraic identity* about nine
formal coordinates.  Nothing here asserts that the physical Gate source is
given by nine such coordinates: the

    PHYSICAL NINE-COORDINATE SOURCE BRIDGE

is **OPEN / SOURCE_UNVERIFIED**, and no theorem below is named as if the source
dictionary were proved.

Contents.

* `fullNine_anova` — the `Fin 9` specialisation of the generic expansion
  `Universal.SafeAlgebra.finset_prod_add_eq_sum_powerset`.
* `fullNine_five_complement_four` — a defect set of size `5` has model
  complement of size `4`.
* `fullNine_defectOrder_card_table` — the full `|J| = j ⟹ |Jᶜ| = 9 - j` table.
* `criticalFive_product_split` — `C_J * a_J = ∏ all nine`.
* `criticalFive_shell_rewrite` — the integer shell relation
  `∏ all − q·ℓ = −2` transported to `C_J * a_J − q·ℓ = −2`.
-/
import Universal.SafeAlgebra.FinsetANOVA

namespace Gate1B.SafeExtensions

open Finset

variable {R : Type*} [CommSemiring R]

/-- **Full-nine ANOVA.**  For `ν i = f i + δ i` on nine coordinates,
`∏ ν = ∑_{J ⊆ Fin 9} δ_J · f_{Jᶜ}`. -/
theorem fullNine_anova (f δ : Fin 9 → R) :
    ∏ i : Fin 9, (f i + δ i)
      = ∑ J ∈ (Finset.univ : Finset (Fin 9)).powerset,
          (∏ j ∈ J, δ j) * ∏ i ∈ Finset.univ \ J, f i :=
  Universal.SafeAlgebra.finset_prod_add_eq_sum_powerset _ f δ

/-- A single ANOVA term: defect product over `J` times model product over the
complement of `J`. -/
def fullNine_term (f δ : Fin 9 → R) (J : Finset (Fin 9)) : R :=
  (∏ j ∈ J, δ j) * ∏ i ∈ Jᶜ, f i

/-- The defect order of a term is the cardinality of its defect set. -/
def fullNine_defectOrder (J : Finset (Fin 9)) : ℕ := J.card

/-- Inside `Fin 9`, the set difference from `univ` is the complement. -/
theorem fullNine_univ_sdiff (J : Finset (Fin 9)) : Finset.univ \ J = Jᶜ := by
  simp [Finset.compl_eq_univ_sdiff]

/-- The ANOVA expansion written with `fullNine_term`. -/
theorem fullNine_anova_term (f δ : Fin 9 → R) :
    ∏ i : Fin 9, (f i + δ i)
      = ∑ J ∈ (Finset.univ : Finset (Fin 9)).powerset, fullNine_term f δ J := by
  rw [fullNine_anova f δ]
  exact Finset.sum_congr rfl fun J _ => by rw [fullNine_term, fullNine_univ_sdiff]

/-- **Critical five.**  A defect set of size five has a model complement of
size four. -/
theorem fullNine_five_complement_four {J : Finset (Fin 9)} (h : J.card = 5) :
    Jᶜ.card = 4 := by
  have := Finset.card_compl J
  simp [h] at this
  omega

/-- The complete defect-order/model-order table on nine coordinates. -/
theorem fullNine_defectOrder_card_table (J : Finset (Fin 9)) :
    Jᶜ.card = 9 - J.card := by
  have := Finset.card_compl J
  simpa using this

/-- The critical-five defect product. -/
def criticalFive_C (nu : Fin 9 → R) (J : Finset (Fin 9)) : R := ∏ j ∈ J, nu j

/-- The complementary model product. -/
def criticalFive_a (nu : Fin 9 → R) (J : Finset (Fin 9)) : R := ∏ i ∈ Jᶜ, nu i

/-- **Critical-five product split.**  For every subset `J` (in particular
`#J = 5`), the defect product times the model product is the full nine-fold
product. -/
theorem criticalFive_product_split (nu : Fin 9 → R) (J : Finset (Fin 9)) :
    criticalFive_C nu J * criticalFive_a nu J = ∏ i : Fin 9, nu i := by
  rw [criticalFive_C, criticalFive_a]
  exact Finset.prod_mul_prod_compl J nu

/-- **Critical-five shell rewrite.**  The integer shell relation for the full
product transports verbatim to the split form.  This is source *geometry*: it
asserts nothing about well-factorability of the five defect factors, and no
analytic estimate follows. -/
theorem criticalFive_shell_rewrite (nu : Fin 9 → ℤ) (J : Finset (Fin 9)) (q ell : ℤ)
    (h : (∏ i : Fin 9, nu i) - q * ell = -2) :
    criticalFive_C nu J * criticalFive_a nu J - q * ell = -2 := by
  rw [criticalFive_product_split nu J]; exact h

end Gate1B.SafeExtensions
