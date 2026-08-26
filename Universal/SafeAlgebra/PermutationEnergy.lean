/-
# Universal safe algebra — ℓ² energy under reindexing, and the square twist

Pure finite algebra.  No analytic input.

* `l2Energy` is the finite ℓ² energy of a family.
* `l2Energy_comp_equiv` — reindexing by any bijection preserves it.
* `squareMulEquiv a` — in a group, `r ↦ r · (a²)⁻¹` is a bijection; hence
  `squareTwist_l2Energy` — the square twist is an ℓ² isometry.
* `squareTwist_gram_bound` — the Gram entries of the twisted family are bounded
  by the common energy, so the twisted family is a bounded Gram family.

Nothing here claims any GCD/Kloosterman closure; it is the unitarity of the
square twist and nothing more.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

variable {ι : Type*} [Fintype ι] {E : Type*} [SeminormedAddCommGroup E]

/-- The finite ℓ² energy of a family. -/
def l2Energy (F : ι → E) : ℝ := ∑ i, ‖F i‖ ^ 2

theorem l2Energy_nonneg (F : ι → E) : 0 ≤ l2Energy F :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Reindexing by a bijection preserves the ℓ² energy.** -/
theorem l2Energy_comp_equiv (e : ι ≃ ι) (F : ι → E) : l2Energy (fun i => F (e i)) = l2Energy F :=
  Equiv.sum_comp e (fun i => ‖F i‖ ^ 2)

/-- The same statement for a bijection between two index types. -/
theorem l2Energy_comp_equiv' {κ : Type*} [Fintype κ] (e : κ ≃ ι) (F : ι → E) :
    l2Energy (fun k => F (e k)) = l2Energy F :=
  Equiv.sum_comp e (fun i => ‖F i‖ ^ 2)

section Group

variable {G : Type*} [Group G] [Fintype G]

/-- **The square twist is a bijection**: `r ↦ r · (a²)⁻¹`. -/
def squareMulEquiv (a : G) : G ≃ G := Equiv.mulRight (a ^ 2)⁻¹

omit [Fintype G] in
@[simp] theorem squareMulEquiv_apply (a r : G) : squareMulEquiv a r = r * (a ^ 2)⁻¹ := rfl

/-- The square-twisted family `P_a F (r) = F(r a^{-2})`. -/
def squareTwist (F : G → E) (a : G) : G → E := fun r => F (r * (a ^ 2)⁻¹)

omit [Fintype G] in
@[simp] theorem squareTwist_norm_eq (F : G → E) (a r : G) :
    ‖squareTwist F a r‖ = ‖F (r * (a ^ 2)⁻¹)‖ := rfl

/-- **Square-twist unitarity**: the twist preserves the ℓ² energy exactly. -/
theorem squareTwist_l2Energy (F : G → E) (a : G) : l2Energy (squareTwist F a) = l2Energy F :=
  l2Energy_comp_equiv (squareMulEquiv a) F

end Group

/-! ## Gram bound for a twisted family -/

section Gram

variable {G : Type*} [Group G] [Fintype G]

/-- The Gram entry of two complex families. -/
noncomputable def gramEntry (u v : G → ℂ) : ℂ := ∑ r, u r * (starRingEnd ℂ) (v r)

omit [Group G] in
/-- Every Gram entry is bounded by the average of the two energies. -/
theorem gramEntry_norm_le (u v : G → ℂ) :
    ‖gramEntry u v‖ ≤ (l2Energy u + l2Energy v) / 2 := by
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ r : G, ‖u r * (starRingEnd ℂ) (v r)‖ ≤ (‖u r‖ ^ 2 + ‖v r‖ ^ 2) / 2 := by
    intro r
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖u r‖ - ‖v r‖), norm_nonneg (u r), norm_nonneg (v r)]
  calc ∑ r, ‖u r * (starRingEnd ℂ) (v r)‖
      ≤ ∑ r, (‖u r‖ ^ 2 + ‖v r‖ ^ 2) / 2 := Finset.sum_le_sum fun r _ => hterm r
    _ = (l2Energy u + l2Energy v) / 2 := by
        simp [l2Energy, Finset.sum_add_distrib, Finset.sum_div, add_div]

/-- **The square-twisted family is a bounded Gram family**: every Gram entry is
bounded by the single common energy of the untwisted vector. -/
theorem squareTwist_gram_bound (K : G → ℂ) (a b : G) :
    ‖gramEntry (squareTwist K a) (squareTwist K b)‖ ≤ l2Energy K := by
  have h := gramEntry_norm_le (squareTwist K a) (squareTwist K b)
  rw [squareTwist_l2Energy, squareTwist_l2Energy] at h
  linarith

/-- The diagonal of the twisted Gram family is constant. -/
theorem squareTwist_gram_diagonal (K : G → ℂ) (a : G) :
    l2Energy (squareTwist K a) = l2Energy K := squareTwist_l2Energy K a

end Gram

end Universal.SafeAlgebra
