/-
# Gate 1B v8.2 — D₁₂ pushforward factorisation

If, along a CRT bijection `e : Γ ≃ Γ₁ × Γ₂`, the residue amplitude factors as

    A g = R₁ (e g).1 * conj (R₂ (e g).2),

then both the ℓ¹ mass and the ℓ² energy of `A` factor exactly.

The CRT bijection is supplied as an explicit `Equiv` hypothesis — nothing here
constructs it, and nothing here is analytic.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

variable {Γ Γ₁ Γ₂ : Type*} [Fintype Γ] [Fintype Γ₁] [Fintype Γ₂]

/-- **ℓ¹ factorisation of the D₁₂ pushforward.** -/
theorem d12Pushforward_l1_factor (e : Γ ≃ Γ₁ × Γ₂) (R₁ : Γ₁ → ℂ) (R₂ : Γ₂ → ℂ)
    (A : Γ → ℂ) (hA : ∀ g, A g = R₁ (e g).1 * (starRingEnd ℂ) (R₂ (e g).2)) :
    ∑ g, ‖A g‖ = (∑ x, ‖R₁ x‖) * ∑ y, ‖R₂ y‖ := by
  classical
  have h1 : ∑ g, ‖A g‖ = ∑ p : Γ₁ × Γ₂, ‖R₁ p.1 * (starRingEnd ℂ) (R₂ p.2)‖ := by
    rw [← Equiv.sum_comp e (fun p : Γ₁ × Γ₂ => ‖R₁ p.1 * (starRingEnd ℂ) (R₂ p.2)‖)]
    exact Finset.sum_congr rfl fun g _ => by rw [hA g]
  rw [h1, Fintype.sum_prod_type]
  simp only [norm_mul, RCLike.norm_conj, ← Finset.mul_sum, ← Finset.sum_mul]

/-- **ℓ² factorisation of the D₁₂ pushforward.** -/
theorem d12Pushforward_l2_factor (e : Γ ≃ Γ₁ × Γ₂) (R₁ : Γ₁ → ℂ) (R₂ : Γ₂ → ℂ)
    (A : Γ → ℂ) (hA : ∀ g, A g = R₁ (e g).1 * (starRingEnd ℂ) (R₂ (e g).2)) :
    ∑ g, ‖A g‖ ^ 2 = (∑ x, ‖R₁ x‖ ^ 2) * ∑ y, ‖R₂ y‖ ^ 2 := by
  classical
  have h1 : ∑ g, ‖A g‖ ^ 2 = ∑ p : Γ₁ × Γ₂, ‖R₁ p.1 * (starRingEnd ℂ) (R₂ p.2)‖ ^ 2 := by
    rw [← Equiv.sum_comp e (fun p : Γ₁ × Γ₂ => ‖R₁ p.1 * (starRingEnd ℂ) (R₂ p.2)‖ ^ 2)]
    exact Finset.sum_congr rfl fun g _ => by rw [hA g]
  rw [h1, Fintype.sum_prod_type]
  simp only [norm_mul, RCLike.norm_conj, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

end Gate1B.SafeAlgebra
