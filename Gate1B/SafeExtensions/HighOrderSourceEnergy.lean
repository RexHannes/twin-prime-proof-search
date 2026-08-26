/-
# Gate 1B v8.3 — H6 / H7 source-energy compiler

**Status: CONDITIONAL_FINITE / PROVED_ALGEBRAIC.**

The H6 source coefficient is the pushforward of a labelled tensor along the
product map,

    a₆(B) = ∑_{C₆ · x = B} Γ₆(C₆) f(x),

and the H7 source coefficient is the identity pushforward `a₇ = Γ₇`.

Everything is hypothesis-carrying: the multiplicity of the product map enters
only through the explicit fibre bound `hFiber`.  **No arithmetic multiplicity
is computed**, and no prime-norm or analytic estimate appears.
-/
import Mathlib
import Universal.SafeAlgebra.ProductEnergyFiniteFiber

namespace Gate1B.SafeExtensions

open Finset Universal.SafeAlgebra

variable {Cty Xty Bty : Type*} [Fintype Cty] [DecidableEq Cty] [Fintype Xty] [DecidableEq Xty]
  [Fintype Bty] [DecidableEq Bty]

/-- Exact energy of a two-factor labelled tensor. -/
theorem pair_tensor_energy (Gam : Cty → ℂ) (f : Xty → ℂ) :
    ∑ p : Cty × Xty, ‖Gam p.1 * f p.2‖ ^ 2
      = (∑ c : Cty, ‖Gam c‖ ^ 2) * (∑ x : Xty, ‖f x‖ ^ 2) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [norm_mul, mul_pow]

/-- The H6 source coefficient `a₆(B) = ∑_{C₆ x = B} Γ₆(C₆) f(x)`. -/
noncomputable def a6 (P : Cty × Xty → Bty) (Gam : Cty → ℂ) (f : Xty → ℂ) : Bty → ℂ :=
  pushforward P (fun p => Gam p.1 * f p.2)

/-- **H6 source-energy compiler.**  Under an explicit fibre bound `M` for the
product map, the energy of the H6 source coefficient is at most `M` times the
tensor energy `Energy(Γ₆) · Energy(f)`. -/
theorem h6Energy_of_fiberBound (P : Cty × Xty → Bty) (Gam : Cty → ℂ) (f : Xty → ℂ) (M : ℕ)
    (hFiber : ∀ b, (fiber P b).card ≤ M) :
    ∑ b : Bty, ‖a6 P Gam f b‖ ^ 2
      ≤ (M : ℝ) * ((∑ c : Cty, ‖Gam c‖ ^ 2) * (∑ x : Xty, ‖f x‖ ^ 2)) := by
  have h := l2_pushforward_le_fiber_card_mul P (fun p : Cty × Xty => Gam p.1 * f p.2) M hFiber
  rwa [pair_tensor_energy Gam f] at h

/-- The H7 source coefficient is the identity pushforward, `a₇ = Γ₇`. -/
theorem a7_eq (Gam : Bty → ℂ) (b : Bty) : pushforward id Gam b = Gam b := by
  classical
  unfold pushforward fiber
  rw [show (univ.filter fun a : Bty => id a = b) = {b} by
    ext a; simp [eq_comm]]
  simp

/-- **H7 source energy is exact** (fibres are singletons). -/
theorem h7Energy_exact (Gam : Bty → ℂ) :
    ∑ b : Bty, ‖pushforward id Gam b‖ ^ 2 = ∑ b : Bty, ‖Gam b‖ ^ 2 :=
  Finset.sum_congr rfl fun b _ => by rw [a7_eq Gam b]

end Gate1B.SafeExtensions
