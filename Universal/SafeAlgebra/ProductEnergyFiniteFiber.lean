/-
# Universal safe algebra v8.3 — pushforward energy with finite fibres

**Status: PROVED_ALGEBRAIC (finite).**

`ProductEnergyInjective` gives the exact product-energy factorisation when the
labelling map is injective.  Here injectivity is replaced by a *fibre bound*:
if every fibre of `f : A → B` has at most `M` elements, then the ℓ² energy of
the pushforward coefficient is at most `M` times the source energy.

The fibre bound `hFiber` is an explicit hypothesis — no arithmetic multiplicity
(no `7!`, no `8!`) is computed or claimed here.
-/
import Mathlib
import Universal.SafeAlgebra.ProductEnergyInjective

namespace Universal.SafeAlgebra

open Finset

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The fibre of `f` over `b`. -/
def fiber (f : A → B) (b : B) : Finset A := univ.filter (fun a => f a = b)

/-- The pushforward coefficient `F b = ∑_{f a = b} c a`. -/
noncomputable def pushforward (f : A → B) (c : A → ℂ) (b : B) : ℂ :=
  ∑ a ∈ fiber f b, c a

omit [DecidableEq A] in
theorem sum_fiber_sum (f : A → B) (g : A → ℝ) :
    ∑ b : B, ∑ a ∈ fiber f b, g a = ∑ a : A, g a := by
  classical
  simpa [fiber] using
    (Finset.sum_fiberwise (s := (univ : Finset A)) (g := f) (f := g))

omit [DecidableEq A] in
/-- **Fibre-bounded pushforward energy.** -/
theorem l2_pushforward_le_fiber_card_mul (f : A → B) (c : A → ℂ) (M : ℕ)
    (hFiber : ∀ b, (fiber f b).card ≤ M) :
    ∑ b : B, ‖pushforward f c b‖ ^ 2 ≤ (M : ℝ) * ∑ a : A, ‖c a‖ ^ 2 := by
  classical
  have key : ∀ b : B, ‖pushforward f c b‖ ^ 2 ≤ (M : ℝ) * ∑ a ∈ fiber f b, ‖c a‖ ^ 2 := by
    intro b
    have h1 : ‖pushforward f c b‖ ≤ ∑ a ∈ fiber f b, ‖c a‖ := by
      unfold pushforward
      exact norm_sum_le _ _
    have h2 : ‖pushforward f c b‖ ^ 2 ≤ (∑ a ∈ fiber f b, ‖c a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (∑ a ∈ fiber f b, ‖c a‖) ^ 2
        ≤ ((fiber f b).card : ℝ) * ∑ a ∈ fiber f b, ‖c a‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h4 : ((fiber f b).card : ℝ) * ∑ a ∈ fiber f b, ‖c a‖ ^ 2
        ≤ (M : ℝ) * ∑ a ∈ fiber f b, ‖c a‖ ^ 2 := by
      have hM : ((fiber f b).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hFiber b
      have hnn : (0 : ℝ) ≤ ∑ a ∈ fiber f b, ‖c a‖ ^ 2 :=
        Finset.sum_nonneg fun a _ => by positivity
      exact mul_le_mul_of_nonneg_right hM hnn
    linarith
  calc ∑ b : B, ‖pushforward f c b‖ ^ 2
      ≤ ∑ b : B, (M : ℝ) * ∑ a ∈ fiber f b, ‖c a‖ ^ 2 :=
        Finset.sum_le_sum fun b _ => key b
    _ = (M : ℝ) * ∑ b : B, ∑ a ∈ fiber f b, ‖c a‖ ^ 2 := by rw [Finset.mul_sum]
    _ = (M : ℝ) * ∑ a : A, ‖c a‖ ^ 2 := by rw [sum_fiber_sum]

omit [DecidableEq A] in
/-- **Uniform-fibre version.** -/
theorem l2_pushforward_le_uniform_fiber (f : A → B) (c : A → ℂ) (M : ℕ)
    (hFiber : ∀ b, (fiber f b).card = M) :
    ∑ b : B, ‖pushforward f c b‖ ^ 2 ≤ (M : ℝ) * ∑ a : A, ‖c a‖ ^ 2 :=
  l2_pushforward_le_fiber_card_mul f c M fun b => (hFiber b).le

/-- **Product-source corollary.**  For a labelled product source with coefficient
`x ↦ ∏ i, g i (x i)` pushed forward along a map with fibres of size at most `M`,
the pushed-forward energy is at most `M` times the product of the coordinate
energies. -/
theorem l2_pushforward_product_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (P : (∀ i, A i) → B) (g : ∀ i, A i → ℂ) (M : ℕ)
    (hFiber : ∀ b, (fiber P b).card ≤ M) :
    ∑ b : B, ‖pushforward P (fun x => ∏ i, g i (x i)) b‖ ^ 2
      ≤ (M : ℝ) * ∏ i, ∑ a : A i, ‖g i a‖ ^ 2 := by
  classical
  have h := l2_pushforward_le_fiber_card_mul P (fun x => ∏ i, g i (x i)) M hFiber
  rwa [l2Energy_pi_product g] at h

end Universal.SafeAlgebra
