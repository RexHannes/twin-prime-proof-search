/-
# Universal safe algebra — Kloosterman-like reindexing (no analytic input)

For a modulus `q` and an arbitrary phase function `F` on `ZMod q` with values in
any additive commutative monoid, put

    K_F(A,B) = ∑_{x ∈ (ZMod q)ˣ} F (A * x + B * x⁻¹).

This file proves the exact unit-substitution identity

    K_F(A,B) = K_F(A*u, B*u⁻¹)

and the product-slot form of it that moves a unit factor out of the second
argument into the first.

**FIREWALL.**  These are *reindexing identities*.  They prove **no** Weil,
Kuznetsov, Pascadi, Blomer–Pascadi or Yang bound, and a reindexing identity
preserves the exact size of the kernel, so it is not a contraction theorem.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

variable {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M]

/-- The Kloosterman-like kernel with an arbitrary phase function `F`. -/
def kLike (F : ZMod q → M) (A B : ZMod q) : M :=
  ∑ x : (ZMod q)ˣ, F (A * (x : ZMod q) + B * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- **Unit substitution.**  Replacing `x` by `u * x` in the defining sum gives
`K_F(A,B) = K_F(A*u, B*u⁻¹)`. -/
theorem kLike_scale (F : ZMod q → M) (A B : ZMod q) (u : (ZMod q)ˣ) :
    kLike F A B = kLike F (A * (u : ZMod q)) (B * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  unfold kLike
  refine (Fintype.sum_equiv (Equiv.mulLeft u) _ _ ?_).symm
  intro x
  have h1 : (((u * x : (ZMod q)ˣ)) : ZMod q) = (u : ZMod q) * (x : ZMod q) := by
    push_cast; ring
  have h2 : ((((u * x)⁻¹ : (ZMod q)ˣ)) : ZMod q)
      = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    rw [mul_inv]
    push_cast; ring
  simp only [Equiv.coe_mulLeft, h1, h2]
  congr 1
  ring

/-- **Product-slot reindexing.**  A unit factor `u` sitting in the second
argument can be moved into the first:

    K_F(k, c * u) = K_F(k * u, c).

With `u = h * B⁻¹` and `c = −2` this is the algebraic content of the passage
from `S(k, −2 h B⁻¹ ; q)` to `S(k h B⁻¹, −2 ; q)` on the unit sector. -/
theorem kLike_productSlot_reindex (F : ZMod q → M) (k c : ZMod q) (u : (ZMod q)ˣ) :
    kLike F k (c * (u : ZMod q)) = kLike F (k * (u : ZMod q)) c := by
  have h := kLike_scale F k (c * (u : ZMod q)) u
  have hc : c * (u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = c := by
    rw [mul_assoc]
    have : (u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, mul_one]
  rw [hc] at h
  exact h

end Universal.SafeAlgebra
