/-
# Gate 1B v8.2 — twisted CRT factorisation of a finite Kloosterman sum

**Tier 2 (hypothesis-carrying).**  The CRT unit bijection and the twisted phase
decomposition are supplied as *explicit hypotheses* (`e`, `hphase`); this file
proves only that they force the exact multiplicative factorisation

    S_{ga}(A,B) = S_g(A₁,B₁) · S_a(A₂,B₂).

Nothing here constructs the twist, and nothing here bounds any factor: no Weil
bound, no cancellation claim.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteKloosterman

namespace Gate1B.SafeAlgebra

open Finset

namespace AdditiveCharacterSystem

variable {n g a : ℕ} [NeZero n] [NeZero g] [NeZero a]

/-- **Twisted CRT factorisation.**  Given a unit bijection `e` and a twisted
phase decomposition, the Kloosterman sum factorises exactly. -/
theorem kloosterman_mul_coprime_twisted
    (C : AdditiveCharacterSystem n) (Cg : AdditiveCharacterSystem g)
    (Ca : AdditiveCharacterSystem a)
    (A B : ZMod n) (A₁ B₁ : ZMod g) (A₂ B₂ : ZMod a)
    (e : (ZMod n)ˣ ≃ (ZMod g)ˣ × (ZMod a)ˣ)
    (hphase : ∀ u : (ZMod n)ˣ,
      C.chi (A * (u : ZMod n) + B * ((u⁻¹ : (ZMod n)ˣ) : ZMod n))
        = Cg.chi (A₁ * (((e u).1 : (ZMod g)ˣ) : ZMod g)
              + B₁ * ((((e u).1)⁻¹ : (ZMod g)ˣ) : ZMod g))
          * Ca.chi (A₂ * (((e u).2 : (ZMod a)ˣ) : ZMod a)
              + B₂ * ((((e u).2)⁻¹ : (ZMod a)ˣ) : ZMod a))) :
    C.kloosterman A B = Cg.kloosterman A₁ B₁ * Ca.kloosterman A₂ B₂ := by
  classical
  have hprod : ∑ p : (ZMod g)ˣ × (ZMod a)ˣ,
      Cg.chi (A₁ * ((p.1 : (ZMod g)ˣ) : ZMod g) + B₁ * (((p.1)⁻¹ : (ZMod g)ˣ) : ZMod g))
        * Ca.chi (A₂ * ((p.2 : (ZMod a)ˣ) : ZMod a) + B₂ * (((p.2)⁻¹ : (ZMod a)ˣ) : ZMod a))
      = Cg.kloosterman A₁ B₁ * Ca.kloosterman A₂ B₂ := by
    unfold kloosterman
    simp only [Fintype.sum_prod_type]
    rw [← Finset.sum_mul_sum]
  rw [← hprod, ← Equiv.sum_comp e]
  exact Finset.sum_congr rfl fun u _ => hphase u

/-- The QK5 shared-`g` specialisation: the same factorisation stated for a
modulus written as `g * a`. -/
theorem qk5_sharedG_twistedFactorization [NeZero (g * a)]
    (C : AdditiveCharacterSystem (g * a)) (Cg : AdditiveCharacterSystem g)
    (Ca : AdditiveCharacterSystem a)
    (A B : ZMod (g * a)) (A₁ B₁ : ZMod g) (A₂ B₂ : ZMod a)
    (e : (ZMod (g * a))ˣ ≃ (ZMod g)ˣ × (ZMod a)ˣ)
    (hphase : ∀ u : (ZMod (g * a))ˣ,
      C.chi (A * (u : ZMod (g * a)) + B * ((u⁻¹ : (ZMod (g * a))ˣ) : ZMod (g * a)))
        = Cg.chi (A₁ * (((e u).1 : (ZMod g)ˣ) : ZMod g)
              + B₁ * ((((e u).1)⁻¹ : (ZMod g)ˣ) : ZMod g))
          * Ca.chi (A₂ * (((e u).2 : (ZMod a)ˣ) : ZMod a)
              + B₂ * ((((e u).2)⁻¹ : (ZMod a)ˣ) : ZMod a))) :
    C.kloosterman A B = Cg.kloosterman A₁ B₁ * Ca.kloosterman A₂ B₂ :=
  kloosterman_mul_coprime_twisted C Cg Ca A B A₁ B₁ A₂ B₂ e hphase

end AdditiveCharacterSystem

end Gate1B.SafeAlgebra
