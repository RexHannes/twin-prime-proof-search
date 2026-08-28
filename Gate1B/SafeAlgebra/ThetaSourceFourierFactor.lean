/-
# Gate 1B v12 — CRT source Fourier factorisation (CONDITIONAL, exact hypotheses)

**Status: PROVED_ALGEBRAIC, CONDITIONAL on explicit CRT scaling hypotheses.**

The repository does not (yet) contain the literal CRT residue pushforward for
the Θ-source in the form needed here, so the factorisation is stated as a
*hypothesis-carrying* theorem: the CRT bijection `e`, the frequency scalings
`lam1, lam2` and the additive phase splitting are all explicit theorem
hypotheses.  Nothing about the actual source is asserted, and no analytic gain
is claimed: the statement is an identity between two finite sums.

    Â(ξ) = F₁(λ₁ ξ) · conj (F₂(λ₂ ξ)).

Contents:

* `crt_source_fourier_factor` — the conditional factorisation;
* `crt_source_fourier_factor_modulus` — the modulus form.
-/
import Mathlib
import Gate1B.SafeAlgebra.KloostermanMultiplierFourier

namespace Gate1B.SafeAlgebra

open Finset

/-- **Conditional CRT source Fourier factorisation.**

Hypotheses (all explicit, none assumed globally):

* `e` is the CRT bijection `ZMod c ≃ ZMod q₁ × ZMod q₂`;
* `hA` says the source is the rank-one CRT pushforward `R₁ ⊗ conj R₂`;
* `hphase` is the exact CRT phase splitting with frequency scalings
  `lam1, lam2`.

Conclusion: the additive transform factorises. -/
theorem crt_source_fourier_factor
    {c q1 q2 : ℕ} [NeZero c] [NeZero q1] [NeZero q2]
    (C : AdditiveCharacterSystem c) (C1 : AdditiveCharacterSystem q1)
    (C2 : AdditiveCharacterSystem q2)
    (e : ZMod c ≃ ZMod q1 × ZMod q2)
    (lam1 : ZMod c → ZMod q1) (lam2 : ZMod c → ZMod q2)
    (R1 : ZMod q1 → ℂ) (R2 : ZMod q2 → ℂ) (A : ZMod c → ℂ)
    (hA : ∀ theta : ZMod c, A theta = R1 (e theta).1 * (starRingEnd ℂ) (R2 (e theta).2))
    (hphase : ∀ xi theta : ZMod c,
      C.chi (-(xi * theta))
        = C1.chi (-(lam1 xi * (e theta).1))
            * (starRingEnd ℂ) (C2.chi (-(lam2 xi * (e theta).2))))
    (xi : ZMod c) :
    C.addHat A xi
      = C1.addHat R1 (lam1 xi) * (starRingEnd ℂ) (C2.addHat R2 (lam2 xi)) := by
  classical
  unfold AdditiveCharacterSystem.addHat
  have hterm : ∀ theta : ZMod c, A theta * C.chi (-(xi * theta))
      = (R1 (e theta).1 * C1.chi (-(lam1 xi * (e theta).1)))
        * (starRingEnd ℂ) (R2 (e theta).2 * C2.chi (-(lam2 xi * (e theta).2))) := by
    intro theta
    rw [hA theta, hphase xi theta, map_mul]
    ring
  rw [Finset.sum_congr rfl fun theta _ => hterm theta]
  rw [← Equiv.sum_comp e.symm (fun theta : ZMod c =>
    (R1 (e theta).1 * C1.chi (-(lam1 xi * (e theta).1)))
      * (starRingEnd ℂ) (R2 (e theta).2 * C2.chi (-(lam2 xi * (e theta).2))))]
  have hsimp : ∀ p : ZMod q1 × ZMod q2,
      (R1 (e (e.symm p)).1 * C1.chi (-(lam1 xi * (e (e.symm p)).1)))
        * (starRingEnd ℂ) (R2 (e (e.symm p)).2 * C2.chi (-(lam2 xi * (e (e.symm p)).2)))
      = (R1 p.1 * C1.chi (-(lam1 xi * p.1)))
        * (starRingEnd ℂ) (R2 p.2 * C2.chi (-(lam2 xi * p.2))) := by
    intro p
    rw [Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl fun p _ => hsimp p]
  rw [Fintype.sum_prod_type]
  rw [map_sum, Finset.sum_mul_sum]

/-- Modulus form of the conditional CRT factorisation. -/
theorem crt_source_fourier_factor_modulus
    {c q1 q2 : ℕ} [NeZero c] [NeZero q1] [NeZero q2]
    (C : AdditiveCharacterSystem c) (C1 : AdditiveCharacterSystem q1)
    (C2 : AdditiveCharacterSystem q2)
    (e : ZMod c ≃ ZMod q1 × ZMod q2)
    (lam1 : ZMod c → ZMod q1) (lam2 : ZMod c → ZMod q2)
    (R1 : ZMod q1 → ℂ) (R2 : ZMod q2 → ℂ) (A : ZMod c → ℂ)
    (hA : ∀ theta : ZMod c, A theta = R1 (e theta).1 * (starRingEnd ℂ) (R2 (e theta).2))
    (hphase : ∀ xi theta : ZMod c,
      C.chi (-(xi * theta))
        = C1.chi (-(lam1 xi * (e theta).1))
            * (starRingEnd ℂ) (C2.chi (-(lam2 xi * (e theta).2))))
    (xi : ZMod c) :
    ‖C.addHat A xi‖ = ‖C1.addHat R1 (lam1 xi)‖ * ‖C2.addHat R2 (lam2 xi)‖ := by
  rw [crt_source_fourier_factor C C1 C2 e lam1 lam2 R1 R2 A hA hphase xi]
  rw [norm_mul, RCLike.norm_conj]

end Gate1B.SafeAlgebra
