/-
# Gate 1B v8.3 — reciprocal additive phase, multiplicative character expansion

**Status: PROVED_ALGEBRAIC (Tier 2: both character systems are supplied).**

Working with a supplied additive character system `C` modulo `q` and a supplied
multiplicative character system `S` on `(ZMod q)ˣ`, we expand the reciprocal
additive phase

    e_q(a · B⁻¹)

into multiplicative characters.  All conjugations are **derived** from
`MulCharSystem.chi_inv` and the Gauss-coefficient twist identity, never
hard-coded from prose.

* `gaussCoeff C S c a = ∑_{v unit} e_q(a v) conj χ_c(v)`;
* `tauCoeff C S c = gaussCoeff C S c 1`;
* `gauss_twist`: `gaussCoeff C S c α = χ_c(α) τ(χ_c)` for a unit `α`;
* `reciprocal_addChar_fourier`: the exact finite expansion;
* `reciprocal_phase_character_expand`: unit-argument form;
* `reciprocal_phase_expand_shift_two`: the fixed-shift specialisation
  `a = -2h` (the shift is fixed, never averaged).

No Pólya–Vinogradov, no large sieve, no bound of any kind is claimed.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteMultiplicativeCharacters
import Gate1B.SafeAlgebra.FiniteKloosterman

namespace Gate1B.SafeAlgebra

open Finset

variable {q : ℕ} [NeZero q] {Ch : Type*} [Fintype Ch] [DecidableEq Ch]

/-- The Gauss coefficient `∑_{v unit} e_q(a v) conj χ_c(v)`. -/
noncomputable def gaussCoeff (C : AdditiveCharacterSystem q) (S : MulCharSystem (ZMod q)ˣ Ch)
    (c : Ch) (a : ZMod q) : ℂ :=
  ∑ v : (ZMod q)ˣ, C.chi (a * (v : ZMod q)) * (starRingEnd ℂ) (S.chi c v)

/-- The Gauss sum `τ(χ_c) = gaussCoeff C S c 1`. -/
noncomputable def tauCoeff (C : AdditiveCharacterSystem q) (S : MulCharSystem (ZMod q)ˣ Ch)
    (c : Ch) : ℂ := gaussCoeff C S c 1

/-- **Gauss twist (derived).**  For a unit `α`, `gaussCoeff C S c α = χ_c(α) τ(χ_c)`. -/
theorem gauss_twist (C : AdditiveCharacterSystem q) (S : MulCharSystem (ZMod q)ˣ Ch)
    (c : Ch) (a : (ZMod q)ˣ) :
    gaussCoeff C S c (a : ZMod q) = S.chi c a * tauCoeff C S c := by
  classical
  unfold gaussCoeff tauCoeff
  rw [← Equiv.sum_comp (Equiv.mulLeft a⁻¹)]
  have key : ∀ v : (ZMod q)ˣ,
      C.chi ((a : ZMod q) * ((Equiv.mulLeft a⁻¹ v : (ZMod q)ˣ) : ZMod q)) *
        (starRingEnd ℂ) (S.chi c (Equiv.mulLeft a⁻¹ v))
      = S.chi c a * (C.chi ((1 : ZMod q) * (v : ZMod q)) * (starRingEnd ℂ) (S.chi c v)) := by
    intro v
    have hcoe : ((a⁻¹ * v : (ZMod q)ˣ) : ZMod q) = (a⁻¹ : (ZMod q)ˣ) * (v : ZMod q) := by
      push_cast; ring
    have h1 : (a : ZMod q) * ((a⁻¹ * v : (ZMod q)ˣ) : ZMod q) = (v : ZMod q) := by
      rw [hcoe, ← mul_assoc]
      norm_cast
      simp
    have h2 : S.chi c (a⁻¹ * v) = (starRingEnd ℂ) (S.chi c a) * S.chi c v := by
      rw [S.map_mul, S.chi_inv]
    simp only [Equiv.coe_mulLeft, h1, h2, one_mul, map_mul]
    have h3 : (starRingEnd ℂ) ((starRingEnd ℂ) (S.chi c a)) = S.chi c a := by simp
    rw [h3]; ring
  simp_rw [key]
  rw [← Finset.mul_sum]
  rfl

/-- **Reciprocal additive phase expansion.**  Exact finite Fourier expansion of
`e_q(a B⁻¹)` over the supplied character family. -/
theorem reciprocal_addChar_fourier (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (a : ZMod q) (B : (ZMod q)ˣ) :
    C.chi (a * ((B⁻¹ : (ZMod q)ˣ) : ZMod q))
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          ∑ c : Ch, gaussCoeff C S c a * S.chi c B⁻¹ := by
  classical
  have h := S.character_fourier_inversion' (fun u : (ZMod q)ˣ => C.chi (a * (u : ZMod q))) B⁻¹
  simpa [MulCharSystem.hat, gaussCoeff] using h

/-- **Unit-argument form**, with the conjugations derived: for units `α, B`,
`e_q(α B⁻¹) = φ(q)⁻¹ ∑_χ τ(χ) χ(α) conj χ(B)`. -/
theorem reciprocal_phase_character_expand (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (a B : (ZMod q)ˣ) :
    C.chi ((a : ZMod q) * ((B⁻¹ : (ZMod q)ˣ) : ZMod q))
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          ∑ c : Ch, tauCoeff C S c * S.chi c a * (starRingEnd ℂ) (S.chi c B) := by
  classical
  rw [reciprocal_addChar_fourier C S (a : ZMod q) B]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [gauss_twist C S c a, S.chi_inv]
  ring

/-- **Fixed-shift specialisation** `a = -2h`.  The shift `2` is fixed: nothing is
averaged over the shift. -/
theorem reciprocal_phase_expand_shift_two (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (h : ZMod q) (B : (ZMod q)ˣ) :
    C.chi ((-2 * h) * ((B⁻¹ : (ZMod q)ˣ) : ZMod q))
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          ∑ c : Ch, gaussCoeff C S c (-2 * h) * (starRingEnd ℂ) (S.chi c B) := by
  classical
  rw [reciprocal_addChar_fourier C S (-2 * h) B]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [S.chi_inv]

end Gate1B.SafeAlgebra
