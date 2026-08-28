/-
# Gate 1B v12 — multiplicative source-character factorisation and Parseval

**Status: PROVED_ALGEBRAIC, CONDITIONAL on explicit CRT unit-bijection and
phase hypotheses.**

For a rank-one source pushforward

    A(g) = R₁(u₁ g) · conj (R₂(u₂ g))

and a CRT unit bijection `G ≃ G₁ × G₂` with an exact unit phase `w` in the
character splitting, the multiplicative-character transform factorises:

    Â(c) = conj (w c) · R̂₁(c₁) · conj (R̂₂(c₂)).

We also record Parseval in the `(ZMod q)ˣ` normalisation:

    ∑_χ |R̂(χ)|² = φ(q) · residueEnergy(R).

No covariance is estimated anywhere; every statement is a finite identity.

Contents:

* `rankOne_source_character_factor`;
* `rankOne_source_character_factor_modulus`;
* `character_parseval_totient`.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteMultiplicativeCharacters

namespace Gate1B.SafeAlgebra

open Finset

namespace MulCharSystem

/-- **Conditional rank-one source-character factorisation.** -/
theorem rankOne_source_character_factor
    {G G1 G2 : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
    [Fintype G1] [DecidableEq G1] [CommGroup G1] [Fintype G2] [DecidableEq G2] [CommGroup G2]
    {Ch Ch1 Ch2 : Type*} [Fintype Ch] [DecidableEq Ch] [Fintype Ch1] [DecidableEq Ch1]
    [Fintype Ch2] [DecidableEq Ch2]
    (S : MulCharSystem G Ch) (S1 : MulCharSystem G1 Ch1) (S2 : MulCharSystem G2 Ch2)
    (e : G ≃ G1 × G2) (idx : Ch → Ch1 × Ch2) (w : Ch → ℂ)
    (R1 : G1 → ℂ) (R2 : G2 → ℂ) (A : G → ℂ)
    (hA : ∀ g : G, A g = R1 (e g).1 * (starRingEnd ℂ) (R2 (e g).2))
    (hchi : ∀ (ch : Ch) (g : G), S.chi ch g
      = w ch * S1.chi (idx ch).1 (e g).1 * (starRingEnd ℂ) (S2.chi (idx ch).2 (e g).2))
    (ch : Ch) :
    S.hat A ch
      = (starRingEnd ℂ) (w ch) * S1.hat R1 (idx ch).1
          * (starRingEnd ℂ) (S2.hat R2 (idx ch).2) := by
  classical
  unfold hat
  have hterm : ∀ g : G, A g * (starRingEnd ℂ) (S.chi ch g)
      = (starRingEnd ℂ) (w ch)
        * ((R1 (e g).1 * (starRingEnd ℂ) (S1.chi (idx ch).1 (e g).1))
            * (starRingEnd ℂ) (R2 (e g).2 * (starRingEnd ℂ) (S2.chi (idx ch).2 (e g).2))) := by
    intro g
    have e1 : (starRingEnd ℂ) (w ch * S1.chi (idx ch).1 (e g).1
          * (starRingEnd ℂ) (S2.chi (idx ch).2 (e g).2))
        = (starRingEnd ℂ) (w ch) * (starRingEnd ℂ) (S1.chi (idx ch).1 (e g).1)
            * S2.chi (idx ch).2 (e g).2 := by
      rw [_root_.map_mul, _root_.map_mul, Complex.conj_conj]
    have e2 : (starRingEnd ℂ) (R2 (e g).2 * (starRingEnd ℂ) (S2.chi (idx ch).2 (e g).2))
        = (starRingEnd ℂ) (R2 (e g).2) * S2.chi (idx ch).2 (e g).2 := by
      rw [_root_.map_mul, Complex.conj_conj]
    rw [hA g, hchi ch g, e1, e2]
    ring
  rw [Finset.sum_congr rfl fun g _ => hterm g, ← Finset.mul_sum, mul_assoc]
  congr 1
  rw [← Equiv.sum_comp e.symm (fun g : G =>
    (R1 (e g).1 * (starRingEnd ℂ) (S1.chi (idx ch).1 (e g).1))
      * (starRingEnd ℂ) (R2 (e g).2 * (starRingEnd ℂ) (S2.chi (idx ch).2 (e g).2)))]
  have hsimp : ∀ p : G1 × G2,
      (R1 (e (e.symm p)).1 * (starRingEnd ℂ) (S1.chi (idx ch).1 (e (e.symm p)).1))
        * (starRingEnd ℂ) (R2 (e (e.symm p)).2
            * (starRingEnd ℂ) (S2.chi (idx ch).2 (e (e.symm p)).2))
      = (R1 p.1 * (starRingEnd ℂ) (S1.chi (idx ch).1 p.1))
        * (starRingEnd ℂ) (R2 p.2 * (starRingEnd ℂ) (S2.chi (idx ch).2 p.2)) := by
    intro p
    rw [Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl fun p _ => hsimp p, Fintype.sum_prod_type]
  rw [map_sum, Finset.sum_mul_sum]

/-- Modulus form: the unit phase disappears. -/
theorem rankOne_source_character_factor_modulus
    {G G1 G2 : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
    [Fintype G1] [DecidableEq G1] [CommGroup G1] [Fintype G2] [DecidableEq G2] [CommGroup G2]
    {Ch Ch1 Ch2 : Type*} [Fintype Ch] [DecidableEq Ch] [Fintype Ch1] [DecidableEq Ch1]
    [Fintype Ch2] [DecidableEq Ch2]
    (S : MulCharSystem G Ch) (S1 : MulCharSystem G1 Ch1) (S2 : MulCharSystem G2 Ch2)
    (e : G ≃ G1 × G2) (idx : Ch → Ch1 × Ch2) (w : Ch → ℂ)
    (R1 : G1 → ℂ) (R2 : G2 → ℂ) (A : G → ℂ)
    (hA : ∀ g : G, A g = R1 (e g).1 * (starRingEnd ℂ) (R2 (e g).2))
    (hchi : ∀ (ch : Ch) (g : G), S.chi ch g
      = w ch * S1.chi (idx ch).1 (e g).1 * (starRingEnd ℂ) (S2.chi (idx ch).2 (e g).2))
    (hw : ∀ ch : Ch, ‖w ch‖ = 1) (ch : Ch) :
    ‖S.hat A ch‖ = ‖S1.hat R1 (idx ch).1‖ * ‖S2.hat R2 (idx ch).2‖ := by
  rw [rankOne_source_character_factor S S1 S2 e idx w R1 R2 A hA hchi ch]
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj, hw ch, one_mul]

/-- **Parseval in the `(ZMod q)ˣ` normalisation**: the character energy is
`φ(q)` times the residue energy. -/
theorem character_parseval_totient {q : ℕ} [NeZero q]
    {Ch : Type*} [Fintype Ch] [DecidableEq Ch]
    (S : MulCharSystem (ZMod q)ˣ Ch) (R : (ZMod q)ˣ → ℂ) :
    ∑ ch : Ch, ‖S.hat R ch‖ ^ 2 = (q.totient : ℝ) * ∑ g : (ZMod q)ˣ, ‖R g‖ ^ 2 := by
  rw [S.character_parseval R, ZMod.card_units_eq_totient q]

end MulCharSystem

end Gate1B.SafeAlgebra
