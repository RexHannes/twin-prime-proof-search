/-
# Gate 1B v8.3 — same-`q` character diagonalisation

**Status: PROVED_ALGEBRAIC (Tier 2: both character systems are supplied).**

The same-`q` residual attaches to a residue vector `R : (ZMod q)ˣ → ℂ` and the
Kloosterman kernel

    K_{t,b}(u) = S(t u⁻¹, b ; q),

the exact finite object

    F(t) = ∑_u R(u) K_{t,b}(u).

Here we prove the two exact finite identities behind it:

* `sameQ_character_expand` —
  `F(t) = φ(q)⁻¹ ∑_χ R̂(χ) τ(χ)² χ(b) χ(t)`, with every conjugation *derived*
  (via `gauss_twist` and `chi_inv`), not postulated;
* `sameQ_gram_expand` — the double character Gram of `∑_{t ∈ T} |F(t)|²`
  against an arbitrary finite dual family `T`, with the dual correlation
  `∑_{t ∈ T} χ(t) conj ψ(t)` isolated as `dualCorrelation`.

**No analytic bound is asserted.**  In particular nothing here says that
`τ(χ)`, `R̂(χ)` or the dual correlations are small, and the nine-factor
analytic moment stays open.
-/
import Mathlib
import Gate1B.SafeAlgebra.ReciprocalCharacterExpansion

namespace Gate1B.SafeAlgebra

open Finset

variable {q : ℕ} [NeZero q] {Ch : Type*} [Fintype Ch] [DecidableEq Ch]

/-- The same-`q` Kloosterman kernel `K_{t,b}(u) = S(t u⁻¹, b; q)`. -/
noncomputable def sameQKernel (C : AdditiveCharacterSystem q) (t b u : (ZMod q)ˣ) : ℂ :=
  C.kloosterman ((t : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) (b : ZMod q)

/-- Reindexing the Kloosterman variable `v = u w` in the same-`q` kernel. -/
theorem sameQKernel_reindex (C : AdditiveCharacterSystem q) (t b u : (ZMod q)ˣ) :
    sameQKernel C t b u
      = ∑ w : (ZMod q)ˣ, C.chi ((t : ZMod q) * (w : ZMod q)) *
          C.chi ((b : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((w⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  classical
  unfold sameQKernel AdditiveCharacterSystem.kloosterman
  rw [← Equiv.sum_comp (Equiv.mulLeft u)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ((u * w : (ZMod q)ˣ) : ZMod q) = (u : ZMod q) * (w : ZMod q) := by push_cast; ring
  have hci : (((u * w)⁻¹ : (ZMod q)ˣ) : ZMod q)
      = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((w⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    rw [mul_inv_rev]; push_cast; ring
  have h1 : (t : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u * w : (ZMod q)ˣ) : ZMod q)
      = (t : ZMod q) * (w : ZMod q) := by
    rw [hc]
    have hinv : ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q) = 1 := by norm_cast; simp
    calc (t : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * (w : ZMod q))
        = (t : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) * (w : ZMod q) := by ring
      _ = (t : ZMod q) * (w : ZMod q) := by rw [hinv, mul_one]
  simp only [Equiv.coe_mulLeft, h1, hci]
  rw [C.add, ← mul_assoc]

/-- The character transform of the same-`q` kernel. -/
noncomputable def kloostermanCharSum (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (c : Ch) (t b : (ZMod q)ˣ) : ℂ :=
  ∑ u : (ZMod q)ˣ, S.chi c u * sameQKernel C t b u

/-- **Exact evaluation of the twisted kernel**: `∑_u χ(u) K_{t,b}(u) = τ(χ)² χ(b) χ(t)`.
The two Gauss factors and the `b t` character factor are *derived*. -/
theorem kloostermanCharSum_eq (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (c : Ch) (t b : (ZMod q)ˣ) :
    kloostermanCharSum C S c t b = tauCoeff C S c ^ 2 * S.chi c b * S.chi c t := by
  classical
  unfold kloostermanCharSum
  simp_rw [sameQKernel_reindex, Finset.mul_sum]
  rw [Finset.sum_comm]
  have inner : ∀ w : (ZMod q)ˣ,
      ∑ u : (ZMod q)ˣ, S.chi c u * (C.chi ((t : ZMod q) * (w : ZMod q)) *
        C.chi ((b : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((w⁻¹ : (ZMod q)ˣ) : ZMod q)))
      = tauCoeff C S c * S.chi c b *
          ((starRingEnd ℂ) (S.chi c w) * C.chi ((t : ZMod q) * (w : ZMod q))) := by
    intro w
    have step : ∀ u : (ZMod q)ˣ,
        S.chi c u * (C.chi ((t : ZMod q) * (w : ZMod q)) *
          C.chi ((b : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((w⁻¹ : (ZMod q)ˣ) : ZMod q)))
        = C.chi ((t : ZMod q) * (w : ZMod q)) *
            (C.chi (((b * w⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) *
              (starRingEnd ℂ) (S.chi c u⁻¹)) := by
      intro u
      have hc : ((b * w⁻¹ : (ZMod q)ˣ) : ZMod q) = (b : ZMod q) * ((w⁻¹ : (ZMod q)ˣ) : ZMod q) := by
        push_cast; ring
      have hchi : (starRingEnd ℂ) (S.chi c u⁻¹) = S.chi c u := by
        rw [S.chi_inv]; simp
      rw [hc, hchi]
      ring_nf
    simp_rw [step]
    rw [← Finset.mul_sum]
    have hgauss : ∑ u : (ZMod q)ˣ,
        C.chi (((b * w⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          (starRingEnd ℂ) (S.chi c u⁻¹)
        = gaussCoeff C S c ((b * w⁻¹ : (ZMod q)ˣ) : ZMod q) := by
      unfold gaussCoeff
      rw [← Equiv.sum_comp (Equiv.inv (ZMod q)ˣ)]
      simp
    rw [hgauss, gauss_twist C S c (b * w⁻¹), S.map_mul, S.chi_inv]
    ring
  simp_rw [inner]
  rw [← Finset.mul_sum]
  have hg2 : ∑ w : (ZMod q)ˣ, ((starRingEnd ℂ) (S.chi c w) * C.chi ((t : ZMod q) * (w : ZMod q)))
      = gaussCoeff C S c (t : ZMod q) := by
    unfold gaussCoeff
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [hg2, gauss_twist C S c t]
  unfold tauCoeff
  ring

/-- The same-`q` residual `F(t) = ∑_u R(u) K_{t,b}(u)`. -/
noncomputable def sameQF (C : AdditiveCharacterSystem q) (R : (ZMod q)ˣ → ℂ)
    (b t : (ZMod q)ˣ) : ℂ :=
  ∑ u : (ZMod q)ˣ, R u * sameQKernel C t b u

/-- **Same-`q` character expansion.** -/
theorem sameQ_character_expand (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (R : (ZMod q)ˣ → ℂ) (b t : (ZMod q)ˣ) :
    sameQF C R b t
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          ∑ c : Ch, S.hat R c * (tauCoeff C S c ^ 2 * S.chi c b * S.chi c t) := by
  classical
  unfold sameQF
  rw [show (∑ u : (ZMod q)ˣ, R u * sameQKernel C t b u)
      = ∑ u : (ZMod q)ˣ, ((1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          ∑ c : Ch, S.hat R c * S.chi c u) * sameQKernel C t b u from
    Finset.sum_congr rfl fun u _ => by rw [← S.character_fourier_inversion' R u]]
  have expand : ∀ u : (ZMod q)ˣ,
      ((1 / (Fintype.card (ZMod q)ˣ : ℂ)) * ∑ c : Ch, S.hat R c * S.chi c u) *
          sameQKernel C t b u
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          ∑ c : Ch, S.hat R c * (S.chi c u * sameQKernel C t b u) := by
    intro u
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  simp_rw [expand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact kloostermanCharSum_eq C S c t b

/-- The dual correlation of two characters over a finite dual family `T`. -/
noncomputable def dualCorrelation (S : MulCharSystem (ZMod q)ˣ Ch) (T : Finset (ZMod q)ˣ)
    (c d : Ch) : ℂ :=
  ∑ t ∈ T, S.chi c t * (starRingEnd ℂ) (S.chi d t)

/-- The same-`q` Gram weight attached to a pair of characters. -/
noncomputable def sameQGramWeight (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (R : (ZMod q)ˣ → ℂ) (b : (ZMod q)ˣ) (c d : Ch) : ℂ :=
  (tauCoeff C S c ^ 2 * (starRingEnd ℂ) (tauCoeff C S d ^ 2)) *
    (S.chi c b * (starRingEnd ℂ) (S.chi d b)) *
    (S.hat R c * (starRingEnd ℂ) (S.hat R d))

/-- **Same-`q` Gram expansion.**  The mass of `F` over an arbitrary finite dual
family `T` is an exact double character Gram. -/
theorem sameQ_gram_expand (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (R : (ZMod q)ˣ → ℂ) (b : (ZMod q)ˣ)
    (T : Finset (ZMod q)ˣ) :
    ∑ t ∈ T, sameQF C R b t * (starRingEnd ℂ) (sameQF C R b t)
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) ^ 2 *
          ∑ c : Ch, ∑ d : Ch, sameQGramWeight C S R b c d * dualCorrelation S T c d := by
  classical
  have hconj : (starRingEnd ℂ) (1 / (Fintype.card (ZMod q)ˣ : ℂ))
      = 1 / (Fintype.card (ZMod q)ˣ : ℂ) := by
    simp
  have hterm : ∀ t : (ZMod q)ˣ, sameQF C R b t * (starRingEnd ℂ) (sameQF C R b t)
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) ^ 2 *
          ∑ c : Ch, ∑ d : Ch, sameQGramWeight C S R b c d *
            (S.chi c t * (starRingEnd ℂ) (S.chi d t)) := by
    intro t
    rw [sameQ_character_expand C S R b t]
    rw [map_mul, hconj, map_sum]
    rw [show (1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          (∑ c : Ch, S.hat R c * (tauCoeff C S c ^ 2 * S.chi c b * S.chi c t)) *
        ((1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          ∑ d : Ch, (starRingEnd ℂ) (S.hat R d * (tauCoeff C S d ^ 2 * S.chi d b * S.chi d t)))
        = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) ^ 2 *
          ((∑ c : Ch, S.hat R c * (tauCoeff C S c ^ 2 * S.chi c b * S.chi c t)) *
            ∑ d : Ch, (starRingEnd ℂ) (S.hat R d * (tauCoeff C S d ^ 2 * S.chi d b * S.chi d t)))
        from by ring]
    congr 1
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    unfold sameQGramWeight
    simp only [map_mul]
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum]
  rfl

end Gate1B.SafeAlgebra
