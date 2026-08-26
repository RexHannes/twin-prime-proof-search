/-
# Gate 1B v8.3 — generic finite multiplicative character system

**Status: PROVED_ALGEBRAIC (Tier 2: hypothesis-carrying interface).**

Mathlib's `DirichletCharacter` / `gaussSum` machinery is concrete and is used
elsewhere; here we need the *generic* finite Fourier calculus on an arbitrary
finite abelian group, with every analytic-free structural fact (multiplicativity,
unimodularity, both orthogonality relations) supplied as an explicit field of a
structure.  Nothing is axiomatised and nothing is asserted to be small.

Contents:

* `MulCharSystem G Ch` — the interface;
* `chi_one`, `chi_inv`, `chi_mul_conj` — derived elementary identities (the
  conjugations are *derived*, never hard-coded);
* `hat` — the finite Fourier coefficient;
* `character_fourier_inversion`, `character_parseval`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- A complete family of multiplicative characters of a finite abelian group `G`,
indexed by a finite type `Ch`, with both orthogonality relations supplied. -/
structure MulCharSystem (G : Type*) [Fintype G] [DecidableEq G] [CommGroup G]
    (Ch : Type*) [Fintype Ch] [DecidableEq Ch] where
  /-- The characters. -/
  chi : Ch → G → ℂ
  /-- Multiplicativity. -/
  map_mul : ∀ c g h, chi c (g * h) = chi c g * chi c h
  /-- Unimodularity. -/
  norm_one : ∀ c g, ‖chi c g‖ = 1
  /-- Orthogonality of two characters over the group. -/
  orthogonality : ∀ c d : Ch,
    ∑ g : G, chi c g * (starRingEnd ℂ) (chi d g) = if c = d then (Fintype.card G : ℂ) else 0
  /-- Dual (completeness) orthogonality over the character family. -/
  dual_orthogonality : ∀ g h : G,
    ∑ c : Ch, chi c g * (starRingEnd ℂ) (chi c h) = if g = h then (Fintype.card G : ℂ) else 0

namespace MulCharSystem

variable {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] (S : MulCharSystem G Ch)

/-- A unimodular character never vanishes. -/
theorem chi_ne_zero (c : Ch) (g : G) : S.chi c g ≠ 0 := by
  intro h0
  have := S.norm_one c g
  rw [h0] at this; simp at this

/-- `χ(g) · conj χ(g) = 1`, derived from unimodularity. -/
theorem chi_mul_conj (c : Ch) (g : G) : S.chi c g * (starRingEnd ℂ) (S.chi c g) = 1 := by
  rw [Complex.mul_conj]; norm_cast; simp [Complex.normSq_eq_norm_sq, S.norm_one c g]

/-- `χ(1) = 1`. -/
theorem chi_one (c : Ch) : S.chi c 1 = 1 := by
  have h := S.map_mul c 1 1
  rw [mul_one] at h
  have h2 : S.chi c 1 * 1 = S.chi c 1 * S.chi c 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel₀ (S.chi_ne_zero c 1) h2).symm

/-- **Derived conjugation rule**: `χ(g⁻¹) = conj χ(g)`. -/
theorem chi_inv (c : Ch) (g : G) : S.chi c g⁻¹ = (starRingEnd ℂ) (S.chi c g) := by
  have h1 : S.chi c g * S.chi c g⁻¹ = 1 := by
    rw [← S.map_mul, mul_inv_cancel, S.chi_one]
  exact mul_left_cancel₀ (S.chi_ne_zero c g) (h1.trans (S.chi_mul_conj c g).symm)

/-- The finite Fourier coefficient `R̂(χ) = ∑_g R(g) conj χ(g)`. -/
noncomputable def hat (R : G → ℂ) (c : Ch) : ℂ := ∑ g : G, R g * (starRingEnd ℂ) (S.chi c g)

/-- **Finite Fourier inversion** on `G`. -/
theorem character_fourier_inversion (R : G → ℂ) (h : G) :
    ∑ c : Ch, S.hat R c * S.chi c h = (Fintype.card G : ℂ) * R h := by
  classical
  simp_rw [hat, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  have key : ∀ g : G, ∑ c : Ch, R g * ((starRingEnd ℂ) (S.chi c g) * S.chi c h)
      = R g * (if h = g then (Fintype.card G : ℂ) else 0) := by
    intro g
    rw [← Finset.mul_sum]
    congr 1
    rw [← S.dual_orthogonality h g]
    exact Finset.sum_congr rfl fun c _ => by ring
  simp_rw [key]
  simp [mul_comm]

/-- Inversion in normalised form. -/
theorem character_fourier_inversion' (R : G → ℂ) (h : G) :
    R h = (1 / (Fintype.card G : ℂ)) * ∑ c : Ch, S.hat R c * S.chi c h := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    have hp : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast Nat.cast_ne_zero.2 hp.ne'
  rw [S.character_fourier_inversion R h]
  field_simp

/-- **Parseval, complex form.** -/
theorem character_parseval_complex (R : G → ℂ) :
    ∑ c : Ch, S.hat R c * (starRingEnd ℂ) (S.hat R c)
      = (Fintype.card G : ℂ) * ∑ g : G, R g * (starRingEnd ℂ) (R g) := by
  classical
  have expand : ∀ c : Ch, S.hat R c * (starRingEnd ℂ) (S.hat R c)
      = ∑ g : G, ∑ g' : G, (R g * (starRingEnd ℂ) (R g')) *
          ((starRingEnd ℂ) (S.chi c g) * S.chi c g') := by
    intro c
    unfold hat
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun g' _ => ?_
    simp
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  have key : ∀ g : G, ∑ c : Ch, ∑ g' : G, (R g * (starRingEnd ℂ) (R g')) *
      ((starRingEnd ℂ) (S.chi c g) * S.chi c g')
      = (Fintype.card G : ℂ) * (R g * (starRingEnd ℂ) (R g)) := by
    intro g
    rw [Finset.sum_comm]
    have h' : ∀ g' : G, ∑ c : Ch, (R g * (starRingEnd ℂ) (R g')) *
        ((starRingEnd ℂ) (S.chi c g) * S.chi c g')
        = (R g * (starRingEnd ℂ) (R g')) * (if g' = g then (Fintype.card G : ℂ) else 0) := by
      intro g'
      rw [← Finset.mul_sum, ← S.dual_orthogonality g' g]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by ring
    simp_rw [h']
    simp [mul_comm]
  simp_rw [key]
  rw [← Finset.mul_sum]

/-- **Parseval**: the Fourier energy is `|G|` times the residue energy. -/
theorem character_parseval (R : G → ℂ) :
    ∑ c : Ch, ‖S.hat R c‖ ^ 2 = (Fintype.card G : ℝ) * ∑ g : G, ‖R g‖ ^ 2 := by
  have h := S.character_parseval_complex R
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-- A character is *principal* when it is identically `1`. -/
def IsPrincipal (c0 : Ch) : Prop := ∀ g : G, S.chi c0 g = 1

end MulCharSystem

end Gate1B.SafeAlgebra
