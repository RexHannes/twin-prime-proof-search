/-
# Gate 1B v12 — moving-multiplier prime-modulus character expansion

**Status: PROVED_ALGEBRAIC (Tier 2: hypothesis-carrying, exact finite algebra).**

This module proves, *from the definitions of the existing bank*, the concrete
multiplicative-character diagonalisation of the finite Kloosterman sum

    S(a·m, n; q) = (1/|G|) ∑_χ τ(χ)² conj(χ(a·m·n)),      G = (ZMod q)ˣ,

and its bilinear (moving-multiplier) consequence

    B_a = (1/|G|) ∑_χ τ(χ)² conj(χ(a)) α̂(χ) β̂(χ).

Conventions are *reused*, never duplicated:

* the additive character is `Gate1B.SafeAlgebra.AdditiveCharacterSystem`;
* the Kloosterman sum is `AdditiveCharacterSystem.kloosterman`;
* the multiplicative characters are `Gate1B.SafeAlgebra.MulCharSystem` on the
  unit group `(ZMod q)ˣ`, with `hat` its finite Fourier coefficient.

No conjugation is hard-coded: every conjugation below is either a field of the
supplied interfaces (`conj_eq`) or is *derived* (`MulCharSystem.chi_inv`).

Nothing here is analytic.  No Weil bound, no square-root cancellation and no
estimate of any kind is claimed; every statement is an exact finite identity.

The identities of this file are valid for an arbitrary modulus `q`; primality is
used only in `MovingMultiplierSecondMoment`, where the Gauss sum modulus is
evaluated.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteKloosterman
import Gate1B.SafeAlgebra.FiniteMultiplicativeCharacters

namespace Gate1B.SafeAlgebra

open Finset

variable {q : ℕ} [NeZero q] {Ch : Type*} [Fintype Ch] [DecidableEq Ch]

/-- The **Gauss sum** `τ(χ) = ∑_{u ∈ (ZMod q)ˣ} χ(u) e(u)` attached to the
supplied additive and multiplicative character systems. -/
noncomputable def gaussSumOf (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (c : Ch) : ℂ :=
  ∑ u : (ZMod q)ˣ, S.chi c u * C.chi ((u : ZMod q))

/-- Auxiliary exact identity: the Kloosterman sum at a unit pair only depends on
the product of its two arguments. -/
theorem kloosterman_unit_reduce (C : AdditiveCharacterSystem q) (a b : (ZMod q)ˣ) :
    C.kloosterman ((a : ZMod q)) ((b : ZMod q))
      = C.kloosterman 1 (((a * b : (ZMod q)ˣ) : ZMod q)) := by
  have h := C.kloosterman_scale 1 (((a * b : (ZMod q)ˣ) : ZMod q)) a
  have h2 : (((a * b : (ZMod q)ˣ) : ZMod q)) * (((a⁻¹ : (ZMod q)ˣ) : ZMod q))
      = ((b : ZMod q)) := by
    rw [← Units.val_mul]
    congr 1
    rw [mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]
  rw [one_mul, h2] at h
  exact h

/-- **Exact multiplicative-character diagonalisation of the Kloosterman sum.**

For units `a, b` of `ZMod q`,

    ∑_χ τ(χ)² conj(χ(a·b)) = |G| · S(a, b; q).

The only inputs are the dual orthogonality relation of the multiplicative
character system, the additivity of the additive character, and the banked
unit-reindexing invariance `kloosterman_scale`. -/
theorem kloosterman_character_expand (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (a b : (ZMod q)ˣ) :
    ∑ c : Ch, (gaussSumOf C S c) ^ 2 * (starRingEnd ℂ) (S.chi c (a * b))
      = (Fintype.card (ZMod q)ˣ : ℂ) * C.kloosterman ((a : ZMod q)) ((b : ZMod q)) := by
  classical
  set N : ℂ := (Fintype.card (ZMod q)ˣ : ℂ) with hN
  -- Step 1: expand the square of the Gauss sum into a double sum over the unit group.
  have expand : ∀ c : Ch, (gaussSumOf C S c) ^ 2 * (starRingEnd ℂ) (S.chi c (a * b))
      = ∑ x : (ZMod q)ˣ, ∑ y : (ZMod q)ˣ,
          (C.chi ((x : ZMod q)) * C.chi ((y : ZMod q))) *
            (S.chi c (x * y) * (starRingEnd ℂ) (S.chi c (a * b))) := by
    intro c
    rw [sq, gaussSumOf, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [S.map_mul, map_mul]
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  -- Step 2: the inner `∑_χ` is the dual orthogonality delta.
  have key : ∀ x : (ZMod q)ˣ,
      ∑ c : Ch, ∑ y : (ZMod q)ˣ,
        (C.chi ((x : ZMod q)) * C.chi ((y : ZMod q))) *
          (S.chi c (x * y) * (starRingEnd ℂ) (S.chi c (a * b)))
        = N * C.chi ((x : ZMod q) + (((x⁻¹ * (a * b) : (ZMod q)ˣ) : ZMod q))) := by
    intro x
    rw [Finset.sum_comm]
    have inner : ∀ y : (ZMod q)ˣ,
        ∑ c : Ch, (C.chi ((x : ZMod q)) * C.chi ((y : ZMod q))) *
            (S.chi c (x * y) * (starRingEnd ℂ) (S.chi c (a * b)))
          = (C.chi ((x : ZMod q)) * C.chi ((y : ZMod q))) *
              (if y = x⁻¹ * (a * b) then N else 0) := by
      intro y
      rw [← Finset.mul_sum, S.dual_orthogonality (x * y) (a * b)]
      congr 1
      refine if_congr ?_ rfl rfl
      exact (eq_inv_mul_iff_mul_eq).symm
    simp_rw [inner, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ (x⁻¹ * (a * b))]
    simp only [Finset.mem_univ, if_true]
    rw [← C.add]
    ring
  simp_rw [key, ← Finset.mul_sum]
  congr 1
  rw [kloosterman_unit_reduce C a b]
  unfold AdditiveCharacterSystem.kloosterman
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  push_cast
  ring

/-- **The moving-multiplier bilinear form.**

    B_a(α, β) = ∑_{m,n ∈ (ZMod q)ˣ} α_m β_n S(a·m, n; q),

for an arbitrary residue `a`.  The typing of `α, β` *is* the unit-support
hypothesis: they are functions on the unit group. -/
noncomputable def movingMultiplier (C : AdditiveCharacterSystem q)
    (alpha beta : (ZMod q)ˣ → ℂ) (a : ZMod q) : ℂ :=
  ∑ m : (ZMod q)ˣ, ∑ n : (ZMod q)ˣ,
    alpha m * beta n * C.kloosterman (a * ((m : ZMod q))) ((n : ZMod q))

/-- **Exact character expansion of the moving-multiplier bilinear form.**

For a *unit* multiplier `a`,

    |G| · B_a = ∑_χ τ(χ)² conj(χ(a)) α̂(χ) β̂(χ),

where `α̂ = S.hat α` is the banked finite Fourier coefficient.  The principal
character is included in the sum. -/
theorem movingMultiplier_bilinear_expand (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (alpha beta : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    (Fintype.card (ZMod q)ˣ : ℂ) * movingMultiplier C alpha beta ((a : ZMod q))
      = ∑ c : Ch, (gaussSumOf C S c) ^ 2 * (starRingEnd ℂ) (S.chi c a) *
          S.hat alpha c * S.hat beta c := by
  classical
  set N : ℂ := (Fintype.card (ZMod q)ˣ : ℂ) with hN
  -- expand the right-hand side
  have hrhs : ∀ c : Ch,
      (gaussSumOf C S c) ^ 2 * (starRingEnd ℂ) (S.chi c a) * S.hat alpha c * S.hat beta c
        = ∑ m : (ZMod q)ˣ, ∑ n : (ZMod q)ˣ, alpha m * beta n *
            ((gaussSumOf C S c) ^ 2 * (starRingEnd ℂ) (S.chi c (a * m * n))) := by
    intro c
    simp only [MulCharSystem.hat]
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [S.map_mul, map_mul]
    ring
  simp_rw [hrhs]
  rw [Finset.sum_comm]
  have step : ∀ m : (ZMod q)ˣ,
      ∑ c : Ch, ∑ n : (ZMod q)ˣ, alpha m * beta n *
          ((gaussSumOf C S c) ^ 2 * (starRingEnd ℂ) (S.chi c (a * m * n)))
        = ∑ n : (ZMod q)ˣ, alpha m * beta n *
            (N * C.kloosterman ((((a * m : (ZMod q)ˣ)) : ZMod q)) ((n : ZMod q))) := by
    intro m
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum, kloosterman_character_expand C S (a * m) n]
  simp_rw [step]
  unfold movingMultiplier
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Units.val_mul]
  ring

/-- Normalised form of the expansion: `B_a` itself, with the `1/|G|` factor
displayed. -/
theorem movingMultiplier_bilinear_expand' (C : AdditiveCharacterSystem q)
    (S : MulCharSystem (ZMod q)ˣ Ch) (alpha beta : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    movingMultiplier C alpha beta ((a : ZMod q))
      = (1 / (Fintype.card (ZMod q)ˣ : ℂ)) *
          ∑ c : Ch, (gaussSumOf C S c) ^ 2 * (starRingEnd ℂ) (S.chi c a) *
            S.hat alpha c * S.hat beta c := by
  have hcard : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0 := by
    have hp : 0 < Fintype.card (ZMod q)ˣ := Fintype.card_pos
    exact_mod_cast Nat.cast_ne_zero.2 hp.ne'
  rw [← movingMultiplier_bilinear_expand C S alpha beta a]
  field_simp

end Gate1B.SafeAlgebra
