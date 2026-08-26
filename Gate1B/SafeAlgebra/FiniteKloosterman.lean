/-
# Gate 1B v8.2 — finite Kloosterman sums under an explicit character system

**Tier 2 (hypothesis-carrying).**  All the finite Kloosterman structure used by
Gate 1B is developed relative to an *explicitly supplied* additive character
system `AdditiveCharacterSystem q`: additivity, unimodularity, conjugation and
orthogonality are fields of the structure, not global assumptions and not
axioms.  Nothing here constructs such a system, and nothing here is analytic:
no Weil bound, no square-root cancellation is claimed.

Contents:

* `AdditiveCharacterSystem` — the interface;
* `chi_zero`, `chi_ne_zero` — elementary consequences;
* `kloosterman` — the finite Kloosterman sum `S(A,B) = ∑_{u ∈ (ZMod q)ˣ}
  χ(Au + Bu⁻¹)`;
* `kloosterman_scale` — the exact unit-reindexing invariance
  `S(Ac, Bc⁻¹) = S(A,B)`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- An explicit additive character system modulo `q`: a unimodular additive
character with the standard orthogonality relation.  Supplied, never assumed. -/
structure AdditiveCharacterSystem (q : ℕ) [NeZero q] where
  /-- The character. -/
  chi : ZMod q → ℂ
  /-- Additivity. -/
  add : ∀ x y, chi (x + y) = chi x * chi y
  /-- Unimodularity. -/
  norm_one : ∀ x, ‖chi x‖ = 1
  /-- Conjugation reverses the argument. -/
  conj_eq : ∀ x, (starRingEnd ℂ) (chi x) = chi (-x)
  /-- Orthogonality of the additive characters. -/
  orthogonality : ∀ x : ZMod q, ∑ a : ZMod q, chi (a * x) = if x = 0 then (q : ℂ) else 0

namespace AdditiveCharacterSystem

variable {q : ℕ} [NeZero q] (C : AdditiveCharacterSystem q)

/-- A unimodular character never vanishes. -/
theorem chi_ne_zero (x : ZMod q) : C.chi x ≠ 0 := by
  intro h0
  have := C.norm_one x
  rw [h0] at this
  simp at this

/-- `χ(0) = 1`. -/
theorem chi_zero : C.chi 0 = 1 := by
  have h := C.add 0 0
  rw [add_zero] at h
  have : C.chi 0 * 1 = C.chi 0 * C.chi 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel₀ (C.chi_ne_zero 0) this).symm

/-- The finite Kloosterman sum `S(A,B) = ∑_{u ∈ (ZMod q)ˣ} χ(Au + Bu⁻¹)`. -/
noncomputable def kloosterman (A B : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, C.chi (A * (u : ZMod q) + B * ((u⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- **Unit-reindexing invariance** of the Kloosterman sum:
`S(Ac, Bc⁻¹) = S(A,B)` for every unit `c`. -/
theorem kloosterman_scale (A B : ZMod q) (c : (ZMod q)ˣ) :
    C.kloosterman (A * (c : ZMod q)) (B * ((c⁻¹ : (ZMod q)ˣ) : ZMod q)) = C.kloosterman A B := by
  classical
  unfold kloosterman
  rw [← Equiv.sum_comp (Equiv.mulLeft c⁻¹)]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  simp [mul_comm, mul_assoc, mul_left_comm]

end AdditiveCharacterSystem

end Gate1B.SafeAlgebra
