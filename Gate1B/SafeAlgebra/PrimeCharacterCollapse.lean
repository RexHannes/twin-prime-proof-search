/-
# Gate 1B v8.4 — prime-conductor character collapse

**Status: PROVED_ALGEBRAIC (Tier 1: concrete `DirichletCharacter` / `gaussSum`).**

For a prime `p`, a nontrivial additive character `ψ` of `ZMod p` and a unit
`A ∈ (ZMod p)ˣ`, with the standard Gauss sum `τ_p(χ) = ∑_a χ(a) ψ(a)`:

* `allChars_gauss_collapse`  : `∑_{χ mod p} τ_p(χ) χ(A) = (p-1) ψ(A⁻¹)`;
* `principal_gauss_eq_neg_one` : `τ_p(χ₀) = -1`;
* `nonprincipal_gauss_collapse` : `∑_{χ ≠ χ₀} τ_p(χ) χ(A) = (p-1) ψ(A⁻¹) + 1`.

Every conjugation and orientation is derived from the definitions: no formula is
hard-coded, and the additive character enters only through
`AddChar.sum_eq_zero_of_ne_one`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- **All-character Gauss collapse.**  `∑_{χ mod p} τ_p(χ) χ(A) = φ(p) ψ(A⁻¹)`
for `A` a unit. -/
theorem allChars_gauss_collapse {p : ℕ} [NeZero p] (psi : AddChar (ZMod p) ℂ) {A : ZMod p}
    (hA : IsUnit A) :
    ∑ chi : DirichletCharacter ℂ p, gaussSum chi psi * chi A = (p.totient : ℂ) * psi A⁻¹ := by
  have hAinv : A * A⁻¹ = 1 := ZMod.mul_inv_of_unit A hA
  have hinvA : A⁻¹ * A = 1 := by rw [mul_comm]; exact hAinv
  have h1 : ∀ chi : DirichletCharacter ℂ p, gaussSum chi psi * chi A
      = ∑ a : ZMod p, chi (a * A) * psi a := by
    intro chi
    rw [gaussSum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by rw [map_mul]; ring)
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ a : ZMod p, ∑ chi : DirichletCharacter ℂ p, chi (a * A) * psi a
      = (if a * A = 1 then (p.totient : ℂ) else 0) * psi a := by
    intro a
    rw [← Finset.sum_mul, DirichletCharacter.sum_characters_eq]
  simp only [h2]
  rw [Finset.sum_eq_single A⁻¹]
  · rw [if_pos hinvA]
  · intro b _ hb
    have hne : b * A ≠ 1 := by
      intro h
      refine hb ?_
      calc b = b * (A * A⁻¹) := by rw [hAinv, mul_one]
        _ = (b * A) * A⁻¹ := by ring
        _ = A⁻¹ := by rw [h, one_mul]
    rw [if_neg hne, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Principal Gauss sum.**  `τ_p(χ₀) = -1` for a nontrivial additive
character. -/
theorem principal_gauss_eq_neg_one {p : ℕ} [Fact p.Prime] {psi : AddChar (ZMod p) ℂ}
    (hpsi : psi ≠ 1) : gaussSum (1 : DirichletCharacter ℂ p) psi = -1 := by
  have hz : ∑ a : ZMod p, psi a = 0 := AddChar.sum_eq_zero_of_ne_one hpsi
  have h : gaussSum (1 : DirichletCharacter ℂ p) psi
      = ∑ a : ZMod p, (if a = 0 then 0 else psi a) := by
    rw [gaussSum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases ha : a = 0
    · simp [ha, MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : ZMod p))]
    · rw [if_neg ha, MulChar.one_apply (isUnit_iff_ne_zero.2 ha), one_mul]
  rw [h]
  have hstep : ∀ a : ZMod p, (if a = 0 then (0:ℂ) else psi a)
      = psi a - (if a = 0 then psi a else 0) := by
    intro a; by_cases ha : a = 0 <;> simp [ha]
  rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_sub_distrib, hz,
    Finset.sum_ite_eq' Finset.univ (0 : ZMod p) (fun a => psi a)]
  simp

/-- **Nonprincipal collapse.**  `∑_{χ ≠ χ₀} τ_p(χ) χ(A) = (p-1) ψ(A⁻¹) + 1`. -/
theorem nonprincipal_gauss_collapse {p : ℕ} [Fact p.Prime] {psi : AddChar (ZMod p) ℂ}
    (hpsi : psi ≠ 1) {A : ZMod p} (hA : IsUnit A) :
    ∑ chi ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ p)), gaussSum chi psi * chi A
      = ((p : ℂ) - 1) * psi A⁻¹ + 1 := by
  have hp : Fact p.Prime := ‹_›
  have hNeZero : NeZero p := ⟨hp.out.ne_zero⟩
  have htot : (p.totient : ℂ) = (p : ℂ) - 1 := by
    rw [Nat.totient_prime hp.out]
    have h1 : 1 ≤ p := hp.out.one_lt.le
    push_cast [Nat.cast_sub h1]
    ring
  have hsplit : ∑ chi : DirichletCharacter ℂ p, gaussSum chi psi * chi A
      = gaussSum (1 : DirichletCharacter ℂ p) psi * (1 : DirichletCharacter ℂ p) A
        + ∑ chi ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ p)), gaussSum chi psi * chi A := by
    rw [← Finset.sum_singleton (fun chi : DirichletCharacter ℂ p => gaussSum chi psi * chi A) 1,
      Finset.sum_add_sum_compl]
  have hall := allChars_gauss_collapse (p := p) psi hA
  rw [hsplit, principal_gauss_eq_neg_one hpsi, MulChar.one_apply hA, htot] at hall
  linear_combination hall

end Gate1B.SafeAlgebra
