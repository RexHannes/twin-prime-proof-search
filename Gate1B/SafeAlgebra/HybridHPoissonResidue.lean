/-
# Gate 1B v8.4 — hybrid h-Poisson: the finite residue part

**Status: PROVED_ALGEBRAIC (Tier 1 for the `p`-side, abstract for the `c₀`-side).**

Only the *arithmetic residue transform* underlying the hybrid `h`-sum

  `∑_h v(h/H) conj χ₀(h) e_p(a h)`

is formalised here.  Under the CRT split of the period `p c₀` (`gcd(p, c₀) = 1`)
the finite transform at dual frequency `m` factors as

  `(∑_{h₁ mod p} e_p((a - m c̄₀) h₁)) · (∑_{h₂ mod c₀} conj χ₀(h₂) e_{c₀}(-m p̄ h₂))`,

whose first factor is `p` exactly when

  `m ≡ a c₀ (mod p)`

and `0` otherwise; the second factor is the `c₀` Gauss factor with the character
twist.  **No infinite Poisson summation is used or claimed here.**
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- The residue condition `m c̄₀ = a` is the congruence `m ≡ a c₀ (mod p)`. -/
theorem residue_condition {p : ℕ} [NeZero p] {c0 c0bar a m : ZMod p} (h : c0 * c0bar = 1) :
    m * c0bar = a ↔ m = a * c0 := by
  constructor
  · intro hm
    calc m = m * (c0 * c0bar) := by rw [h, mul_one]
      _ = (m * c0bar) * c0 := by ring
      _ = a * c0 := by rw [hm]
  · intro hm
    calc m * c0bar = a * (c0 * c0bar) := by rw [hm]; ring
      _ = a := by rw [h, mul_one]

/-- **Hybrid residue transform.**  The finite `h`-transform over the period
`p c₀` splits into a `p`-additive residue factor and the `c₀`-character factor.
The `p`-factor vanishes unless the dual frequency satisfies the exact residue
condition, in which case it equals `p`. -/
theorem hybridResidueTransform {p c0 : ℕ} [NeZero p] [NeZero c0]
    (psiP : AddChar (ZMod p) ℂ) (hprim : psiP.IsPrimitive)
    (chiBar psiC0 : ZMod c0 → ℂ) (a t : ZMod p) (mc0 : ZMod c0) :
    ∑ x : ZMod p × ZMod c0, chiBar x.2 * (psiP ((a - t) * x.1) * psiC0 (x.2 * mc0))
      = (if t = a then (p : ℂ) else 0) * ∑ b : ZMod c0, chiBar b * psiC0 (b * mc0) := by
  classical
  have hfac : ∑ x : ZMod p × ZMod c0, chiBar x.2 * (psiP ((a - t) * x.1) * psiC0 (x.2 * mc0))
      = (∑ h1 : ZMod p, psiP ((a - t) * h1)) * ∑ b : ZMod c0, chiBar b * psiC0 (b * mc0) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun h1 _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  have hp : ∑ h1 : ZMod p, psiP ((a - t) * h1) = if t = a then (p : ℂ) else 0 := by
    have := AddChar.sum_mulShift (R := ZMod p) (a - t) hprim
    rw [show (∑ h1 : ZMod p, psiP ((a - t) * h1)) = ∑ h1 : ZMod p, psiP (h1 * (a - t)) from
      Finset.sum_congr rfl (fun h1 _ => by rw [mul_comm])]
    rw [this, ZMod.card]
    by_cases h : t = a
    · rw [if_pos (by rw [h, sub_self] : a - t = 0), if_pos h]
    · rw [if_neg (fun hc => h (by have := sub_eq_zero.1 hc; exact this.symm)), if_neg h]
      push_cast; ring
  rw [hfac, hp]

/-- The residue factor written directly as the congruence `m ≡ a c₀ (mod p)`. -/
theorem hybridResidue_congruence {p c0 : ℕ} [NeZero p] [NeZero c0]
    (psiP : AddChar (ZMod p) ℂ) (hprim : psiP.IsPrimitive)
    (chiBar psiC0 : ZMod c0 → ℂ) (a m c0p c0bar : ZMod p) (mc0 : ZMod c0)
    (hinv : c0p * c0bar = 1) :
    ∑ x : ZMod p × ZMod c0, chiBar x.2 * (psiP ((a - m * c0bar) * x.1) * psiC0 (x.2 * mc0))
      = (if m = a * c0p then (p : ℂ) else 0) * ∑ b : ZMod c0, chiBar b * psiC0 (b * mc0) := by
  rw [hybridResidueTransform psiP hprim chiBar psiC0 a (m * c0bar) mc0]
  by_cases h : m = a * c0p
  · rw [if_pos h, if_pos ((residue_condition hinv).2 h)]
  · rw [if_neg h, if_neg (fun hc => h ((residue_condition hinv).1 hc))]

end Gate1B.SafeAlgebra
