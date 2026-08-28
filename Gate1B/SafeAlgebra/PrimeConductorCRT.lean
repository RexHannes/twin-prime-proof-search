/-
# Gate 1B v8.4 — prime character CRT factorisation `c = p c₀`

**Status: PROVED_ALGEBRAIC.**

For `c = p c₀` with `p` prime and `gcd(p, c₀) = 1`:

* `primeConductor_char_equiv` — the concrete CRT ring isomorphism
  `ZMod (p c₀) ≃+* ZMod p × ZMod c₀` (Mathlib's `ZMod.chineseRemainder`) turns a
  pair of multiplicative functions into a multiplicative function modulo `c`;
* `primeConductor_gauss_factor` — the induced Gauss factorisation

    `τ_c(χ) = χ_p(c₀) · χ_{c₀}(p) · τ_p(χ_p) · τ_{c₀}(χ_{c₀})`,

  in which **every cross factor is derived** (from the unit-shift lemma
  `gaussShift_unit`), not hard-coded.

The CRT split of the additive phase is the one supplied hypothesis; it is the
statement that `e_{pc₀}(x) = e_p(x c̄₀) e_{c₀}(x p̄)` in the repository's Fourier
convention.
-/
import Mathlib
import Gate1B.SafeAlgebra.InducedGaussFactor

namespace Gate1B.SafeAlgebra

open Finset

/-- **Character CRT.**  For coprime moduli, a pair of multiplicative functions
transported along `ZMod.chineseRemainder` is multiplicative. -/
theorem primeConductor_char_equiv {m n : ℕ} (h : Nat.Coprime m n)
    (chi1 : ZMod m → ℂ) (chi2 : ZMod n → ℂ)
    (hmul1 : ∀ x y, chi1 (x * y) = chi1 x * chi1 y)
    (hmul2 : ∀ x y, chi2 (x * y) = chi2 x * chi2 y) :
    ∀ x y : ZMod (m * n),
      (fun z : ZMod (m * n) =>
          chi1 ((ZMod.chineseRemainder h z).1) * chi2 ((ZMod.chineseRemainder h z).2)) (x * y)
        = (fun z : ZMod (m * n) =>
            chi1 ((ZMod.chineseRemainder h z).1) * chi2 ((ZMod.chineseRemainder h z).2)) x *
          (fun z : ZMod (m * n) =>
            chi1 ((ZMod.chineseRemainder h z).1) * chi2 ((ZMod.chineseRemainder h z).2)) y := by
  intro x y
  simp only [map_mul, Prod.fst_mul, Prod.snd_mul, hmul1, hmul2]
  ring

/-- **CRT Gauss factorisation.**  With the CRT split of the additive phase
supplied, the Gauss sum modulo `m n` factors, with the two derived cross factors
`chi1 n` and `chi2 m`. -/
theorem crt_gauss_factor {m n : ℕ} [NeZero m] [NeZero n]
    (chi1 psi1 : ZMod m → ℂ) (chi2 psi2 : ZMod n → ℂ)
    (chi psi : ZMod m × ZMod n → ℂ) (nbar : ZMod m) (mbar : ZMod n)
    (hmul1 : ∀ x y, chi1 (x * y) = chi1 x * chi1 y)
    (hmul2 : ∀ x y, chi2 (x * y) = chi2 x * chi2 y)
    (hnbar : (n : ZMod m) * nbar = 1) (hmbar : (m : ZMod n) * mbar = 1)
    (hchi : ∀ a b, chi (a, b) = chi1 a * chi2 b)
    (hpsi : ∀ a b, psi (a, b) = psi1 (a * nbar) * psi2 (b * mbar)) :
    ∑ x : ZMod m × ZMod n, chi x * psi x
      = chi1 (n : ZMod m) * chi2 (m : ZMod n)
          * (∑ a : ZMod m, chi1 a * psi1 a) * (∑ b : ZMod n, chi2 b * psi2 b) := by
  have hsplit : ∑ x : ZMod m × ZMod n, chi x * psi x
      = (∑ a : ZMod m, chi1 a * psi1 (a * nbar)) * (∑ b : ZMod n, chi2 b * psi2 (b * mbar)) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hchi, hpsi]; ring
  rw [hsplit, gaussShift_unit chi1 psi1 (n : ZMod m) nbar hnbar hmul1,
    gaussShift_unit chi2 psi2 (m : ZMod n) mbar hmbar hmul2]
  ring

/-- **Prime-conductor specialisation** `c = p c₀`: the Gauss sum modulo `c`
factors as `χ_p(c₀) χ_{c₀}(p) τ_p τ_{c₀}`. -/
theorem primeConductor_gauss_factor {p c0 : ℕ} [NeZero p] [NeZero c0]
    (chiP psiP : ZMod p → ℂ) (chiC0 psiC0 : ZMod c0 → ℂ)
    (chi psi : ZMod p × ZMod c0 → ℂ) (c0bar : ZMod p) (pbar : ZMod c0)
    (hmulP : ∀ x y, chiP (x * y) = chiP x * chiP y)
    (hmulC0 : ∀ x y, chiC0 (x * y) = chiC0 x * chiC0 y)
    (hc0bar : (c0 : ZMod p) * c0bar = 1) (hpbar : (p : ZMod c0) * pbar = 1)
    (hchi : ∀ a b, chi (a, b) = chiP a * chiC0 b)
    (hpsi : ∀ a b, psi (a, b) = psiP (a * c0bar) * psiC0 (b * pbar)) :
    ∑ x : ZMod p × ZMod c0, chi x * psi x
      = chiP (c0 : ZMod p) * chiC0 (p : ZMod c0)
          * (∑ a : ZMod p, chiP a * psiP a) * (∑ b : ZMod c0, chiC0 b * psiC0 b) :=
  crt_gauss_factor chiP psiP chiC0 psiC0 chi psi c0bar pbar hmulP hmulC0 hc0bar hpbar hchi hpsi

end Gate1B.SafeAlgebra
