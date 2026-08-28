/-
# Gate 1B v8.4 — the induced Gauss factor

**Status: PROVED_ALGEBRAIC (Tier 2: CRT split and Ramanujan value supplied as
explicit hypotheses; the factor `μ(e) χ*(e)` is *derived*, never assumed).**

Target identity, for `gcd(c, e) = 1`, `e` squarefree and `χ*` primitive mod `c`:

  `τ_{ce}(ind χ*) = μ(e) · χ*(e) · τ_c(χ*)`.

TIER 1.  Mathlib's `gaussSum` is the sum `∑ a, χ a * ψ a`; the abstract sums
used below are literally of that shape (`gaussSum_eq_abstract`), so the result
is stated in the repository's Fourier convention with no re-normalisation.
Mathlib does **not** currently provide the conductor/induction API (primitive
characters, induced characters modulo `c e`, Ramanujan sums for squarefree
moduli), so the full concrete derivation is not available.

TIER 2 (what is proved here).  The two structural inputs are supplied as
hypotheses:

* the CRT split of the modulus `c e` into `(ZMod c) × (ZMod e)`, under which the
  induced character becomes `χ*(a) · 1_{(b,e)=1}` and the additive phase becomes
  `ψ_c(a ē) ψ_e(b c̄)`;
* the Ramanujan-sum value `∑_b 1_{(b,e)=1} ψ_e(b c̄) = μ(e)` (squarefree `e`,
  `c̄` a unit).

Everything else — in particular the *twist* `χ*(e)`, which is where the sign and
orientation conventions live — is derived, from the unit-shift lemma
`gaussShift_unit`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset
open scoped ArithmeticFunction.Moebius

/-! ## The unit shift of a Gauss sum -/

/-- **Twisted Gauss shift.**  If `t · t̄ = 1` in a finite commutative ring and
`chi` is multiplicative, then shifting the additive phase by `t̄` multiplies the
Gauss sum by `chi t`.  (This is the abstract form of
`gaussSum χ (ψ.mulShift t̄) = χ(t) gaussSum χ ψ`.) -/
theorem gaussShift_unit {R : Type*} [CommRing R] [Fintype R]
    (chi psi : R → ℂ) (t tbar : R) (ht : t * tbar = 1)
    (hmul : ∀ x y, chi (x * y) = chi x * chi y) :
    ∑ a : R, chi a * psi (a * tbar) = chi t * ∑ a : R, chi a * psi a := by
  have hbij : Function.Bijective (fun s : R => s * t) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun s => s * tbar, ?_, ?_⟩
    · intro s; simp [mul_assoc, ht]
    · intro s; simp [mul_assoc, mul_comm tbar t, ht]
  have key := Fintype.sum_bijective (fun s : R => s * t) hbij
    (fun s => chi s * chi t * psi s) (fun a => chi a * psi (a * tbar)) ?_
  · rw [← key, Finset.mul_sum]; exact Finset.sum_congr rfl (fun s _ => by ring)
  · intro x
    show chi x * chi t * psi x = chi (x * t) * psi (x * t * tbar)
    rw [hmul x t, mul_assoc x t tbar, ht, mul_one]

/-- The abstract Gauss sum used here **is** Mathlib's `gaussSum` in the same
Fourier convention. -/
theorem gaussSum_eq_abstract {R : Type*} [CommRing R] [Fintype R]
    (chi : MulChar R ℂ) (psi : AddChar R ℂ) :
    gaussSum chi psi = ∑ a : R, chi a * psi a := rfl

/-! ## The induced Gauss factor -/

/-- **Induced Gauss factor (Tier 2).**  With the CRT split of the modulus and
the Ramanujan value supplied, the Gauss sum of the induced character modulo
`c e` equals `μ(e) χ*(e) τ_c(χ*)`.

Hypotheses:
* `hmul` — multiplicativity of `χ*` on `ZMod c`;
* `hebar` — `ē` is the inverse of `e` modulo `c` (this is where `gcd(c,e)=1`
  enters);
* `hchi` — the induced character splits as `χ*(a) · unitE b` under CRT
  (`unitE` is the indicator of `(b, e) = 1`);
* `hpsi` — the CRT split of the additive phase modulo `c e`;
* `hram` — the Ramanujan sum modulo the squarefree `e` equals `μ(e)`. -/
theorem induced_gauss_squarefree {c e : ℕ} [NeZero c] [NeZero e]
    (chiStar psiC : ZMod c → ℂ) (psiE unitE : ZMod e → ℂ)
    (chiInd psiCE : ZMod c × ZMod e → ℂ)
    (ebar : ZMod c) (cbar : ZMod e)
    (hmul : ∀ x y, chiStar (x * y) = chiStar x * chiStar y)
    (hebar : (e : ZMod c) * ebar = 1)
    (hchi : ∀ a b, chiInd (a, b) = chiStar a * unitE b)
    (hpsi : ∀ a b, psiCE (a, b) = psiC (a * ebar) * psiE (b * cbar))
    (hram : ∑ b : ZMod e, unitE b * psiE (b * cbar) = (μ e : ℂ)) :
    ∑ x : ZMod c × ZMod e, chiInd x * psiCE x
      = (μ e : ℂ) * chiStar (e : ZMod c) * ∑ a : ZMod c, chiStar a * psiC a := by
  have hsplit : ∑ x : ZMod c × ZMod e, chiInd x * psiCE x
      = (∑ a : ZMod c, chiStar a * psiC (a * ebar)) *
        (∑ b : ZMod e, unitE b * psiE (b * cbar)) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hchi, hpsi]; ring
  rw [hsplit, hram, gaussShift_unit chiStar psiC (e : ZMod c) ebar hebar hmul]
  ring

end Gate1B.SafeAlgebra
