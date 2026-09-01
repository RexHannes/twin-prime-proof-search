import Gate1B.HStarCenteredAdditiveProjector

/-!
# Gate 1B · FM722 · the centred **one-factor completion**

**Everything in this module is exact finite Fourier algebra over `ZMod q`.**
No analytic estimate is proved here, none is assumed, and no analytic interface
is inhabited.  Nothing outside this file is modified: the additive character
`eM`, the Ramanujan sum `ramanujanSum`, the unit-sector principal model
`unitPrincipal` and the centred projector `centeredProjector` are the
repository's own objects, re-used unchanged.

## The normalised DFT convention (fixed once and for all)

```
  hatAlpha (k) = ∑_{A mod q} alpha(A) e_q(−k A),
  invDFT  (F) (A) = ∑_{k mod q} F(k) e_q(k A),
  invDFT (hatAlpha) = q · alpha.
```

There is **no** hidden `q^{1/2}`: the whole normalisation sits in the single
factor `q` of `invDFT_dftHat`.

## The one-factor completion (§6 of the source request)

For a unit `w = B·π` mod `q`,

```
  ∑_A alpha(A) Δ_q(A·B·π)
      = (1/q) ∑_k hatAlpha(k) [ e_q(−2 k (Bπ)⁻¹) − c_q(k)/φ(q) ],
```

and the `k = 0` coefficient of the bracket is exactly zero.

## Contents

* §1 the DFT convention, Fourier inversion in both directions;
* §2 unit invariance of the Ramanujan sum;
* §3 the twisted centred transform;
* §4 the **one-factor centred completion** and the vanishing of `k = 0`;
* §5 the prime case of the Ramanujan closed form (kernel-proved) and the
  general squarefree closed form, exposed as an *uninhabited* arithmetic
  interface (never assumed, never inhabited).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier
open TwinPrimeProject.CurrentProgramme.HStarCentered

variable {q : ℕ} [NeZero q]

/-! ## 1. The normalised DFT convention -/

/-- Multiplication by a unit is a bijection of `ZMod q`. -/
def unitMul (u : (ZMod q)ˣ) : ZMod q ≃ ZMod q where
  toFun n := (u : ZMod q) * n
  invFun n := ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * n
  left_inv n := by simp [← mul_assoc, ← Units.val_mul]
  right_inv n := by simp [← mul_assoc, ← Units.val_mul]

omit [NeZero q] in
@[simp] theorem unitMul_apply (u : (ZMod q)ˣ) (n : ZMod q) :
    unitMul u n = (u : ZMod q) * n := rfl

/-- **The DFT convention.**  `hatAlpha(k) = ∑_A alpha(A) e_q(−kA)`. -/
noncomputable def dftHat (q : ℕ) [NeZero q] (alpha : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  ∑ A : ZMod q, alpha A * eM q (-(k * A))

/-- **The unnormalised inverse transform.**  `invDFT(F)(A) = ∑_k F(k) e_q(kA)`. -/
noncomputable def invDFT (q : ℕ) [NeZero q] (F : ZMod q → ℂ) (A : ZMod q) : ℂ :=
  ∑ k : ZMod q, F k * eM q (k * A)

theorem cast_card_ne_zero (q : ℕ) [NeZero q] : ((q : ℂ)) ≠ 0 := by
  exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne'

/-- **Fourier inversion (unnormalised form).**  `invDFT (hatAlpha) = q · alpha`. -/
theorem invDFT_dftHat (alpha : ZMod q → ℂ) (A : ZMod q) :
    invDFT q (dftHat q alpha) A = (q : ℂ) * alpha A := by
  classical
  simp only [invDFT, dftHat, Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ B : ZMod q, (∑ k : ZMod q, alpha B * eM q (-(k * B)) * eM q (k * A))
      = alpha B * (if A - B = 0 then (q : ℂ) else 0) := by
    intro B
    have h1 : ∀ k : ZMod q,
        alpha B * eM q (-(k * B)) * eM q (k * A) = alpha B * eM q (k * (A - B)) := by
      intro k
      rw [mul_assoc, ← eM_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum, full_char_sum]
  rw [Finset.sum_congr rfl fun B _ => key B, Finset.sum_eq_single A]
  · simp [mul_comm]
  · intro b _ hb
    have : A - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Fourier inversion (normalised form).** -/
theorem fourier_inversion (alpha : ZMod q → ℂ) (A : ZMod q) :
    alpha A = (q : ℂ)⁻¹ * ∑ k : ZMod q, dftHat q alpha k * eM q (k * A) := by
  have h := invDFT_dftHat (q := q) alpha A
  rw [invDFT] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (cast_card_ne_zero q), one_mul]

/-- **The transform is onto.**  Every frequency vector `F` is the DFT of the
normalised inverse transform of `F`; in particular a DFT vector may have full
support. -/
theorem dftHat_invDFT (F : ZMod q → ℂ) (k : ZMod q) :
    dftHat q (fun A => (q : ℂ)⁻¹ * invDFT q F A) k = F k := by
  classical
  have hq := cast_card_ne_zero q
  simp only [dftHat, invDFT, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ j : ZMod q,
      (∑ A : ZMod q, (q : ℂ)⁻¹ * (F j * eM q (j * A)) * eM q (-(k * A)))
        = (q : ℂ)⁻¹ * (F j * (if j - k = 0 then (q : ℂ) else 0)) := by
    intro j
    have h1 : ∀ A : ZMod q,
        (q : ℂ)⁻¹ * (F j * eM q (j * A)) * eM q (-(k * A))
          = ((q : ℂ)⁻¹ * F j) * eM q (A * (j - k)) := by
      intro A
      have he : eM q (j * A) * eM q (-(k * A)) = eM q (A * (j - k)) := by
        rw [← eM_add]; congr 1; ring
      calc (q : ℂ)⁻¹ * (F j * eM q (j * A)) * eM q (-(k * A))
          = ((q : ℂ)⁻¹ * F j) * (eM q (j * A) * eM q (-(k * A))) := by ring
        _ = ((q : ℂ)⁻¹ * F j) * eM q (A * (j - k)) := by rw [he]
    rw [Finset.sum_congr rfl fun A _ => h1 A, ← Finset.mul_sum]
    rw [show (∑ A : ZMod q, eM q (A * (j - k))) = if j - k = 0 then (q : ℂ) else 0 from
      full_char_sum (j - k)]
    ring
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_eq_single k]
  · rw [sub_self, if_pos rfl]
    field_simp
  · intro b _ hb
    have : b - k ≠ 0 := sub_ne_zero.mpr hb
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## 2. Unit invariance of the Ramanujan sum -/

/-- `c_q(h v) = c_q(h)` for every unit `v`. -/
theorem ramanujanSum_unit_mul (h : ZMod q) (v : (ZMod q)ˣ) :
    ramanujanSum q (h * (v : ZMod q)) = ramanujanSum q h := by
  classical
  unfold ramanujanSum
  rw [← Equiv.sum_comp (Equiv.mulRight v⁻¹)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp [Units.val_mul, mul_comm, mul_left_comm]

/-- `c_q(−h) = c_q(h)`. -/
theorem ramanujanSum_neg (h : ZMod q) : ramanujanSum q (-h) = ramanujanSum q h := by
  have := ramanujanSum_unit_mul (q := q) h (-1)
  simpa using this

/-! ## 3. The twisted centred transform -/

/-- The **one-factor centred coefficient**
`e_q(−2 k w⁻¹) − c_q(k)/φ(q)`. -/
noncomputable def centeredOneFactorCoeff (q : ℕ) [NeZero q] (k : ZMod q) (w : (ZMod q)ˣ) : ℂ :=
  eM q (-2 * (k * ((w⁻¹ : (ZMod q)ˣ) : ZMod q))) - ramanujanSum q k / (q.totient : ℂ)

/-- The twisted centred transform: for a unit `w`,
`∑_A e_q(kA) Δ_q(A w) = e_q(−2 k w⁻¹) − c_q(k)/φ(q)`. -/
theorem centered_twisted_transform (k : ZMod q) (w : (ZMod q)ˣ) :
    (∑ A : ZMod q, eM q (k * A) * centeredProjector q (A * (w : ZMod q)))
      = centeredOneFactorCoeff q k w := by
  classical
  rw [← Equiv.sum_comp (unitMul w⁻¹)
      (fun A => eM q (k * A) * centeredProjector q (A * (w : ZMod q)))]
  have h1 : ∀ n : ZMod q,
      eM q (k * (unitMul w⁻¹ n)) * centeredProjector q ((unitMul w⁻¹ n) * (w : ZMod q))
        = centeredProjector q n * eM q ((k * ((w⁻¹ : (ZMod q)ˣ) : ZMod q)) * n) := by
    intro n
    have hcancel : ((w⁻¹ : (ZMod q)ˣ) : ZMod q) * n * (w : ZMod q) = n := by
      simp [mul_comm, mul_left_comm, ← Units.val_mul]
    simp only [unitMul_apply, hcancel]
    rw [mul_comm]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun n _ => h1 n]
  have hform := centeredFourier_eq_ramanujan_form q (k * ((w⁻¹ : (ZMod q)ˣ) : ZMod q))
  rw [show (∑ n : ZMod q, centeredProjector q n * eM q ((k * ((w⁻¹ : (ZMod q)ˣ) : ZMod q)) * n))
      = centeredFourier q (k * ((w⁻¹ : (ZMod q)ˣ) : ZMod q)) from rfl, hform,
    centeredOneFactorCoeff]
  congr 1
  · congr 1; ring
  · rw [show -(k * ((w⁻¹ : (ZMod q)ˣ) : ZMod q)) = k * ((-w⁻¹ : (ZMod q)ˣ) : ZMod q) by simp,
      ramanujanSum_unit_mul]

/-! ## 4. The one-factor centred completion -/

/-- **FM722-ONEFACTOR-CENTERED-COMPLETION45 (kernel form).**

For every finite `alpha` mod `q` and all units `B, π` mod `q`,

```
  ∑_A alpha(A) Δ_q(A·B·π)
     = (1/q) ∑_k hatAlpha(k) [ e_q(−2 k (Bπ)⁻¹) − c_q(k)/φ(q) ].
```
-/
theorem oneFactor_centered_completion (alpha : ZMod q → ℂ) (B pi : (ZMod q)ˣ) :
    (∑ A : ZMod q, alpha A * centeredProjector q (A * ((B * pi : (ZMod q)ˣ) : ZMod q)))
      = (q : ℂ)⁻¹ * ∑ k : ZMod q,
          dftHat q alpha k * centeredOneFactorCoeff q k (B * pi) := by
  classical
  set w : (ZMod q)ˣ := B * pi with hw
  have expand : ∀ A : ZMod q,
      alpha A * centeredProjector q (A * (w : ZMod q))
        = (q : ℂ)⁻¹ * ∑ k : ZMod q,
            dftHat q alpha k * (eM q (k * A) * centeredProjector q (A * (w : ZMod q))) := by
    intro A
    conv_lhs => rw [fourier_inversion alpha A]
    rw [mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun A _ => expand A, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, centered_twisted_transform]

/-- **The `k = 0` coefficient vanishes.**  This is the load-bearing centring
statement of the one-factor completion. -/
theorem centeredOneFactorCoeff_zero (w : (ZMod q)ˣ) :
    centeredOneFactorCoeff q 0 w = 0 := by
  simp only [centeredOneFactorCoeff, zero_mul, mul_zero, eM_zero, ramanujanSum_zero]
  rw [div_self (totient_cast_ne_zero q), sub_self]

/-- Consequently the `k = 0` term of the completed one-factor sum is zero. -/
theorem oneFactor_zero_frequency_term (alpha : ZMod q → ℂ) (w : (ZMod q)ˣ) :
    dftHat q alpha 0 * centeredOneFactorCoeff q 0 w = 0 := by
  rw [centeredOneFactorCoeff_zero, mul_zero]

/-! ## 5. The Ramanujan closed form -/

/-- **Prime case of the Ramanujan closed form, kernel-proved.**  For `q = p`
prime and `k ≠ 0`, `c_p(k) = −1`; this is the value `μ(p)/φ(p) · φ(p)` of the
closed form at `(p,k) = 1`. -/
theorem ramanujanSum_prime_nonzero {p : ℕ} [Fact p.Prime] (k : ZMod p) (hk : k ≠ 0) :
    ramanujanSum p k = -1 := by
  classical
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hall : ∑ a : ZMod p, eM p (-(k * a)) = 0 := by
    have h := full_char_sum (M := p) (-k)
    rw [if_neg (neg_ne_zero.mpr hk)] at h
    rw [← h]
    exact Finset.sum_congr rfl fun a _ => by congr 1; ring
  have hunits : ∑ a : (ZMod p)ˣ, eM p (-(k * (a : ZMod p)))
      = ∑ a : {x : ZMod p // x ≠ 0}, eM p (-(k * (a : ZMod p))) := by
    simpa using (Equiv.sum_comp (unitsEquivNeZero (G₀ := ZMod p))
      (fun x : {x : ZMod p // x ≠ 0} => eM p (-(k * (x : ZMod p)))))
  have hsub : ∑ a ∈ Finset.univ.erase (0 : ZMod p), eM p (-(k * a))
      = ∑ a : {x : ZMod p // x ≠ 0}, eM p (-(k * (a : ZMod p))) := by
    refine Finset.sum_subtype _ (fun x => ?_) _
    simp [Finset.mem_erase]
  rw [ramanujanSum, hunits, ← hsub, Finset.sum_erase_eq_sub (Finset.mem_univ (0 : ZMod p)), hall]
  simp

/-- **Arithmetic closed form of the centred Ramanujan coefficient (INTERFACE).**

`c_q(k)/φ(q) = μ(q/(q,k))/φ(q/(q,k))` on the squarefree sector.  This module
proves the *finite-character* half of §7 of the request (unit invariance,
`c_q(0) = φ(q)`, the prime evaluation).  The general arithmetic closed form is
exposed here as a structure and is **never inhabited, never assumed and never
used as an axiom**. -/
structure RamanujanSquarefreeClosedForm : Prop where
  /-- Hölder's closed form on the squarefree sector:
  `c_q(k)/φ(q) = μ(q/(q,k))/φ(q/(q,k))`. -/
  closed_form :
    ∀ (q : ℕ) [NeZero q], Squarefree q → ∀ k : ℕ,
      ramanujanSum q ((k : ℕ) : ZMod q) / (q.totient : ℂ)
        = ((ArithmeticFunction.moebius (q / Nat.gcd q k) : ℤ) : ℂ)
            / ((Nat.totient (q / Nat.gcd q k) : ℂ))

end FM722
end CurrentProgramme
end TwinPrimeProject
