/-
# Gate1B / R11 / Frontier / Latest : the affine character Gram identity and its `√ℓ` norm

Append-only module.  **Exact finite algebra only.**

The source-side affine character estimate of the current frontier rests on one deterministic
fact: the affine character matrix

```
V[a, x] = e( a x / ℓ ),        a, x  <  ℓ
```

satisfies the exact Gram identity `V* V = ℓ · I`, hence is `√ℓ` times an isometry.  Everything in
this module is that identity and its consequences; no analytic estimate is claimed.

* §1 the additive character `ee ℓ k = e(k/ℓ)` and its exact algebra;
* §2 complete-sum orthogonality `∑_{x<ℓ} e(kx/ℓ) = ℓ·1_{ℓ | k}`;
* §3 the **Gram identity** `∑_{x<ℓ} V[a,x] conj V[b,x] = ℓ·1_{ℓ | a-b}`;
* §4 **Parseval / operator norm**: `∑_{a<ℓ} |(Vf)(a)|² = ℓ ∑_{x<ℓ} |f(x)|²`, i.e. `‖V‖ = √ℓ`.
-/
import Mathlib

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. The additive character -/

/-- The additive character `e(k/ℓ) = exp(2πi k/ℓ)`. -/
noncomputable def ee (l : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (l : ℂ))

theorem ee_add (l : ℕ) (k₁ k₂ : ℤ) : ee l (k₁ + k₂) = ee l k₁ * ee l k₂ := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_zero (l : ℕ) : ee l 0 = 1 := by simp [ee]

theorem ee_pow (l : ℕ) (k : ℤ) (x : ℕ) : ee l k ^ x = ee l (k * x) := by
  induction x with
  | zero => simp [ee_zero]
  | succ n ih =>
      rw [pow_succ, ih, ← ee_add]
      congr 1
      push_cast
      ring

theorem ee_conj (l : ℕ) (k : ℤ) : (starRingEnd ℂ) (ee l k) = ee l (-k) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, map_intCast, map_natCast, Complex.conj_I, map_ofNat,
    Complex.conj_ofReal]
  push_cast
  ring

/-- The character is trivial exactly on the multiples of `ℓ` (`ℓ > 0`). -/
theorem ee_eq_one_of_dvd {l : ℕ} (hl : 0 < l) {k : ℤ} (h : (l : ℤ) ∣ k) : ee l k = 1 := by
  obtain ⟨m, rfl⟩ := h
  unfold ee
  have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
  have hrw : 2 * (Real.pi : ℂ) * Complex.I * (((l : ℤ) * m : ℤ) : ℂ) / (l : ℂ)
      = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [hrw, Complex.exp_int_mul_two_pi_mul_I]

theorem ee_ne_one_of_not_dvd {l : ℕ} (hl : 0 < l) {k : ℤ} (h : ¬ (l : ℤ) ∣ k) : ee l k ≠ 1 := by
  intro hc
  unfold ee at hc
  rw [Complex.exp_eq_one_iff] at hc
  obtain ⟨n, hn⟩ := hc
  have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp at hn
  have hkl : k = l * n := by exact_mod_cast hn
  exact h ⟨n, hkl⟩

/-! ## 2. Complete-sum orthogonality -/

/-- **Orthogonality.**  A complete additive character sum is `ℓ` on the trivial character and `0`
otherwise. -/
theorem sum_ee_complete {l : ℕ} (hl : 0 < l) (k : ℤ) :
    ∑ x ∈ range l, ee l (k * x) = if (l : ℤ) ∣ k then (l : ℂ) else 0 := by
  by_cases h : (l : ℤ) ∣ k
  · rw [if_pos h]
    have : ∀ x ∈ range l, ee l (k * x) = 1 := by
      intro x _
      exact ee_eq_one_of_dvd hl (Dvd.dvd.mul_right h _)
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    have hne : ee l k ≠ 1 := ee_ne_one_of_not_dvd hl h
    have hgeom : ∑ x ∈ range l, ee l k ^ x = (ee l k ^ l - 1) / (ee l k - 1) :=
      geom_sum_eq hne l
    have hpow : ee l k ^ l = 1 := by
      rw [ee_pow]
      exact ee_eq_one_of_dvd hl ⟨k, by ring⟩
    calc ∑ x ∈ range l, ee l (k * x) = ∑ x ∈ range l, ee l k ^ x := by
          exact Finset.sum_congr rfl fun x _ => (ee_pow l k x).symm
      _ = (ee l k ^ l - 1) / (ee l k - 1) := hgeom
      _ = 0 := by rw [hpow]; simp

/-! ## 3. The Gram identity -/

/-- The affine character matrix `V[a,x] = e(ax/ℓ)`. -/
noncomputable def affineMat (l : ℕ) (a x : ℕ) : ℂ := ee l ((a : ℤ) * (x : ℤ))

/-- **Affine character Gram identity**: `V* V = ℓ I`, i.e. distinct rows are orthogonal and each
row has squared norm exactly `ℓ`. -/
theorem affine_gram {l : ℕ} (hl : 0 < l) (a b : ℕ) :
    ∑ x ∈ range l, affineMat l a x * (starRingEnd ℂ) (affineMat l b x)
      = if (l : ℤ) ∣ ((a : ℤ) - b) then (l : ℂ) else 0 := by
  have : ∀ x ∈ range l, affineMat l a x * (starRingEnd ℂ) (affineMat l b x)
      = ee l (((a : ℤ) - b) * x) := by
    intro x _
    unfold affineMat
    rw [ee_conj, ← ee_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl this, sum_ee_complete hl]

/-- Diagonal case of the Gram identity: each affine row has squared norm exactly `ℓ`. -/
theorem affine_gram_diag {l : ℕ} (hl : 0 < l) (a : ℕ) :
    ∑ x ∈ range l, affineMat l a x * (starRingEnd ℂ) (affineMat l a x) = (l : ℂ) := by
  rw [affine_gram hl a a]
  simp

/-! ## 4. Parseval and the `√ℓ` operator norm -/

/-- The affine character transform. -/
noncomputable def affineTransform (l : ℕ) (f : ℕ → ℂ) (a : ℕ) : ℂ :=
  ∑ x ∈ range l, f x * affineMat l a x

/-- **Parseval for the affine character matrix**: the transform is exactly `√ℓ` times an
isometry.  This is the deterministic content of the `√ℓ` operator norm. -/
theorem affine_parseval {l : ℕ} (hl : 0 < l) (f : ℕ → ℂ) :
    ∑ a ∈ range l, ‖affineTransform l f a‖ ^ 2 = (l : ℝ) * ∑ x ∈ range l, ‖f x‖ ^ 2 := by
  have key : ∀ a : ℕ, ((‖affineTransform l f a‖ ^ 2 : ℝ) : ℂ)
      = ∑ x ∈ range l, ∑ y ∈ range l,
          f x * (starRingEnd ℂ) (f y) * ee l (((x : ℤ) - y) * a) := by
    intro a
    have hnorm : ((‖affineTransform l f a‖ ^ 2 : ℝ) : ℂ)
        = affineTransform l f a * (starRingEnd ℂ) (affineTransform l f a) := by
      rw [Complex.mul_conj']; push_cast; ring
    rw [hnorm]
    unfold affineTransform
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    unfold affineMat
    rw [map_mul, ee_conj]
    have hprod : ee l ((a : ℤ) * x) * ee l (-((a : ℤ) * y)) = ee l (((x : ℤ) - y) * a) := by
      rw [← ee_add]; congr 1; ring
    calc f x * ee l ((a : ℤ) * x) * ((starRingEnd ℂ) (f y) * ee l (-((a : ℤ) * y)))
        = f x * (starRingEnd ℂ) (f y) * (ee l ((a : ℤ) * x) * ee l (-((a : ℤ) * y))) := by ring
      _ = f x * (starRingEnd ℂ) (f y) * ee l (((x : ℤ) - y) * a) := by rw [hprod]
  have step : ∀ x ∈ range l, ∑ a ∈ range l, ∑ y ∈ range l,
      f x * (starRingEnd ℂ) (f y) * ee l (((x : ℤ) - y) * a)
      = (l : ℂ) * (f x * (starRingEnd ℂ) (f x)) := by
    intro x hx
    rw [Finset.sum_comm]
    have inner : ∀ y ∈ range l, ∑ a ∈ range l,
        f x * (starRingEnd ℂ) (f y) * ee l (((x : ℤ) - y) * a)
        = if y = x then (l : ℂ) * (f x * (starRingEnd ℂ) (f x)) else 0 := by
      intro y hy
      rw [← Finset.mul_sum, sum_ee_complete hl]
      by_cases hxy : y = x
      · subst hxy; simp [mul_comm]
      · rw [if_neg, mul_zero, if_neg hxy]
        intro hdvd
        have hx' : x < l := mem_range.mp hx
        have hy' : y < l := mem_range.mp hy
        have h1 : |(x : ℤ) - y| < l := by rw [abs_lt]; omega
        have := Int.eq_zero_of_abs_lt_dvd hdvd h1
        exact hxy (by omega)
    rw [Finset.sum_congr rfl inner, Finset.sum_ite_eq' (range l) x
      (fun _ => (l : ℂ) * (f x * (starRingEnd ℂ) (f x))), if_pos hx]
  have hsum : ((∑ a ∈ range l, ‖affineTransform l f a‖ ^ 2 : ℝ) : ℂ)
      = (((l : ℝ) * ∑ x ∈ range l, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun a _ => key a), Finset.sum_comm,
      Finset.sum_congr rfl step, ← Finset.mul_sum]
    push_cast
    refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
    rw [Complex.mul_conj']
  exact_mod_cast hsum

end Gate1B.R11.Frontier.Latest
