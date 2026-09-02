/-
# Universal / D0WP — additive character core

**Status of this module: KERNEL_PROVED elementary algebra.**

This module contains only elementary, machine-checked facts about the additive
character

```
e_n(x) = exp(2 π i x / n),   n : ℕ,  x : ℤ.
```

Nothing analytic is asserted here: no estimate, no cancellation, no external
theorem.  The results are periodicity, the vanishing criterion, the exact
scaling law `e_{s r}(s x) = e_r(x)` used by the effective-modulus reduction, and
the exact finite orthogonality sum used by the finite Fourier matrix.
-/
import Mathlib

namespace Universal.D0WP

open Finset

noncomputable section

/-- The additive character `e_n(x) = exp(2 π i x / n)`.  For `n = 0` this is the
constant `1`, which is harmless: every statement below assumes `n ≠ 0`. -/
def ac (n : ℕ) (x : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) / (n : ℂ))

@[simp] theorem ac_zero (n : ℕ) : ac n 0 = 1 := by
  simp [ac]

theorem ac_add (n : ℕ) (x y : ℤ) : ac n (x + y) = ac n x * ac n y := by
  unfold ac
  rw [← Complex.exp_add]
  push_cast
  ring_nf

theorem ac_eq_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℤ) : ac n x = 1 ↔ (n : ℤ) ∣ x := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  constructor
  · intro h
    rw [ac, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    field_simp at hk
    exact ⟨k, by exact_mod_cast hk⟩
  · rintro ⟨k, rfl⟩
    rw [ac, Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    push_cast
    field_simp

/-- Periodicity: the character only sees the residue class modulo `n`. -/
theorem ac_congr {n : ℕ} (hn : n ≠ 0) {x y : ℤ} (h : x ≡ y [ZMOD (n : ℤ)]) :
    ac n x = ac n y := by
  obtain ⟨k, hk⟩ : (n : ℤ) ∣ y - x := Int.ModEq.dvd h
  have hy : y = x + (n : ℤ) * k := by omega
  rw [hy, ac_add, (ac_eq_one_iff hn _).2 ⟨k, rfl⟩, mul_one]

/-- **Exact scaling law.**  Cancelling a common factor `s` from the modulus and
the numerator does not change the character. -/
theorem ac_scale {s r : ℕ} (hs : s ≠ 0) (x : ℤ) :
    ac (s * r) ((s : ℤ) * x) = ac r x := by
  have hs0 : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs
  unfold ac
  congr 1
  push_cast
  by_cases hr : (r : ℂ) = 0
  · simp [hr]
  · field_simp

theorem ac_pow (n : ℕ) (c : ℤ) (v : ℕ) : (ac n c) ^ v = ac n (c * v) := by
  unfold ac
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem ac_neg (n : ℕ) (x : ℤ) : ac n (-x) = (ac n x)⁻¹ := by
  have h := ac_add n x (-x)
  simp only [add_neg_cancel, ac_zero] at h
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)

theorem ac_conj (n : ℕ) (x : ℤ) : (starRingEnd ℂ) (ac n x) = ac n (-x) := by
  unfold ac
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp [map_div₀, Complex.conj_I, map_ofNat]

theorem ac_norm (n : ℕ) (x : ℤ) : ‖ac n x‖ = 1 := by
  unfold ac
  rw [Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) / (n : ℂ)).re = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq]
  rw [h, Real.exp_zero]

theorem ac_ne_zero (n : ℕ) (x : ℤ) : ac n x ≠ 0 := by
  intro h
  have := ac_norm n x
  rw [h] at this
  simp at this

/-- **Exact finite orthogonality.**  The complete additive sum is `n` when the
frequency vanishes modulo `n`, and `0` otherwise. -/
theorem sum_ac_range {n : ℕ} (hn : n ≠ 0) (c : ℤ) :
    ∑ v ∈ range n, ac n (c * v) = if (n : ℤ) ∣ c then (n : ℂ) else 0 := by
  have hrw : ∀ v ∈ range n, ac n (c * v) = (ac n c) ^ v := by
    intro v _
    rw [ac_pow]
  rw [Finset.sum_congr rfl hrw]
  by_cases hd : (n : ℤ) ∣ c
  · simp [(ac_eq_one_iff hn c).2 hd, hd]
  · have hne : ac n c ≠ 1 := fun h => hd ((ac_eq_one_iff hn c).1 h)
    have hpow : (ac n c) ^ n = 1 := by
      rw [ac_pow, (ac_eq_one_iff hn _).2 ⟨c, by ring⟩]
    rw [geom_sum_eq hne, hpow]
    simp [hd]

end

end Universal.D0WP
