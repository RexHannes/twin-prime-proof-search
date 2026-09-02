/-
# Universal / D0WP — the finite Fourier matrix and its exact operator norm

**Status of this module: KERNEL_PROVED elementary algebra.**

The inner `d0 · wp` provider uses the *unnormalised finite Fourier kernel*

```
K(u, v) = e_{rSharp}(- ASharp * u * v)
```

on the full additive residue system modulo `rSharp` (units are zero-extended:
nothing below assumes `u` or `v` invertible).  We prove directly, by the exact
additive orthogonality of `Universal.D0WP.ac`, that

```
K Kᴴ = rSharp • I,
```

and we prove the only consequence that is actually used downstream, namely the
bilinear bound with constant `sqrt rSharp`:

```
‖∑_{u,v} X u * K u v * Y v‖ ≤ sqrt rSharp * ‖X‖₂ * ‖Y‖₂.
```

This is *not* presented as a multiplicative-character theorem: no Gauss sum,
Weil bound or Dirichlet character occurs.  The only hypotheses are `rSharp ≠ 0`
and `gcd(ASharp, rSharp) = 1`, which the effective-modulus module supplies.
-/
import Universal.D0WP.EffectiveModulus

namespace Universal.D0WP

open Finset

noncomputable section

/-- The unnormalised finite Fourier kernel `K(u,v) = e_n(-A u v)`. -/
def Kker (A n : ℕ) (u v : ℕ) : ℂ := ac n (-(A : ℤ) * u * v)

theorem Kker_symm (A n u v : ℕ) : Kker A n u v = Kker A n v u := by
  unfold Kker
  ring_nf

theorem Kker_norm (A n u v : ℕ) : ‖Kker A n u v‖ = 1 := ac_norm _ _

/-- **Row orthogonality (exact).** -/
theorem Kker_row_orth {A n : ℕ} (hn : n ≠ 0) (hA : Nat.Coprime A n) (i i' : Fin n) :
    ∑ j : Fin n, Kker A n i j * (starRingEnd ℂ) (Kker A n i' j)
      = if i = i' then (n : ℂ) else 0 := by
  have key : ∀ j : Fin n, Kker A n i j * (starRingEnd ℂ) (Kker A n i' j)
      = ac n (((A : ℤ) * ((i' : ℕ) - (i : ℕ))) * (j : ℕ)) := by
    intro j
    unfold Kker
    rw [ac_conj, ← ac_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  rw [Fin.sum_univ_eq_sum_range (fun j => ac n (((A : ℤ) * ((i' : ℕ) - (i : ℕ))) * (j : ℕ))) n]
  rw [sum_ac_range hn]
  by_cases h : i = i'
  · subst h; simp
  · have hne : ¬ ((n : ℤ) ∣ (A : ℤ) * ((i' : ℕ) - (i : ℕ))) := by
      intro hdvd
      have hcop : IsCoprime (n : ℤ) (A : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        simpa [Nat.gcd_comm] using hA
      have h2 : (n : ℤ) ∣ ((i' : ℕ) - (i : ℕ) : ℤ) := hcop.dvd_of_dvd_mul_left hdvd
      have hi : (i : ℕ) < n := i.isLt
      have hi' : (i' : ℕ) < n := i'.isLt
      have := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
      exact h (Fin.ext (by omega))
    simp [hne, h]

/-- **Column orthogonality (exact).**  Immediate from row orthogonality, since
the kernel is symmetric. -/
theorem Kker_col_orth {A n : ℕ} (hn : n ≠ 0) (hA : Nat.Coprime A n) (v w : Fin n) :
    ∑ u : Fin n, Kker A n u v * (starRingEnd ℂ) (Kker A n u w)
      = if v = w then (n : ℂ) else 0 := by
  have : ∀ u : Fin n, Kker A n u v * (starRingEnd ℂ) (Kker A n u w)
      = Kker A n v u * (starRingEnd ℂ) (Kker A n w u) := by
    intro u
    rw [Kker_symm A n u v, Kker_symm A n u w]
  rw [Finset.sum_congr rfl (fun u _ => this u), Kker_row_orth hn hA]

/-- The finite Fourier matrix. -/
def Kmat (A n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i j => Kker A n i j

/-- **`K Kᴴ = n • I` (kernel-proved).**  The full unnormalised finite Fourier
matrix on the complete residue system is `sqrt n` times a unitary. -/
theorem Kmat_mul_conjTranspose {A n : ℕ} (hn : n ≠ 0) (hA : Nat.Coprime A n) :
    Kmat A n * (Kmat A n).conjTranspose = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i k
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin n,
      Kmat A n i j * (Kmat A n).conjTranspose j k
        = Kker A n i j * (starRingEnd ℂ) (Kker A n k j) := fun _ => rfl
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Kker_row_orth hn hA]
  by_cases h : i = k <;> simp [h]

/-- The finite Fourier transform attached to the kernel. -/
def Ktrans (A n : ℕ) (Y : Fin n → ℂ) (u : Fin n) : ℂ :=
  ∑ v : Fin n, Kker A n u v * Y v

/-- **Exact Parseval / `ℓ²` identity for the unnormalised transform.** -/
theorem Ktrans_l2 {A n : ℕ} (hn : n ≠ 0) (hA : Nat.Coprime A n) (Y : Fin n → ℂ) :
    ∑ u : Fin n, ‖Ktrans A n Y u‖ ^ 2 = n * ∑ v : Fin n, ‖Y v‖ ^ 2 := by
  have hc : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj']
    push_cast
    ring
  have main : ∑ u : Fin n, Ktrans A n Y u * (starRingEnd ℂ) (Ktrans A n Y u)
      = (n : ℂ) * ∑ v : Fin n, Y v * (starRingEnd ℂ) (Y v) := by
    have e1 : ∀ u : Fin n, Ktrans A n Y u * (starRingEnd ℂ) (Ktrans A n Y u)
        = ∑ v : Fin n, ∑ w : Fin n,
            (Kker A n u v * (starRingEnd ℂ) (Kker A n u w)) * (Y v * (starRingEnd ℂ) (Y w)) := by
      intro u
      unfold Ktrans
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
      simp only [map_mul]
      ring
    rw [Finset.sum_congr rfl (fun u _ => e1 u), Finset.sum_comm]
    have step : ∀ v : Fin n, ∑ u : Fin n, ∑ w : Fin n,
        (Kker A n u v * (starRingEnd ℂ) (Kker A n u w)) * (Y v * (starRingEnd ℂ) (Y w))
        = (n : ℂ) * (Y v * (starRingEnd ℂ) (Y v)) := by
      intro v
      rw [Finset.sum_comm]
      have inner : ∀ w : Fin n, ∑ u : Fin n,
          (Kker A n u v * (starRingEnd ℂ) (Kker A n u w)) * (Y v * (starRingEnd ℂ) (Y w))
          = (if v = w then (n : ℂ) else 0) * (Y v * (starRingEnd ℂ) (Y w)) := by
        intro w
        rw [← Finset.sum_mul, Kker_col_orth hn hA]
      rw [Finset.sum_congr rfl (fun w _ => inner w)]
      simp
    rw [Finset.sum_congr rfl (fun v _ => step v), Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hc (Ktrans A n Y u)),
      Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => hc (Y v))] at main
  exact_mod_cast main

/-- **Operator norm `sqrt n`, in the bilinear form actually used.**

For arbitrary `X, Y` (zero-extended from the units if desired),

```
‖∑_{u,v} X u * K u v * Y v‖ ≤ sqrt n * sqrt (∑ ‖X‖²) * sqrt (∑ ‖Y‖²).
```
-/
theorem Kker_bilinear_bound {A n : ℕ} (hn : n ≠ 0) (hA : Nat.Coprime A n)
    (X Y : Fin n → ℂ) :
    ‖∑ u : Fin n, ∑ v : Fin n, X u * Kker A n u v * Y v‖
      ≤ Real.sqrt n * Real.sqrt (∑ u : Fin n, ‖X u‖ ^ 2)
          * Real.sqrt (∑ v : Fin n, ‖Y v‖ ^ 2) := by
  have hrw : ∑ u : Fin n, ∑ v : Fin n, X u * Kker A n u v * Y v
      = ∑ u : Fin n, X u * Ktrans A n Y u := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    unfold Ktrans
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hrw]
  have step1 : ‖∑ u : Fin n, X u * Ktrans A n Y u‖
      ≤ ∑ u : Fin n, ‖X u‖ * ‖Ktrans A n Y u‖ := by
    refine (norm_sum_le _ _).trans_eq ?_
    exact Finset.sum_congr rfl (fun u _ => norm_mul _ _)
  have step2 : ∑ u : Fin n, ‖X u‖ * ‖Ktrans A n Y u‖
      ≤ Real.sqrt (∑ u : Fin n, ‖X u‖ ^ 2)
          * Real.sqrt (∑ u : Fin n, ‖Ktrans A n Y u‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have step3 : Real.sqrt (∑ u : Fin n, ‖Ktrans A n Y u‖ ^ 2)
      = Real.sqrt n * Real.sqrt (∑ v : Fin n, ‖Y v‖ ^ 2) := by
    rw [Ktrans_l2 hn hA, Real.sqrt_mul (by positivity)]
  calc ‖∑ u : Fin n, X u * Ktrans A n Y u‖
      ≤ ∑ u : Fin n, ‖X u‖ * ‖Ktrans A n Y u‖ := step1
    _ ≤ Real.sqrt (∑ u : Fin n, ‖X u‖ ^ 2)
          * Real.sqrt (∑ u : Fin n, ‖Ktrans A n Y u‖ ^ 2) := step2
    _ = Real.sqrt n * Real.sqrt (∑ u : Fin n, ‖X u‖ ^ 2)
          * Real.sqrt (∑ v : Fin n, ‖Y v‖ ^ 2) := by rw [step3]; ring

end

end Universal.D0WP
