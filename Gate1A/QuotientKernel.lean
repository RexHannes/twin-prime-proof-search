/-
# Gate-1A: the exact finite quotient kernel (Section 6)

`C = p q r`, `N = p r`, `I_j = j N + [0, N)`.  The finite Fourier coefficient is

```
β_j(h) = (1/C) ∑_{s ∈ I_j} e_C(-h s).
```

The centred kernel removes the `h ≡ 0 (mod C)` mode.  We prove:

* `quotient_kernel_zero_mode`  : `β_j°(0) = 0` (the `h = 0` firewall);
* `quotient_kernel_exact_nonzero` : the exact geometric-series formula for
  `h` not divisible by `C`.

All endpoints, representatives and the denominator nonvanishing are explicit.
-/
import Mathlib

namespace Gate1A

open Finset

namespace QuotientKernel

/-- `E t = exp(2πi t)`. -/
noncomputable def E (t : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

theorem E_add (s t : ℂ) : E (s + t) = E s * E t := by
  simp only [E, mul_add, Complex.exp_add]

theorem E_zero : E 0 = 1 := by simp [E]

theorem E_pow (t : ℂ) (n : ℕ) : E t ^ n = E ((n : ℂ) * t) := by
  simp only [E, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- `E t = 1` exactly on the integers. -/
theorem E_eq_one_iff (t : ℂ) : E t = 1 ↔ ∃ n : ℤ, t = (n : ℂ) := by
  rw [E, Complex.exp_eq_one_iff]
  have hne : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) * t
        = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by linear_combination hn
    exact mul_left_cancel₀ hne h2
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem E_int (n : ℤ) : E ((n : ℂ)) = 1 := (E_eq_one_iff _).mpr ⟨n, rfl⟩

/-- The finite Fourier coefficient of the `j`-th interval `I_j = jN + [0,N)`. -/
noncomputable def betaKernel (p q r : ℕ) (j h : ℤ) : ℂ :=
  (1 / ((p * q * r : ℕ) : ℂ)) *
    ∑ a ∈ Finset.range (p * r),
      E (-((h : ℂ) * ((j : ℂ) * ((p * r : ℕ) : ℂ) + (a : ℂ))) / ((p * q * r : ℕ) : ℂ))

/-- The centred kernel: the `h ≡ 0 (mod C)` Fourier mode is removed. -/
noncomputable def betaCentered (p q r : ℕ) (j h : ℤ) : ℂ :=
  betaKernel p q r j h -
    (if ((p * q * r : ℕ) : ℤ) ∣ h then ((p * r : ℕ) : ℂ) / ((p * q * r : ℕ) : ℂ) else 0)

variable (p q r : ℕ)

/-- On the `C`-divisible modes the uncentred kernel is exactly `N/C`. -/
theorem betaKernel_of_dvd (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (j h : ℤ)
    (hh : ((p * q * r : ℕ) : ℤ) ∣ h) :
    betaKernel p q r j h = ((p * r : ℕ) : ℂ) / ((p * q * r : ℕ) : ℂ) := by
  obtain ⟨k, rfl⟩ := hh
  have hCpos : (0 : ℕ) < p * q * r := by positivity
  have hC : ((p * q * r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hterm : ∀ a ∈ Finset.range (p * r),
      E (-(((((p * q * r : ℕ) : ℤ) * k : ℤ) : ℂ) *
          ((j : ℂ) * ((p * r : ℕ) : ℂ) + (a : ℂ))) / ((p * q * r : ℕ) : ℂ)) = 1 := by
    intro a _
    have hexp : (-(((((p * q * r : ℕ) : ℤ) * k : ℤ) : ℂ) *
        ((j : ℂ) * ((p * r : ℕ) : ℂ) + (a : ℂ))))
        = ((p * q * r : ℕ) : ℂ) *
            (-((k : ℂ) * ((j : ℂ) * ((p * r : ℕ) : ℂ) + (a : ℂ)))) := by
      push_cast; ring
    rw [hexp, mul_div_cancel_left₀ _ hC,
      show (-((k : ℂ) * ((j : ℂ) * ((p * r : ℕ) : ℂ) + (a : ℂ))))
        = (((-(k * ((j : ℤ) * ((p * r : ℕ) : ℤ) + (a : ℤ)))) : ℤ) : ℂ) by push_cast; ring,
      E_int]
  rw [betaKernel, Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  ring

/-- **`quotient_kernel_zero_mode`** — the `h = 0` firewall. -/
theorem quotient_kernel_zero_mode (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (j : ℤ) :
    betaCentered p q r j 0 = 0 := by
  rw [betaCentered, if_pos (dvd_zero _), betaKernel_of_dvd p q r hp hq hr j 0 (dvd_zero _)]
  ring

/-- **`quotient_kernel_exact_nonzero`** — the exact geometric-series formula.

For `h` not divisible by `C = p q r`,

```
β_j°(h) = e_q(-jh) · (1 - e_q(-h)) / ( p q r · (1 - e_{pqr}(-h)) ).
```
-/
theorem quotient_kernel_exact_nonzero (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (j h : ℤ) (hh : ¬ ((p * q * r : ℕ) : ℤ) ∣ h) :
    betaCentered p q r j h
      = E (-((j : ℂ) * (h : ℂ)) / (q : ℂ)) *
          (1 - E (-(h : ℂ) / (q : ℂ))) /
          (((p * q * r : ℕ) : ℂ) * (1 - E (-(h : ℂ) / ((p * q * r : ℕ) : ℂ)))) := by
  have hCpos : (0 : ℕ) < p * q * r := by positivity
  have hC : ((p * q * r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hqC : ((q : ℂ)) ≠ 0 := by exact_mod_cast hq.ne'
  -- the ratio N/C is exactly 1/q
  have hNC : ((p * r : ℕ) : ℂ) / ((p * q * r : ℕ) : ℂ) = 1 / (q : ℂ) := by
    rw [div_eq_div_iff hC hqC]
    push_cast; ring
  set z : ℂ := E (-(h : ℂ) / ((p * q * r : ℕ) : ℂ)) with hz
  have hzne : z ≠ 1 := by
    rw [hz, Ne, E_eq_one_iff]
    rintro ⟨n, hn⟩
    apply hh
    refine ⟨-n, ?_⟩
    have h1 : -(h : ℂ) = (n : ℂ) * ((p * q * r : ℕ) : ℂ) := by
      field_simp at hn
      linear_combination hn
    have h2 : ((h : ℤ) : ℂ) = ((((p * q * r : ℕ) : ℤ) * (-n) : ℤ) : ℂ) := by
      push_cast
      push_cast at h1
      linear_combination -h1
    exact_mod_cast h2
  have hterm : ∀ a ∈ Finset.range (p * r),
      E (-((h : ℂ) * ((j : ℂ) * ((p * r : ℕ) : ℂ) + (a : ℂ))) / ((p * q * r : ℕ) : ℂ))
        = E (-((j : ℂ) * (h : ℂ)) / (q : ℂ)) * z ^ a := by
    intro a _
    rw [hz, E_pow, ← E_add]
    congr 1
    have hsplit : -((h : ℂ) * ((j : ℂ) * ((p * r : ℕ) : ℂ) + (a : ℂ))) /
        ((p * q * r : ℕ) : ℂ)
        = (-(j : ℂ) * (h : ℂ)) * (((p * r : ℕ) : ℂ) / ((p * q * r : ℕ) : ℂ))
          + (a : ℂ) * (-(h : ℂ) / ((p * q * r : ℕ) : ℂ)) := by
      field_simp
      ring
    rw [hsplit, hNC]
    ring
  have hzN : z ^ (p * r) = E (-(h : ℂ) / (q : ℂ)) := by
    rw [hz, E_pow]
    congr 1
    rw [show ((p * r : ℕ) : ℂ) * (-(h : ℂ) / ((p * q * r : ℕ) : ℂ))
        = (-(h : ℂ)) * (((p * r : ℕ) : ℂ) / ((p * q * r : ℕ) : ℂ)) by ring, hNC]
    ring
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hzne
  have hz2 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzne)
  rw [betaCentered, if_neg hh, sub_zero, betaKernel, Finset.sum_congr rfl hterm,
    ← Finset.mul_sum, geom_sum_eq hzne, hzN]
  field_simp
  ring

end QuotientKernel

end Gate1A
