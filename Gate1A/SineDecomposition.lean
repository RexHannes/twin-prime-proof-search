/-
# Gate-1A: the exact sine decomposition and its quadratic amplitude error
(Section 7)

`sine_ratio_exact` is an **exact** complex identity: the linear phase is
retained exactly, and only the sine *amplitude* ratio is later approximated.

`sine_ratio_quadratic_error` is a rigorous calculus inequality showing that
the amplitude ratio `sin(Nu)/(N sin u)` differs from `1` by `O((Nu)²)` —
quadratic, not linear.  The constant is explicit (namely `1`).
-/
import Mathlib

namespace Gate1A

namespace SineDecomposition

open Complex in
/-- `2 i sin z = e^{iz} − e^{−iz}`. -/
theorem two_I_sin (z : ℂ) :
    2 * Complex.I * Complex.sin z
      = Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [Complex.sin, show -z * Complex.I = -(z * Complex.I) by ring]
  linear_combination (Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)) * hI

/-- `1 − e^{−2ix} = e^{−ix} · 2i sin x`. -/
theorem one_sub_exp (x : ℂ) :
    1 - Complex.exp (-(2 * x * Complex.I))
      = Complex.exp (-(x * Complex.I)) * (2 * Complex.I * Complex.sin x) := by
  rw [two_I_sin, mul_sub, ← Complex.exp_add, ← Complex.exp_add,
    show -(x * Complex.I) + x * Complex.I = 0 by ring, Complex.exp_zero,
    show -(x * Complex.I) + -(x * Complex.I) = -(2 * x * Complex.I) by ring]

/-- **`sine_ratio_exact`.**  The exact decomposition of the quotient-kernel
amplitude into a retained linear phase and a sine ratio.  The denominator
hypothesis `sin(x/n) ≠ 0` is explicit. -/
theorem sine_ratio_exact (n : ℕ) (hn : 0 < n) (x : ℂ)
    (hs : Complex.sin (x / (n : ℂ)) ≠ 0) :
    (1 - Complex.exp (-(2 * x * Complex.I))) /
        ((n : ℂ) * (1 - Complex.exp (-(2 * (x / (n : ℂ)) * Complex.I))))
      = Complex.exp (-(x * Complex.I) * (1 - 1 / (n : ℂ))) *
          (Complex.sin x / ((n : ℂ) * Complex.sin (x / (n : ℂ)))) := by
  have hnc : ((n : ℂ)) ≠ 0 := by exact_mod_cast hn.ne'
  have hexp1 : Complex.exp (-(x * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
  have hexp2 : Complex.exp (-((x / (n : ℂ)) * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
  rw [one_sub_exp, one_sub_exp]
  rw [show Complex.exp (-(x * Complex.I) * (1 - 1 / (n : ℂ)))
      = Complex.exp (-(x * Complex.I)) / Complex.exp (-((x / (n : ℂ)) * Complex.I)) by
    rw [← Complex.exp_sub]
    congr 1
    field_simp
    ring]
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  field_simp

/-! ### The quadratic amplitude error -/

/-- `|sin x − x| ≤ |x|³/4` for `|x| ≤ 1`. -/
theorem abs_sin_sub_self_le {x : ℝ} (hx : |x| ≤ 1) : |Real.sin x - x| ≤ |x| ^ 3 / 4 := by
  have hb := Real.sin_bound hx
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hsplit : Real.sin x - x = (Real.sin x - (x - x ^ 3 / 6)) + (-(x ^ 3 / 6)) := by ring
  have h1 : |Real.sin x - x| ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  have h2 : |x ^ 3 / 6| = |x| ^ 3 / 6 := by
    rw [abs_div, abs_pow]
    norm_num
  have h3 : |x| ^ 4 * (5 / 96) ≤ |x| ^ 3 * (5 / 96) := by
    have : |x| ^ 4 ≤ |x| ^ 3 := by
      calc |x| ^ 4 = |x| ^ 3 * |x| := by ring
        _ ≤ |x| ^ 3 * 1 := by nlinarith [pow_nonneg hx0 3]
        _ = |x| ^ 3 := by ring
    nlinarith
  rw [h2] at h1
  nlinarith [pow_nonneg hx0 3]

/-- **`sine_ratio_quadratic_error`.**  The sine-ratio amplitude differs from
`1` by a **quadratic** amount:
`|sin(Nu)/(N sin u) − 1| ≤ (N u)²` for `N ≥ 1`, `|u| ≤ 1`, `|N u| ≤ 1`,
`u ≠ 0`. -/
theorem sine_ratio_quadratic_error {u : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hu : |u| ≤ 1) (hnu : |(n : ℝ) * u| ≤ 1) (hu0 : u ≠ 0) :
    |Real.sin ((n : ℝ) * u) / ((n : ℝ) * Real.sin u) - 1| ≤ ((n : ℝ) * u) ^ 2 := by
  set N : ℝ := (n : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have habs : 0 < |u| := abs_pos.mpr hu0
  -- basic sine estimates
  have hsu := abs_sin_sub_self_le hu
  have hsnu := abs_sin_sub_self_le hnu
  -- lower bound on |sin u|
  have hcube : |u| ^ 3 ≤ |u| := by
    calc |u| ^ 3 = |u| * (|u| * |u|) := by ring
      _ ≤ |u| * (1 * 1) := by nlinarith [abs_nonneg u]
      _ = |u| := by ring
  have hsinu : (3 / 4) * |u| ≤ |Real.sin u| := by
    have h1 : |u| - |Real.sin u| ≤ |Real.sin u - u| := by
      have := abs_sub_abs_le_abs_sub u (Real.sin u)
      rwa [abs_sub_comm u (Real.sin u)] at this
    nlinarith
  have hsinu0 : Real.sin u ≠ 0 := by
    intro h
    rw [h, abs_zero] at hsinu
    nlinarith
  -- numerator estimate
  have hnum : |Real.sin (N * u) - N * Real.sin u| ≤ (N * |u|) ^ 3 / 2 := by
    have hsplit : Real.sin (N * u) - N * Real.sin u
        = (Real.sin (N * u) - N * u) - N * (Real.sin u - u) := by ring
    have h1 : |Real.sin (N * u) - N * Real.sin u|
        ≤ |Real.sin (N * u) - N * u| + |N * (Real.sin u - u)| := by
      rw [hsplit, sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    have h2 : |N * (Real.sin u - u)| = N * |Real.sin u - u| := by
      rw [abs_mul, abs_of_pos hN0]
    have h3 : N * |Real.sin u - u| ≤ N * (|u| ^ 3 / 4) := by
      exact mul_le_mul_of_nonneg_left hsu hN0.le
    have h4 : |N * u| ^ 3 = (N * |u|) ^ 3 := by
      rw [abs_mul, abs_of_pos hN0]
    have hsq1 : (1 : ℝ) ≤ N ^ 2 := by nlinarith [hN1]
    have hNN : N ≤ N ^ 3 := by nlinarith [hN0, hsq1]
    have hcu : (0 : ℝ) ≤ |u| ^ 3 := pow_nonneg (abs_nonneg u) 3
    have hexp3 : (N * |u|) ^ 3 = N ^ 3 * |u| ^ 3 := by ring
    have h5 : N * (|u| ^ 3 / 4) ≤ (N * |u|) ^ 3 / 4 := by
      rw [hexp3]
      have hmm : N * |u| ^ 3 ≤ N ^ 3 * |u| ^ 3 := mul_le_mul_of_nonneg_right hNN hcu
      linarith
    rw [h2] at h1
    rw [h4] at hsnu
    linarith
  -- denominator lower bound
  have hden : (3 / 4) * (N * |u|) ≤ |N * Real.sin u| := by
    rw [abs_mul, abs_of_pos hN0]
    nlinarith
  have hdenpos : 0 < |N * Real.sin u| := lt_of_lt_of_le (by positivity) hden
  have hrewrite : Real.sin (N * u) / (N * Real.sin u) - 1
      = (Real.sin (N * u) - N * Real.sin u) / (N * Real.sin u) := by
    field_simp
  rw [hrewrite, abs_div, div_le_iff₀ hdenpos]
  have hsq : (N * u) ^ 2 = (N * |u|) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  rw [hsq]
  calc |Real.sin (N * u) - N * Real.sin u| ≤ (N * |u|) ^ 3 / 2 := hnum
    _ ≤ (N * |u|) ^ 2 * ((3 / 4) * (N * |u|)) := by nlinarith [mul_pos hN0 habs]
    _ ≤ (N * |u|) ^ 2 * |N * Real.sin u| := by
        exact mul_le_mul_of_nonneg_left hden (by positivity)

end SineDecomposition

end Gate1A
