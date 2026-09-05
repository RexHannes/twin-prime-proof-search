/-
# Gate1B / R11 : the exact reciprocity identity

For coprime `A, k` with modular inverses `A'` (mod `k`) and `k'` (mod `A`) we prove, first
as an exact identity in `ℝ / ℤ` (equivalently: up to an explicit integer),

```
A'/k + k'/A = 1/(A k)   (mod 1),
```

and then the exponential form actually used by the compiler, at the **fixed shift 2**:

```
e_k(-2h A') = e_A(2h k') · e_{Ak}(-2h).
```

Nothing here is an estimate; the integer witness is exhibited explicitly.
-/
import Mathlib

namespace Gate1B.R11

open Complex

noncomputable section

/-! ## 1. The additive character `e(x) = exp(2πix)` -/

/-- `e(x) = exp(2π i x)`. -/
def ec (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/-- `e` turns addition into multiplication. -/
theorem ec_add (x y : ℝ) : ec (x + y) = ec x * ec y := by
  unfold ec
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- `e` is trivial on the integers. -/
theorem ec_intCast (n : ℤ) : ec (n : ℝ) = 1 := by
  unfold ec
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- `e` only sees the argument modulo `1`. -/
theorem ec_add_int (x : ℝ) (n : ℤ) : ec (x + (n : ℝ)) = ec x := by
  rw [ec_add, ec_intCast, mul_one]

/-- `e_q(m) = e(m/q)`, the additive character to the modulus `q`. -/
def eMod (q : ℤ) (m : ℝ) : ℂ := ec (m / (q : ℝ))

/-! ## 2. The reciprocity identity in `ℝ/ℤ` -/

/-- The integer witness of reciprocity: `A A' + k k' − 1` is divisible by `A k`. -/
theorem reciprocity_dvd {A k A' k' : ℤ} (hcop : IsCoprime A k)
    (hA' : k ∣ A * A' - 1) (hk' : A ∣ k * k' - 1) :
    A * k ∣ A * A' + k * k' - 1 := by
  refine hcop.mul_dvd ?_ ?_
  · obtain ⟨c, hc⟩ := hk'
    exact ⟨A' + c, by linarith [hc]⟩
  · obtain ⟨c, hc⟩ := hA'
    exact ⟨c + k', by linarith [hc]⟩

/-- **Exact reciprocity modulo `1`.**  With `A A' ≡ 1 (mod k)` and `k k' ≡ 1 (mod A)`,

```
A'/k + k'/A = 1/(A k) + n
```

for the explicit integer `n = (A A' + k k' − 1)/(A k)`. -/
theorem reciprocity_mod_one {A k A' k' : ℤ} (hA : A ≠ 0) (hk : k ≠ 0) (hcop : IsCoprime A k)
    (hA' : k ∣ A * A' - 1) (hk' : A ∣ k * k' - 1) :
    ∃ n : ℤ, (A' : ℝ) / (k : ℝ) + (k' : ℝ) / (A : ℝ) = 1 / ((A : ℝ) * (k : ℝ)) + (n : ℝ) := by
  obtain ⟨n, hn⟩ := reciprocity_dvd hcop hA' hk'
  refine ⟨n, ?_⟩
  have hAR : (A : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hA
  have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hnR : (A : ℝ) * (A' : ℝ) + (k : ℝ) * (k' : ℝ) - 1 = (A : ℝ) * (k : ℝ) * (n : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hn
  field_simp
  linarith [hnR]

/-! ## 3. The exponential reciprocity identity at the fixed shift `2` -/

/-- **Exponential reciprocity (exact).**

```
e_k(-2h A') = e_A(2h k') · e_{Ak}(-2h).
```

The shift is the fixed value `2`; nothing is averaged over it. -/
theorem reciprocity_exp {A k A' k' : ℤ} (hA : A ≠ 0) (hk : k ≠ 0) (hcop : IsCoprime A k)
    (hA' : k ∣ A * A' - 1) (hk' : A ∣ k * k' - 1) (h : ℤ) :
    eMod k (-2 * h * A') = eMod A (2 * h * k') * eMod (A * k) (-2 * h) := by
  obtain ⟨n, hn⟩ := reciprocity_mod_one hA hk hcop hA' hk'
  have hAR : (A : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hA
  have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hsplit : (-2 * (h : ℝ) * (A' : ℝ)) / (k : ℝ)
      = ((2 * (h : ℝ) * (k' : ℝ)) / (A : ℝ) + (-2 * (h : ℝ)) / ((A : ℝ) * (k : ℝ)))
        + ((-2 * h * n : ℤ) : ℝ) := by
    have hA'k : (A' : ℝ) / (k : ℝ)
        = 1 / ((A : ℝ) * (k : ℝ)) + (n : ℝ) - (k' : ℝ) / (A : ℝ) := by linarith [hn]
    have : (-2 * (h : ℝ) * (A' : ℝ)) / (k : ℝ) = (-2 * (h : ℝ)) * ((A' : ℝ) / (k : ℝ)) := by
      ring
    rw [this, hA'k]
    push_cast
    field_simp
    ring
  unfold eMod
  push_cast
  rw [hsplit, ec_add_int, ec_add]

end

end Gate1B.R11
