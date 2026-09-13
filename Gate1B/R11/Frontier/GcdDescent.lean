/-
# Gate1B / R11 / Frontier : gcd descent along the matched line

Exact algebra only.  Along the matched line of `Gate1B.R11.Frontier.MatchedLine`,

* `gcd(d_t, d_{t+h}) = gcd(d_t, A h)` unconditionally (shift law), and
* `gcd(d_t, d_{t+h}) = gcd(d_t, h)` **once `gcd(d_t, A) = 1`**, which is not assumed silently:
  it is *derived* from the determinant `A B_t − k d_t = −2` together with the oddness of `d_t`
  (the physical source is supported on odd `d`; `gcd(d_t, A) ∣ 2` always, and oddness removes
  the factor 2).  The same argument gives `gcd(B_t, B_{t+h}) = gcd(B_t, h)` from `gcd(B_t, k) = 1`,
  derived from the determinant plus oddness of `B_t`.

Finally the **determinant descent**: writing `g = gcd(d_t, h)`, `d_t = g d'`, `d_{t+h} = g d''`,
`h = g h'`, the two-copy determinant `2h` descends to

```
d' B_{t+h} − d'' B_t = 2 h'.
```

Gcd normalisation: `Int.gcd` is the Mathlib `ℕ`-valued gcd of the absolute values, so all gcd
statements below are equalities of natural numbers and carry no sign ambiguity.
-/
import Gate1B.R11.Frontier.MatchedLine

namespace Gate1B.R11.Frontier

/-! ## 1. The coprimalities, derived rather than assumed -/

/-- A common divisor of the two determinant products divides `2`. -/
theorem dvd_two_of_det {g A B k d : ℤ} (hA : g ∣ A * B) (hk : g ∣ k * d)
    (hdet : A * B - k * d = -2) : g ∣ 2 := by
  have hsub : g ∣ A * B - k * d := dvd_sub hA hk
  rw [hdet] at hsub
  exact (dvd_neg.mp hsub)

/-- A gcd dividing `2` and dividing an odd number is `1`. -/
theorem gcd_eq_one_of_dvd_two {g : ℕ} {x : ℤ} (hdvd : (g : ℤ) ∣ 2) (hgx : (g : ℤ) ∣ x)
    (hodd : Odd x) : g = 1 := by
  have hdvdN : g ∣ 2 := by exact_mod_cast hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvdN with h | h
  · exact h
  · exfalso
    rw [h] at hgx
    obtain ⟨m, hm⟩ := hgx
    obtain ⟨n, hn⟩ := hodd
    omega

/-- `gcd(d, A) ∣ 2` for any point of the matched determinant. -/
theorem gcd_d_A_dvd_two {A k B d : ℤ} (hdet : A * B - k * d = -2) :
    ((Int.gcd d A : ℤ)) ∣ 2 :=
  dvd_two_of_det (Dvd.dvd.mul_right (Int.gcd_dvd_right d A) B)
    (Dvd.dvd.mul_left (Int.gcd_dvd_left d A) k) hdet

/-- `gcd(B, k) ∣ 2` for any point of the matched determinant. -/
theorem gcd_B_k_dvd_two {A k B d : ℤ} (hdet : A * B - k * d = -2) :
    ((Int.gcd B k : ℤ)) ∣ 2 :=
  dvd_two_of_det (Dvd.dvd.mul_left (Int.gcd_dvd_left B k) A)
    (Dvd.dvd.mul_right (Int.gcd_dvd_right B k) d) hdet

/-- With `d` odd, `gcd(d, A) = 1`. -/
theorem coprime_d_A {A k B d : ℤ} (hdet : A * B - k * d = -2) (hodd : Odd d) :
    Int.gcd d A = 1 :=
  gcd_eq_one_of_dvd_two (gcd_d_A_dvd_two hdet) (Int.gcd_dvd_left d A) hodd

/-- With `B` odd, `gcd(B, k) = 1`. -/
theorem coprime_B_k {A k B d : ℤ} (hdet : A * B - k * d = -2) (hodd : Odd B) :
    Int.gcd B k = 1 :=
  gcd_eq_one_of_dvd_two (gcd_B_k_dvd_two hdet) (Int.gcd_dvd_left B k) hodd

/-! ## 2. Gcd descent -/

/-- Shift form: `gcd(d_t, d_{t+h}) = gcd(d_t, A h)` — no hypothesis needed. -/
theorem gcd_dLine_shift (d0 A t h : ℤ) :
    Int.gcd (dLine d0 A t) (dLine d0 A (t + h)) = Int.gcd (dLine d0 A t) (A * h) := by
  rw [dLine_shift]
  have : dLine d0 A t + A * h = A * h + 1 * (dLine d0 A t) := by ring
  rw [this, Int.gcd_add_mul_right_right]

/-- Cancelling a coprime factor from the second argument of `Int.gcd`. -/
theorem gcd_mul_left_cancel_of_coprime {a b c : ℤ} (hco : Int.gcd a b = 1) :
    Int.gcd a (b * c) = Int.gcd a c := by
  have hnat : Nat.Coprime b.natAbs a.natAbs := by
    have : Nat.Coprime a.natAbs b.natAbs := hco
    exact this.symm
  show Nat.gcd a.natAbs (b * c).natAbs = Nat.gcd a.natAbs c.natAbs
  rw [Int.natAbs_mul]
  exact Nat.Coprime.gcd_mul_left_cancel_right _ hnat

/-- **GCD DESCENT (d-side).**  `gcd(d_t, d_{t+h}) = gcd(d_t, h)` under the exact
coprimality `gcd(d_t, A) = 1`. -/
theorem gcd_dLine_two_copy {d0 A t : ℤ} (hco : Int.gcd (dLine d0 A t) A = 1) (h : ℤ) :
    Int.gcd (dLine d0 A t) (dLine d0 A (t + h)) = Int.gcd (dLine d0 A t) h := by
  rw [gcd_dLine_shift, gcd_mul_left_cancel_of_coprime hco]

/-- **GCD DESCENT (B-side).**  `gcd(B_t, B_{t+h}) = gcd(B_t, h)` under `gcd(B_t, k) = 1`. -/
theorem gcd_BLine_two_copy {B0 k t : ℤ} (hco : Int.gcd (BLine B0 k t) k = 1) (h : ℤ) :
    Int.gcd (BLine B0 k t) (BLine B0 k (t + h)) = Int.gcd (BLine B0 k t) h := by
  rw [BLine_shift]
  have hrw : BLine B0 k t + k * h = k * h + 1 * (BLine B0 k t) := by ring
  rw [hrw, Int.gcd_add_mul_right_right, gcd_mul_left_cancel_of_coprime hco]

/-- The `d`-side coprimality is available from the physical hypotheses (determinant + `d` odd). -/
theorem gcd_dLine_two_copy_of_det {A k d0 B0 : ℤ} (h0 : A * B0 - k * d0 = -2) (t : ℤ)
    (hodd : Odd (dLine d0 A t)) (h : ℤ) :
    Int.gcd (dLine d0 A t) (dLine d0 A (t + h)) = Int.gcd (dLine d0 A t) h :=
  gcd_dLine_two_copy (coprime_d_A (k := k) (B := BLine B0 k t) (matched_det_line h0 t) hodd) h

/-- The `B`-side coprimality is available from the physical hypotheses (determinant + `B` odd). -/
theorem gcd_BLine_two_copy_of_det {A k d0 B0 : ℤ} (h0 : A * B0 - k * d0 = -2) (t : ℤ)
    (hodd : Odd (BLine B0 k t)) (h : ℤ) :
    Int.gcd (BLine B0 k t) (BLine B0 k (t + h)) = Int.gcd (BLine B0 k t) h :=
  gcd_BLine_two_copy (coprime_B_k (A := A) (d := dLine d0 A t) (matched_det_line h0 t) hodd) h

/-! ## 3. Determinant descent after removing `g = gcd(d_t, h)` -/

/-- **EXACT DETERMINANT DESCENT.**  If `d_t = g d'`, `d_{t+h} = g d''`, `h = g h'` with `g ≠ 0`,
then `d' B_{t+h} − d'' B_t = 2 h'`. -/
theorem twoCopy_det_descent {A k d0 B0 : ℤ} (h0 : A * B0 - k * d0 = -2) (t h g d' d'' h' : ℤ)
    (hg : g ≠ 0) (hd : dLine d0 A t = g * d') (hd' : dLine d0 A (t + h) = g * d'')
    (hh : h = g * h') :
    d' * BLine B0 k (t + h) - d'' * BLine B0 k t = 2 * h' := by
  subst hh
  have hmain := twoCopy_det h0 t (g * h')
  rw [hd, hd'] at hmain
  have hcancel : g * (d' * BLine B0 k (t + g * h') - d'' * BLine B0 k t) = g * (2 * h') := by
    linear_combination hmain
  exact mul_left_cancel₀ hg hcancel

end Gate1B.R11.Frontier
