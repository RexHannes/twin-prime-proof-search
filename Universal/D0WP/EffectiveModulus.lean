/-
# Universal / D0WP — effective modulus reduction

**Status of this module: KERNEL_PROVED elementary algebra.**

For the inner `d0 · wp` provider one always meets the phase

```
e_r(A * inverse_r(u)),      gcd(u, r) = 1,
```

where `A` need not be coprime to `r`.  The *effective modulus* is obtained by
cancelling `s = gcd(A, r)`:

```
rSharp = r / s,     ASharp = A / s.
```

This module proves, with no squarefree hypothesis on `r`:

* `ASharp` and `rSharp` are coprime;
* the exact phase identity
  `e_r(A * inverse_r(u)) = e_{rSharp}(ASharp * inverse_{rSharp}(u))`,
  where each inverse is an arbitrary integer inverse for its own modulus;
* independence of the chosen inverse representative.

No estimate is claimed here.
-/
import Universal.D0WP.AdditiveCharacterCore

namespace Universal.D0WP

open Finset

noncomputable section

/-- The cancelled common factor `s = gcd(A, r)`. -/
def commonFactor (A r : ℕ) : ℕ := Nat.gcd A r

/-- The effective modulus `rSharp = r / gcd(A, r)`. -/
def rSharp (A r : ℕ) : ℕ := r / Nat.gcd A r

/-- The effective numerator `ASharp = A / gcd(A, r)`. -/
def ASharp (A r : ℕ) : ℕ := A / Nat.gcd A r

theorem commonFactor_ne_zero {A r : ℕ} (hr : r ≠ 0) : commonFactor A r ≠ 0 := by
  simpa [commonFactor, Nat.gcd_eq_zero_iff] using fun _ h => hr h

theorem rSharp_ne_zero {A r : ℕ} (hr : r ≠ 0) : rSharp A r ≠ 0 := by
  have hs : 0 < Nat.gcd A r := Nat.pos_of_ne_zero (commonFactor_ne_zero (A := A) hr)
  have : 0 < r / Nat.gcd A r := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr)
    (Nat.gcd_dvd_right A r)) hs
  simpa [rSharp] using this.ne'

theorem factor_r (A r : ℕ) : r = commonFactor A r * rSharp A r := by
  simpa [commonFactor, rSharp] using (Nat.mul_div_cancel' (Nat.gcd_dvd_right A r)).symm

theorem factor_A (A r : ℕ) : A = commonFactor A r * ASharp A r := by
  simpa [commonFactor, ASharp] using (Nat.mul_div_cancel' (Nat.gcd_dvd_left A r)).symm

/-- **Effective coprimality.**  After cancelling `gcd(A, r)` the numerator and
the modulus are coprime.  No squarefree hypothesis is used. -/
theorem coprime_ASharp_rSharp {A r : ℕ} (hr : r ≠ 0) :
    Nat.Coprime (ASharp A r) (rSharp A r) := by
  have hs : 0 < Nat.gcd A r := Nat.pos_of_ne_zero (commonFactor_ne_zero (A := A) hr)
  simpa [ASharp, rSharp] using Nat.coprime_div_gcd_div_gcd hs

theorem rSharp_dvd (A r : ℕ) : (rSharp A r : ℤ) ∣ (r : ℤ) := by
  have hnat : rSharp A r ∣ r :=
    ⟨commonFactor A r, by rw [mul_comm]; exact factor_r A r⟩
  exact_mod_cast Int.natCast_dvd_natCast.mpr hnat

/-- Any inverse of `u` modulo `r` is also an inverse modulo the effective
modulus, and hence agrees with any inverse modulo `rSharp`. -/
theorem inverse_congr_rSharp {A r : ℕ} {u ubar ubar' : ℤ}
    (hu : u * ubar ≡ 1 [ZMOD (r : ℤ)])
    (hu' : u * ubar' ≡ 1 [ZMOD (rSharp A r : ℤ)]) :
    ubar ≡ ubar' [ZMOD (rSharp A r : ℤ)] := by
  have h1 : u * ubar ≡ 1 [ZMOD (rSharp A r : ℤ)] :=
    Int.ModEq.of_dvd (rSharp_dvd A r) hu
  calc ubar = ubar * 1 := by ring
    _ ≡ ubar * (u * ubar') [ZMOD (rSharp A r : ℤ)] := (Int.ModEq.refl ubar).mul hu'.symm
    _ = (u * ubar) * ubar' := by ring
    _ ≡ 1 * ubar' [ZMOD (rSharp A r : ℤ)] := h1.mul_right _
    _ = ubar' := by ring

/-- **EFFECTIVE MODULUS REDUCTION (kernel-proved).**  For every `u` with an
inverse modulo `r`,

```
e_r(A * inverse_r(u)) = e_{rSharp}(ASharp * inverse_{rSharp}(u)),
```

for arbitrary integer inverses on each side.  No squarefree assumption on `r`. -/
theorem ac_effective_modulus {A r : ℕ} (hr : r ≠ 0) {u ubar ubar' : ℤ}
    (hu : u * ubar ≡ 1 [ZMOD (r : ℤ)])
    (hu' : u * ubar' ≡ 1 [ZMOD (rSharp A r : ℤ)]) :
    ac r ((A : ℤ) * ubar) = ac (rSharp A r) ((ASharp A r : ℤ) * ubar') := by
  have hs : commonFactor A r ≠ 0 := commonFactor_ne_zero (A := A) hr
  have hrs : r = commonFactor A r * rSharp A r := factor_r A r
  have hAs : (A : ℤ) = (commonFactor A r : ℤ) * (ASharp A r : ℤ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) (factor_A A r)
  have step1 : ac r ((A : ℤ) * ubar)
      = ac (commonFactor A r * rSharp A r)
          ((commonFactor A r : ℤ) * ((ASharp A r : ℤ) * ubar)) := by
    rw [← hrs, hAs]
    ring_nf
  rw [step1, ac_scale hs]
  exact ac_congr (rSharp_ne_zero (A := A) hr)
    ((inverse_congr_rSharp (A := A) hu hu').mul_left _)

/-- **Representative independence.**  The reduced phase does not depend on the
chosen inverse representative modulo the effective modulus. -/
theorem ac_representative_independent {A r : ℕ} (hr : r ≠ 0) {u v v' : ℤ}
    (hv : u * v ≡ 1 [ZMOD (rSharp A r : ℤ)])
    (hv' : u * v' ≡ 1 [ZMOD (rSharp A r : ℤ)]) :
    ac (rSharp A r) ((ASharp A r : ℤ) * v) = ac (rSharp A r) ((ASharp A r : ℤ) * v') := by
  have hcong : v ≡ v' [ZMOD (rSharp A r : ℤ)] := by
    calc v = v * 1 := by ring
      _ ≡ v * (u * v') [ZMOD (rSharp A r : ℤ)] := (Int.ModEq.refl v).mul hv'.symm
      _ = (u * v) * v' := by ring
      _ ≡ 1 * v' [ZMOD (rSharp A r : ℤ)] := hv.mul_right _
      _ = v' := by ring
  exact ac_congr (rSharp_ne_zero (A := A) hr) (hcong.mul_left _)

end

end Universal.D0WP
