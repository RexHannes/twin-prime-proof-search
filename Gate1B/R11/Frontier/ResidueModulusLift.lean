/-
# Gate1B / R11 / Frontier : the modulus-lifting identity and the local principal correction

Append-only module of the residue-aware delta.  **Exact finite algebra only** — no asymptotic
statement is made anywhere.

For `gcd(h,d) = 1` the selected centered kernel lifts from modulus `d` to modulus `h·d`:

```
I_h(n) · ( δ_d(n) − u_d(n)/φ(d) )
    =
  ( δ_{hd}(n) − u_{hd}(n)/φ(hd) )
    +
  u_d(n)/φ(d) · ( u_h(n)/φ(h) − I_h(n) ) .
```

The second summand is named `LocalPrincipalCorrection`.  The firewall
`modulus_lift_does_not_erase_localPrincipalCorrection` records, by an explicit finite witness,
that modulus lifting **does not** erase it.

Also banked: the exact logarithm split `log((n+2)/d) = log((n+2)/(hd)) + log h`, the bookkeeping
used by the lifted consumer.
-/
import Gate1B.R11.Frontier.ThreeFactorSelectedOwner

namespace Gate1B.R11.Frontier

open Finset

/-! ## 1. CRT multiplicativity of the two parts of the centered kernel -/

/-- CRT: the congruence indicator is multiplicative across coprime moduli. -/
theorem deltaSel_mul_of_coprime {h d : ℕ} (hcop : Nat.Coprime h d) (n : ℕ) :
    deltaSel (h * d) n = deltaSel h n * deltaSel d n := by
  unfold deltaSel
  by_cases hh : h ∣ n + 2
  · by_cases hd : d ∣ n + 2
    · rw [if_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hh hd), if_pos hh, if_pos hd]
      norm_num
    · rw [if_neg, if_pos hh, if_neg hd]
      · norm_num
      · exact fun hc => hd (dvd_trans (Dvd.intro_left h rfl) hc)
  · rw [if_neg, if_neg hh]
    · norm_num
    · exact fun hc => hh (dvd_trans (Dvd.intro d rfl) hc)

/-- The coprimality indicator is multiplicative in the modulus (no hypothesis needed). -/
theorem uSel_mul (h d n : ℕ) : uSel (h * d) n = uSel h n * uSel d n := by
  unfold uSel
  have hiff : Nat.gcd n (h * d) = 1 ↔ Nat.gcd n h = 1 ∧ Nat.gcd n d = 1 := by
    constructor
    · intro hc
      exact ⟨Nat.Coprime.coprime_dvd_right (Dvd.intro d rfl) hc,
        Nat.Coprime.coprime_dvd_right (Dvd.intro_left h rfl) hc⟩
    · intro ⟨h1, h2⟩
      exact Nat.Coprime.mul_right h1 h2
  by_cases hc : Nat.gcd n (h * d) = 1
  · obtain ⟨h1, h2⟩ := hiff.mp hc
    rw [if_pos hc, if_pos h1, if_pos h2]; norm_num
  · rw [if_neg hc]
    by_cases h1 : Nat.gcd n h = 1
    · by_cases h2 : Nat.gcd n d = 1
      · exact absurd (hiff.mpr ⟨h1, h2⟩) hc
      · rw [if_neg h2]; norm_num
    · rw [if_neg h1]; norm_num

/-! ## 2. The modulus-lifting identity -/

/-- **`LocalPrincipalCorrection`** — the exact local term produced by lifting the modulus from
`d` to `h·d`:  `u_d(n)/φ(d) · ( u_h(n)/φ(h) − I_h(n) )`. -/
def LocalPrincipalCorrection (h d n : ℕ) : ℚ :=
  uSel d n / (Nat.totient d : ℚ) * (uSel h n / (Nat.totient h : ℚ) - deltaSel h n)

/-- **The modulus-lifting identity.**  Exact finite algebra, via CRT and `φ(hd) = φ(h)φ(d)`.

(The research statement assumes `h` odd; oddness is *not* needed for the identity — only
`gcd(h,d) = 1` is.  The version with the literal oddness hypothesis is
`modulus_lift_identity_odd` below.) -/
theorem modulus_lift_identity {h d : ℕ} (hcop : Nat.Coprime h d) (n : ℕ) :
    deltaSel h n * centeredSel d n
      = centeredSel (h * d) n + LocalPrincipalCorrection h d n := by
  have hphi : ((Nat.totient (h * d) : ℕ) : ℚ) = (Nat.totient h : ℚ) * (Nat.totient d : ℚ) := by
    rw [Nat.totient_mul hcop]; push_cast; ring
  unfold centeredSel LocalPrincipalCorrection
  rw [deltaSel_mul_of_coprime hcop, uSel_mul, hphi]
  field_simp
  ring

/-- The modulus-lifting identity as stated in the research bank, with the literal oddness
hypothesis on `h` (which the proof does not need). -/
theorem modulus_lift_identity_odd {h d : ℕ} (_hodd : Odd h) (hcop : Nat.Coprime h d) (n : ℕ) :
    deltaSel h n * centeredSel d n
      = centeredSel (h * d) n + LocalPrincipalCorrection h d n :=
  modulus_lift_identity hcop n

/-- **Firewall.**  Modulus lifting does *not* erase the local principal correction: there is an
explicit `(h, d, n)` with `gcd(h,d) = 1`, `h` odd, at which the correction is nonzero. -/
theorem modulus_lift_does_not_erase_localPrincipalCorrection :
    ∃ h d n : ℕ, Odd h ∧ Nat.Coprime h d ∧ LocalPrincipalCorrection h d n ≠ 0 := by
  have h3 : Nat.totient 3 = 2 := by decide
  refine ⟨3, 1, 1, ⟨1, rfl⟩, by decide, ?_⟩
  norm_num [LocalPrincipalCorrection, uSel, deltaSel, h3]

/-- Consequently the lifted kernel is **not** the naive product: the local principal correction
is a genuine extra summand. -/
theorem lifted_kernel_ne_naive_product :
    ∃ h d n : ℕ, Nat.Coprime h d ∧
      deltaSel h n * centeredSel d n ≠ centeredSel (h * d) n := by
  have h3 : Nat.totient 3 = 2 := by decide
  refine ⟨3, 1, 1, by decide, ?_⟩
  norm_num [centeredSel, uSel, deltaSel, h3]

/-! ## 3. The logarithm split -/

/-- **Exact logarithm bookkeeping for the lifted consumer.**  For positive quantities,
`log((n+2)/d) = log((n+2)/(h·d)) + log h`. -/
theorem log_split (y h d : ℝ) (hy : 0 < y) (hh : 0 < h) (hd : 0 < d) :
    Real.log (y / d) = Real.log (y / (h * d)) + Real.log h := by
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hd),
    Real.log_div (ne_of_gt hy) (by positivity), Real.log_mul (ne_of_gt hh) (ne_of_gt hd)]
  ring

/-- The same split at the arithmetic evaluation point `n + 2`, for positive moduli. -/
theorem log_split_shift (n h d : ℕ) (hh : 0 < h) (hd : 0 < d) :
    Real.log (((n : ℝ) + 2) / d) = Real.log (((n : ℝ) + 2) / ((h : ℝ) * d)) + Real.log h := by
  refine log_split _ _ _ (by positivity) ?_ ?_
  · exact_mod_cast hh
  · exact_mod_cast hd

end Gate1B.R11.Frontier
