/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : the normalised determinant  (J3)

Append-only module; exact algebra only, kernel-proved, no analytic statement.

With `h = (v, ṽ)`, `v = h a`, `ṽ = h b` (so `(a,b) = 1` and `[v,ṽ] = h a b`), the normalised
determinant of a pair of JCORE core points is

```
Δ = n b ũ − ñ a u,
```

and the exact frequency difference is

```
n/(uv) − ñ/(ũṽ) = Δ / ([v,ṽ] u ũ).
```

§2 proves that identity, §3 proves `Δ = 0 ↔ EqualRationalFrequency`, hence `Δ ≠ 0` on the
unequal-frequency (off-diagonal) JCORE owner.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.RationalFrequency

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-! ## 1. The common part of the second denominators -/

/-- `h = (v, ṽ)`. -/
def hCommon (i j : Core) : ℕ := Nat.gcd i.v j.v

/-- `a = v / h`. -/
def aPart (i j : Core) : ℕ := i.v / hCommon i j

/-- `b = ṽ / h`. -/
def bPart (i j : Core) : ℕ := j.v / hCommon i j

/-- `ℓ = [v, ṽ]`. -/
def lcmPart (i j : Core) : ℕ := Nat.lcm i.v j.v

theorem hCommon_pos {i j : Core} (hi : 0 < i.v) : 0 < hCommon i j :=
  Nat.gcd_pos_of_pos_left _ hi

theorem v_eq_h_mul_a (i j : Core) : i.v = hCommon i j * aPart i j :=
  (Nat.mul_div_cancel' (Nat.gcd_dvd_left i.v j.v)).symm

theorem v_eq_h_mul_b (i j : Core) : j.v = hCommon i j * bPart i j :=
  (Nat.mul_div_cancel' (Nat.gcd_dvd_right i.v j.v)).symm

/-- `(a, b) = 1`. -/
theorem aPart_coprime_bPart {i j : Core} (hi : 0 < i.v) :
    Nat.Coprime (aPart i j) (bPart i j) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hi)

/-- `[v, ṽ] = h a b`. -/
theorem lcmPart_eq (i j : Core) (hi : 0 < i.v) :
    lcmPart i j = hCommon i j * (aPart i j * bPart i j) := by
  have hh : 0 < hCommon i j := hCommon_pos hi
  have hgl : hCommon i j * lcmPart i j = i.v * j.v := Nat.gcd_mul_lcm i.v j.v
  have hprod : i.v * j.v = hCommon i j * (hCommon i j * (aPart i j * bPart i j)) := by
    conv_lhs => rw [v_eq_h_mul_a i j, v_eq_h_mul_b i j]
    ring
  have : hCommon i j * lcmPart i j
      = hCommon i j * (hCommon i j * (aPart i j * bPart i j)) := by rw [hgl, hprod]
  exact Nat.eq_of_mul_eq_mul_left hh this

/-! ## 2. The determinant and the exact frequency difference -/

/-- **The normalised determinant** `Δ = n b ũ − ñ a u`. -/
def Delta (i j : Core) : ℤ := i.n * (bPart i j : ℤ) * (j.u : ℤ) - j.n * (aPart i j : ℤ) * (i.u : ℤ)

/-- **The exact determinant identity**

`n/(uv) − ñ/(ũṽ) = Δ / ([v,ṽ] u ũ)`. -/
theorem freq_sub_eq_delta_div {i j : Core} (hiu : 0 < i.u) (hiv : 0 < i.v) (hju : 0 < j.u)
    (hjv : 0 < j.v) :
    freq i - freq j = ((Delta i j : ℤ) : ℚ) / (((lcmPart i j * i.u * j.u : ℕ) : ℚ)) := by
  have hh : 0 < hCommon i j := hCommon_pos hiv
  have ha : 0 < aPart i j := by
    rcases Nat.eq_zero_or_pos (aPart i j) with h0 | h
    · rw [v_eq_h_mul_a i j, h0, Nat.mul_zero] at hiv; omega
    · exact h
  have hb : 0 < bPart i j := by
    rcases Nat.eq_zero_or_pos (bPart i j) with h0 | h
    · rw [v_eq_h_mul_b i j, h0, Nat.mul_zero] at hjv; omega
    · exact h
  have hlcm : lcmPart i j = hCommon i j * (aPart i j * bPart i j) := lcmPart_eq i j hiv
  have hvq : ((i.v : ℕ) : ℚ) = ((hCommon i j : ℕ) : ℚ) * ((aPart i j : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℚ)) (v_eq_h_mul_a i j)
  have hvq' : ((j.v : ℕ) : ℚ) = ((hCommon i j : ℕ) : ℚ) * ((bPart i j : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℚ)) (v_eq_h_mul_b i j)
  have hiu' : ((i.u : ℕ) : ℚ) ≠ 0 := by positivity
  have hju' : ((j.u : ℕ) : ℚ) ≠ 0 := by positivity
  have hhq : ((hCommon i j : ℕ) : ℚ) ≠ 0 := by positivity
  have haq : ((aPart i j : ℕ) : ℚ) ≠ 0 := by positivity
  have hbq : ((bPart i j : ℕ) : ℚ) ≠ 0 := by positivity
  unfold freq Core.den Delta
  rw [hlcm]
  push_cast
  rw [hvq, hvq']
  field_simp

/-! ## 3. `Δ = 0` is exactly the equal-frequency class -/

/-- **`Δ = 0 ↔ EqualRationalFrequency`.** -/
theorem delta_eq_zero_iff {i j : Core} (hiu : 0 < i.u) (hiv : 0 < i.v) (hju : 0 < j.u)
    (hjv : 0 < j.v) :
    Delta i j = 0 ↔ EqualRationalFrequency i j := by
  have hh : 0 < hCommon i j := hCommon_pos hiv
  have hl : 0 < lcmPart i j := Nat.lcm_pos hiv hjv
  have hden : (((lcmPart i j * i.u * j.u : ℕ) : ℚ)) ≠ 0 := by
    have : 0 < lcmPart i j * i.u * j.u := Nat.mul_pos (Nat.mul_pos hl hiu) hju
    positivity
  have hdiff := freq_sub_eq_delta_div hiu hiv hju hjv
  constructor
  · intro h0
    have : freq i - freq j = 0 := by rw [hdiff, h0]; simp
    unfold EqualRationalFrequency
    linarith
  · intro heq
    have h0 : freq i - freq j = 0 := by unfold EqualRationalFrequency at heq; rw [heq]; ring
    rw [hdiff] at h0
    have hz : ((Delta i j : ℤ) : ℚ) = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact h
      · exact absurd h hden
    exact_mod_cast hz

/-- **On the unequal-frequency JCORE owner the determinant does not vanish.** -/
theorem delta_ne_zero_of_unequal {i j : Core} (hiu : 0 < i.u) (hiv : 0 < i.v) (hju : 0 < j.u)
    (hjv : 0 < j.v) (h : UnequalRationalFrequency i j) : Delta i j ≠ 0 := by
  intro h0
  exact h ((delta_eq_zero_iff hiu hiv hju hjv).mp h0)

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
