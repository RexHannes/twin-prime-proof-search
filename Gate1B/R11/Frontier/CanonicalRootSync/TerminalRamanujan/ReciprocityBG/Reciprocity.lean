/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
source-relation reciprocity and the exit of the common factor `e`  (B3)

Append-only module.  Exact algebra only; **no analytic saving is stated or implied anywhere in
this file**, and nothing pre-existing is edited.

Contents.

* §1  the classical reciprocity identity `A/b + B/a ≡ 1/(ab) (mod 1)` for coprime `a`, `b` with
  `aA ≡ 1 (mod b)`, `bB ≡ 1 (mod a)` — kernel-proved at the level of `ℚ / ℤ`;
* §2  the split `C = C₁C₂`, the composite moduli `M₁ = C₁u`, `M₂ = C₂v`, the prime-power-free
  extraction `eᵢ = (e, Cᵢ)`, `Lᵢ = Cᵢ/eᵢ`, and the exact factorisation `Cᵢ = eᵢLᵢ` together with
  the coprimality `(Lᵢ, e/eᵢ) = 1`;
* §3  the **source relation** `z' − z = e k` and the exact identity showing that the large common
  factor `e` leaves the reciprocal denominator:

  ```
  2n/(C u v z) − 2n/(C u v z')  =  2 n k / (D u v z z'),        C = e D .
  ```

  The factor `e` is *not* lost: it is still present in the source relation `z' = z + e k` and in
  `C = e D`.  Only the reciprocal denominator has been reduced.
* §4  the firewall: without the source relation the reduction is false (finite counterexample).

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.CRTPhase

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

/-! ## 1. The reciprocity identity in `ℚ / ℤ` -/

/-- **Reciprocity.**  For coprime nonzero `a`, `b` with `a A ≡ 1 (mod b)` and `b B ≡ 1 (mod a)`,
`A/b + B/a ≡ 1/(ab)` in `ℚ / ℤ`. -/
theorem reciprocity_mod_one {a b A B : ℤ} (ha0 : (a : ℚ) ≠ 0) (hb0 : (b : ℚ) ≠ 0)
    (hab : IsCoprime a b) (hA : a * A ≡ 1 [ZMOD b]) (hB : b * B ≡ 1 [ZMOD a]) :
    CongMod1 ((A : ℚ) / (b : ℚ) + (B : ℚ) / (a : ℚ)) (1 / ((a : ℚ) * (b : ℚ))) := by
  have hda : a ∣ a * A + b * B - 1 := by
    have h1 : a ∣ b * B - 1 := Int.ModEq.dvd hB.symm
    have h2 : a * A + b * B - 1 = a * A + (b * B - 1) := by ring
    rw [h2]
    exact Dvd.dvd.add (Dvd.intro A rfl) h1
  have hdb : b ∣ a * A + b * B - 1 := by
    have h1 : b ∣ a * A - 1 := Int.ModEq.dvd hA.symm
    have h2 : a * A + b * B - 1 = (a * A - 1) + b * B := by ring
    rw [h2]
    exact Dvd.dvd.add h1 (Dvd.intro B rfl)
  obtain ⟨k, hk⟩ := hab.mul_dvd hda hdb
  refine ⟨k, ?_⟩
  have hkq : ((a * A + b * B - 1 : ℤ) : ℚ) = ((a * b : ℤ) : ℚ) * (k : ℚ) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hk
  push_cast at hkq
  field_simp
  linarith [hkq]

/-! ## 2. The split `C = C₁C₂` and the extraction `Cᵢ = eᵢLᵢ` -/

/-- The composite modulus `M₁ = C₁ u`. -/
def Mone (C1 u : ℕ) : ℕ := C1 * u

/-- The composite modulus `M₂ = C₂ v`. -/
def Mtwo (C2 v : ℕ) : ℕ := C2 * v

/-- `eᵢ = (e, Cᵢ)`: the part of the common factor `e` sitting inside `Cᵢ`. -/
def eComp (e Ci : ℕ) : ℕ := Nat.gcd e Ci

/-- `Lᵢ = Cᵢ / eᵢ`: the residual modulus after the common factor has been extracted. -/
def Lcomp (e Ci : ℕ) : ℕ := Ci / Nat.gcd e Ci

/-- **Exact extraction**: `Cᵢ = eᵢ Lᵢ`. -/
theorem eComp_mul_Lcomp (e Ci : ℕ) : eComp e Ci * Lcomp e Ci = Ci :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right e Ci)

/-- The extracted part divides `e`. -/
theorem eComp_dvd (e Ci : ℕ) : eComp e Ci ∣ e := Nat.gcd_dvd_left e Ci

/-- **The residual modulus is coprime to the residual common factor**: `(Lᵢ, e/eᵢ) = 1`.  This is
what it means for the extraction to be complete on the `Cᵢ`-side. -/
theorem coprime_Lcomp (e Ci : ℕ) (h : 0 < Nat.gcd e Ci) :
    Nat.Coprime (Lcomp e Ci) (e / Nat.gcd e Ci) :=
  (Nat.coprime_div_gcd_div_gcd h).symm

/-- If `C = C₁C₂` then `M₁M₂ = C u v`: the two composite moduli reassemble the full modulus. -/
theorem Mone_mul_Mtwo (C1 C2 u v : ℕ) : Mone C1 u * Mtwo C2 v = (C1 * C2) * (u * v) := by
  unfold Mone Mtwo; ring

/-! ## 3. The source relation and the exit of `e` from the denominator -/

/-- The reciprocal phase `2n/(C u v z)`. -/
def recipPhase (n C u v z : ℤ) : ℚ := ((2 * n : ℤ) : ℚ) / ((C * u * v * z : ℤ) : ℚ)

/-- **The source relation removes `e` from the reciprocal denominator.**  With `C = e D` and the
source relation `z' = z + e k`,

```
2n/(C u v z) − 2n/(C u v z')  =  2 n k / (D u v z z').
```

The common factor `e` has left the denominator; it is still present in `C = e D` and in the
source relation itself, so nothing has been discarded.  No estimate is claimed. -/
theorem source_relation_reduces_denominator {n e D u v z z' k : ℤ}
    (he0 : (e : ℚ) ≠ 0) (hD0 : (D : ℚ) ≠ 0)
    (hu0 : (u : ℚ) ≠ 0) (hv0 : (v : ℚ) ≠ 0) (hz0 : (z : ℚ) ≠ 0) (hz'0 : (z' : ℚ) ≠ 0)
    (hsrc : z' = z + e * k) :
    recipPhase n (e * D) u v z - recipPhase n (e * D) u v z'
      = ((2 * n * k : ℤ) : ℚ) / ((D * u * v * z * z' : ℤ) : ℚ) := by
  have hz'q : (z' : ℚ) = (z : ℚ) + (e : ℚ) * (k : ℚ) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hsrc
  unfold recipPhase
  push_cast
  rw [hz'q]
  have hsum : (z : ℚ) + (e : ℚ) * (k : ℚ) ≠ 0 := by
    rw [← hz'q]; exact hz'0
  field_simp
  ring

/-- **`e` survives where it must.**  The source relation retains the common factor exactly:
`z' − z = e k`. -/
theorem source_relation_retains_e {e z z' k : ℤ} (hsrc : z' = z + e * k) : z' - z = e * k := by
  rw [hsrc]; ring

/-! ## 4. Firewall: no reduction without the source relation -/

/-- **The reduction genuinely needs `e ∣ z' − z`.**  For `e = 2`, `D = u = v = 1`, `z = 1`,
`z' = 2`, `n = 1` (so that `z' − z = 1` is *not* a multiple of `e`) the difference of reciprocal
phases is `1/2`, which is not of the reduced shape `2nk/(D u v z z') = k` for any integer `k`. -/
theorem reduction_needs_source_relation :
    recipPhase 1 (2 * 1) 1 1 1 - recipPhase 1 (2 * 1) 1 1 2 = 1 / 2
      ∧ ∀ k : ℤ, recipPhase 1 (2 * 1) 1 1 1 - recipPhase 1 (2 * 1) 1 1 2
          ≠ ((2 * 1 * k : ℤ) : ℚ) / ((1 * 1 * 1 * 1 * 2 : ℤ) : ℚ) := by
  have hval : recipPhase 1 (2 * 1) 1 1 1 - recipPhase 1 (2 * 1) 1 1 2 = 1 / 2 := by
    unfold recipPhase; norm_num
  refine ⟨hval, fun k hk => ?_⟩
  rw [hval] at hk
  push_cast at hk
  have : (1 : ℚ) = 2 * k := by linarith [hk]
  have h2 : (1 : ℤ) = 2 * k := by exact_mod_cast this
  omega

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
