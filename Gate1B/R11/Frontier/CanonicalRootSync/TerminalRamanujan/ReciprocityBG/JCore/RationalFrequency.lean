/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : the rational-frequency split  (J2)

Append-only module; exact algebra only, no analytic statement.

The JCORE square expansion pairs a core point `(n, u, v)` with a second copy `(ñ, ũ, ṽ)`.  The
route splits the expansion according to whether the two *rational frequencies* agree:

```
EqualRationalFrequency :   n / (uv)  =  ñ / (ũṽ).
```

§2 proves, under the banked dual support assumptions `(n, uv) = 1` and `(ñ, ũṽ) = 1` (and
positive denominators), the exact characterisation

```
n / (uv) = ñ / (ũṽ)   ↔   n = ñ  ∧  uv = ũṽ,
```

signed frequencies included (`n`, `ñ` range over `ℤ`, both signs and `0`).  §3 records that the
class is *not* the class of identical factorisations: `(u, v)` and `(ũ, ṽ)` with the same product
are equal-frequency.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.Core

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-! ## 1. The frequency and the split predicate -/

/-- The rational frequency `n / (uv)` of a core point (signed). -/
def freq (i : Core) : ℚ := (i.n : ℚ) / ((i.den : ℕ) : ℚ)

/-- **`EqualRationalFrequency`** — the two copies carry the same rational frequency. -/
def EqualRationalFrequency (i j : Core) : Prop := freq i = freq j

/-- **`UnequalRationalFrequency`** — the negation; this is the off-diagonal JCORE owner's
support. -/
def UnequalRationalFrequency (i j : Core) : Prop := ¬ EqualRationalFrequency i j

instance (i j : Core) : Decidable (EqualRationalFrequency i j) := by
  unfold EqualRationalFrequency; infer_instance

/-! ## 2. The exact characterisation under dual support -/

/-- Cross-multiplied form of equality of frequencies. -/
theorem freq_eq_iff_cross {i j : Core} (hi : 0 < i.den) (hj : 0 < j.den) :
    freq i = freq j ↔ i.n * (j.den : ℤ) = j.n * (i.den : ℤ) := by
  have hi' : ((i.den : ℕ) : ℚ) ≠ 0 := by positivity
  have hj' : ((j.den : ℕ) : ℚ) ≠ 0 := by positivity
  unfold freq
  rw [div_eq_div_iff hi' hj']
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) h

/-- **The exact rational-frequency characterisation.**  Under the banked dual support
assumptions, two admissible core points have the same frequency exactly when the numerators
agree *and* the denominators agree. -/
theorem equalRationalFrequency_iff {i j : Core} (hi : CoreAdmissible i) (hj : CoreAdmissible j) :
    EqualRationalFrequency i j ↔ i.n = j.n ∧ i.den = j.den := by
  have hip : 0 < i.den := den_pos hi
  have hjp : 0 < j.den := den_pos hj
  constructor
  · intro h
    have hcross : i.n * (j.den : ℤ) = j.n * (i.den : ℤ) :=
      (freq_eq_iff_cross hip hjp).mp h
    -- absolute values give mutual divisibility of the denominators
    have habs : i.n.natAbs * j.den = j.n.natAbs * i.den := by
      have := congrArg Int.natAbs hcross
      simpa [Int.natAbs_mul] using this
    have hdvd1 : i.den ∣ j.den := by
      have h1 : i.den ∣ i.n.natAbs * j.den := ⟨j.n.natAbs, by rw [habs]; ring⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hi.coprime) h1)
    have hdvd2 : j.den ∣ i.den := by
      have h1 : j.den ∣ j.n.natAbs * i.den := ⟨i.n.natAbs, by rw [← habs]; ring⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hj.coprime) h1)
    have hden : i.den = j.den := Nat.dvd_antisymm hdvd1 hdvd2
    refine ⟨?_, hden⟩
    have hne : ((i.den : ℤ)) ≠ 0 := by exact_mod_cast hip.ne'
    have : i.n * (i.den : ℤ) = j.n * (i.den : ℤ) := by rw [hden] at hcross ⊢; exact hcross
    exact mul_right_cancel₀ hne this
  · rintro ⟨hn, hd⟩
    unfold EqualRationalFrequency freq
    rw [hn, hd]

/-! ## 3. The class is closed under refactorisation -/

/-- **Different decompositions with the same product stay in the equal-frequency class.**  The
split is by the *product* `uv`, never by the factorisation. -/
theorem equalRationalFrequency_of_same_product {n : ℤ} {u v u' v' : ℕ} (h : u * v = u' * v') :
    EqualRationalFrequency ⟨n, u, v⟩ ⟨n, u', v'⟩ := by
  unfold EqualRationalFrequency freq Core.den
  simp only
  rw [h]

/-- Explicit witness: `(1, 2, 3)` and `(1, 6, 1)` are distinct core points of the same
frequency. -/
theorem equalFrequency_distinct_factorisations :
    EqualRationalFrequency ⟨1, 2, 3⟩ ⟨1, 6, 1⟩ ∧ (⟨1, 2, 3⟩ : Core) ≠ ⟨1, 6, 1⟩ := by
  refine ⟨equalRationalFrequency_of_same_product (by norm_num), ?_⟩
  intro h
  have := congrArg Core.u h
  norm_num at this

/-- Signed frequencies are genuinely signed: `n = -1` and `n = 1` over the same denominator are
*not* equal-frequency. -/
theorem signed_frequencies_distinguished :
    UnequalRationalFrequency ⟨-1, 1, 1⟩ ⟨1, 1, 1⟩ := by
  unfold UnequalRationalFrequency EqualRationalFrequency freq Core.den
  norm_num

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
