/-
# Gate04Root.Rows

The divisor-relaxed row map `(r, m, k) ↦ (m, m', k)` and its injectivity, plus the
finite divisor counting interface for the admissible `k`'s attached to a fixed
pair `(m, m')`.

The analytic divisor estimate `τ(n) = X^{o(1)}` is **not** proved here; it is
recorded as an explicit external interface predicate
`DivisorGrowthInterface`, which is never assumed.
-/
import Gate04Root.Affine

namespace Gate04Root

/-- A row of the divisor-relaxed graph. -/
structure GraphRow where
  r : ℤ
  m : ℤ
  k : ℤ
  mPrime : ℤ
  k_ne_zero : k ≠ 0
  mPrime_def : mPrime = m + k * r

namespace GraphRow

/-- The divisor-relaxed image of a row. -/
def divisorRow (g : GraphRow) : ℤ × ℤ × ℤ := (g.m, g.mPrime, g.k)

/-- `k` divides `m' - m`. -/
theorem k_dvd_mPrime_sub_m (g : GraphRow) : g.k ∣ g.mPrime - g.m :=
  ⟨g.r, by rw [g.mPrime_def]; ring⟩

/-- `r` is recovered from `(m, m', k)`. -/
theorem r_eq (g : GraphRow) : g.r = (g.mPrime - g.m) / g.k := by
  have h : g.mPrime - g.m = g.k * g.r := by rw [g.mPrime_def]; ring
  rw [h, Int.mul_ediv_cancel_left _ g.k_ne_zero]

/-- **Injectivity of the divisor-relaxed row map.** -/
theorem graphRow_to_divisorRow_injective : Function.Injective divisorRow := by
  rintro ⟨r₁, m₁, k₁, mp₁, hk₁, hd₁⟩ ⟨r₂, m₂, k₂, mp₂, hk₂, hd₂⟩ h
  simp only [divisorRow, Prod.mk.injEq] at h
  obtain ⟨hm, hmp, hk⟩ := h
  subst hm; subst hmp; subst hk
  have : k₁ * r₁ = k₁ * r₂ := by
    have := hd₁.symm.trans hd₂
    linarith
  have hr : r₁ = r₂ := by
    exact mul_left_cancel₀ hk₁ this
  subst hr
  rfl

end GraphRow

/-- `k` is *admissible* for the pair `(m, m')` if it is nonzero and occurs as the
jump of some row with these endpoints. -/
def AdmissibleK (m mPrime k : ℤ) : Prop := k ≠ 0 ∧ ∃ r : ℤ, mPrime = m + k * r

theorem admissibleK_dvd {m mPrime k : ℤ} (h : AdmissibleK m mPrime k) :
    k ∣ mPrime - m := by
  obtain ⟨_, r, hr⟩ := h
  exact ⟨r, by rw [hr]; ring⟩

/-- **Row cardinal interface.**  Any finite set of positive admissible jumps for a
fixed pair `(m, m')` with `m' ≠ m` injects into the divisors of `|m' - m|`. -/
theorem card_admissible_le_card_divisors {m mPrime : ℤ} (hne : mPrime ≠ m)
    (S : Finset ℤ) (hS : ∀ k ∈ S, 0 < k ∧ AdmissibleK m mPrime k) :
    S.card ≤ (Int.natAbs (mPrime - m)).divisors.card := by
  have hne' : (mPrime - m).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero, sub_eq_zero] using hne
  refine Finset.card_le_card_of_injOn (fun k => k.natAbs) ?_ ?_
  · intro k hk
    obtain ⟨hpos, hadm⟩ := hS k hk
    refine Nat.mem_divisors.mpr ⟨?_, hne'⟩
    exact Int.natAbs_dvd_natAbs.mpr (admissibleK_dvd hadm)
  · intro a ha b hb hab
    have hA := (hS a ha).1
    have hB := (hS b hb).1
    simp only at hab
    omega

/-- **EXTERNAL ANALYTIC INTERFACE (never assumed, never proved here).**
The divisor bound `τ(n) ≤ X^ε` for `n ≤ X`.  It is stated only so that later
analytic work has a fixed, named place to plug in. -/
def DivisorGrowthInterface (X eps : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X → ((n.divisors.card : ℝ)) ≤ X ^ eps

end Gate04Root
