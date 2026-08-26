import Gate04Root.Rows
import RequestProject.NANC.Gate01Root.RootCollisions

/-!
# Gate01Root: divisor-relaxed rows

The projection `(r, m, k) ↦ (m, m', k)` with `m' = m + k r` is injective when
`k ≠ 0` (because `r = (m' - m)/k`), every admissible `k` divides `m' - m`, and a
finite set of positive admissible `k`'s injects into the divisors of `|m' - m|`.

The analytic divisor estimate `τ(n) = X^{o(1)}` is **not** formalised; it appears
only as the named external interface `Gate04Root.DivisorGrowthInterface`, which is
never assumed here.
-/

namespace RouteAFibreFrame
namespace Gate01Root

/-- A divisor-relaxed graph row. -/
abbrev GraphRow := Gate04Root.GraphRow

/-- The divisor-relaxed projection `(r, m, k) ↦ (m, m', k)`. -/
def divisorRow (g : GraphRow) : ℤ × ℤ × ℤ := Gate04Root.GraphRow.divisorRow g

/-- **Injectivity of the divisor-relaxed row map.** -/
theorem graphRow_to_divisorRow_injective : Function.Injective divisorRow :=
  Gate04Root.GraphRow.graphRow_to_divisorRow_injective

/-- **Every projected `k` divides `m' - m`.** -/
theorem graphRow_k_dvd_difference (g : GraphRow) : g.k ∣ g.mPrime - g.m :=
  Gate04Root.GraphRow.k_dvd_mPrime_sub_m g

/-- `r` is recovered from the projected data. -/
theorem graphRow_r_eq (g : GraphRow) : g.r = (g.mPrime - g.m) / g.k :=
  Gate04Root.GraphRow.r_eq g

/-- Admissibility of a jump `k` for a fixed pair `(m, m')`. -/
def AdmissibleK (m mPrime k : ℤ) : Prop := Gate04Root.AdmissibleK m mPrime k

/-- **Cardinal interface.**  A finite set of positive admissible jumps injects
into the divisors of `|m' - m|`. -/
theorem admissibleK_card_le_divisors_card {m mPrime : ℤ} (hne : mPrime ≠ m)
    (S : Finset ℤ) (hS : ∀ k ∈ S, 0 < k ∧ AdmissibleK m mPrime k) :
    S.card ≤ (Int.natAbs (mPrime - m)).divisors.card :=
  Gate04Root.card_admissible_le_card_divisors hne S hS

/-- **EXTERNAL ANALYTIC INTERFACE** (never assumed, never proved): the divisor
bound `τ(n) ≤ X^ε` for `n ≤ X`. -/
abbrev DivisorGrowthInterface (X eps : ℝ) : Prop := Gate04Root.DivisorGrowthInterface X eps

end Gate01Root
end RouteAFibreFrame
