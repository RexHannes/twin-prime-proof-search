/-
# Gate1B / R11 : Möbius–log divisor split (§8)

Elementary, unconditional material only:

* the pointwise divisor-sum form of `Λ = μ * log`;
* the tautological split of that divisor sum at an arbitrary cutoff `U`;
* the `V* = 2` support observation, in the *explicitly stated* truncated convention.

No Type-II identity, no analytic content, no marketing.
-/
import Gate1B.R11.CanonicalSource

namespace Gate1B.R11

open Finset ArithmeticFunction

/-! ## 1. Pointwise Möbius–log identity -/

/-- `Λ(N) = ∑_{d ∣ N} μ(d) log(N/d)`, the pointwise form of `Λ = μ * log`. -/
theorem vonMangoldt_eq_sum_moebius_mul_log (N : ℕ) :
    vonMangoldt N = ∑ d ∈ N.divisors, (moebius d : ℝ) * Real.log ((N / d : ℕ) : ℝ) := by
  have h := congrArg (fun f => f N) ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  simp only [ArithmeticFunction.mul_apply] at h
  rw [← h, Nat.sum_divisorsAntidiagonal
      (fun x y => ((↑moebius : ArithmeticFunction ℝ) x) * ArithmeticFunction.log y)]
  simp [ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply]

/-! ## 2. The tautological cutoff split -/

/-- The low (`d ≤ U`) part of the Möbius–log divisor sum. -/
noncomputable def lowMobiusLog (U N : ℕ) : ℝ :=
  ∑ d ∈ N.divisors.filter (fun d => d ≤ U), (moebius d : ℝ) * Real.log ((N / d : ℕ) : ℝ)

/-- The long (`d > U`) part of the Möbius–log divisor sum. -/
noncomputable def longMobiusLog (U N : ℕ) : ℝ :=
  ∑ d ∈ N.divisors.filter (fun d => U < d), (moebius d : ℝ) * Real.log ((N / d : ℕ) : ℝ)

/-- **Möbius–log divisor split.**  For every cutoff `U`, `Λ(N)` is exactly the low part plus
the long part.  Tautological (a partition of the divisor set), hence unconditional. -/
theorem vonMangoldt_split (U N : ℕ) :
    vonMangoldt N = lowMobiusLog U N + longMobiusLog U N := by
  rw [vonMangoldt_eq_sum_moebius_mul_log, lowMobiusLog, longMobiusLog]
  rw [← Finset.sum_filter_add_sum_filter_not N.divisors (fun d => d ≤ U)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun d _ => ?_) fun _ _ => rfl
  constructor <;> intro h <;> omega

/-- The long part is exactly the defect of the low part from `Λ`. -/
theorem longMobiusLog_eq_sub (U N : ℕ) :
    longMobiusLog U N = vonMangoldt N - lowMobiusLog U N := by
  rw [vonMangoldt_split U N]; ring

/-! ## 3. The `V* = 2` support observation

The convention is stated explicitly: `vonMangoldtTrunc V N` is the part of `∑_{d ∣ N} Λ(d)`
carried by divisors `d ≤ V`.  For `V = 2` the only possible contribution is the integer `2`
itself, so the truncation vanishes on odd `N`. -/

/-- Truncated von Mangoldt divisor sum: only divisors `d ≤ V` contribute. -/
noncomputable def vonMangoldtTrunc (V N : ℕ) : ℝ :=
  ∑ d ∈ N.divisors.filter (fun d => d ≤ V), vonMangoldt d

/-- Every divisor of an odd number is odd. -/
theorem odd_of_dvd_odd {N d : ℕ} (hN : Odd N) (hd : d ∣ N) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · have h2 : (2 : ℕ) ∣ N := dvd_trans he.two_dvd hd
    exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hN)
  · exact ho

/-- For odd `N ≠ 0`, the divisors `d ≤ 2` are exactly `{1}`. -/
theorem divisors_filter_le_two_of_odd {N : ℕ} (hN0 : N ≠ 0) (hN : Odd N) :
    N.divisors.filter (fun d => d ≤ 2) = {1} := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, -⟩, hle⟩
    have hodd : Odd d := odd_of_dvd_odd hN hd
    interval_cases d
    · exact absurd (Nat.eq_zero_of_zero_dvd hd) hN0
    · rfl
    · exact absurd hodd (by decide)
  · rintro rfl
    exact ⟨⟨one_dvd N, hN0⟩, by norm_num⟩

/-- **`V* = 2` support observation.**  In the stated truncated convention, the `V ≤ 2`
truncated von Mangoldt sum vanishes on odd arguments. -/
theorem vonMangoldtTrunc_two_eq_zero_of_odd {N : ℕ} (hN0 : N ≠ 0) (hN : Odd N) :
    vonMangoldtTrunc 2 N = 0 := by
  rw [vonMangoldtTrunc, divisors_filter_le_two_of_odd hN0 hN]
  simp

end Gate1B.R11
