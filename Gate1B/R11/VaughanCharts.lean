/-
# Gate1B / R11 : the Vaughan chart, its `V* = 2` specialization, and chart equivalence

Everything in this file is an **exact identity** between arithmetic functions or between
their pointwise values.  There is no estimate, no asymptotic, and no claim that one chart
is analytically easier than another.

Contents.

* `truncLE` / `truncGT`: the two cutoff truncations of an arithmetic function, and the
  tautological decomposition `f = truncLE U f + truncGT U f`.
* `vaughan_identity`: the four-lane Vaughan identity

  ```
  Λ = Λ_{≤V} + μ_{≤U} * log − μ_{≤U} * Λ_{≤V} * ζ + μ_{>U} * Λ_{>V} * ζ
  ```

  as an identity in the commutative ring `ArithmeticFunction ℝ`.
* the `V* = 2` specialization on odd arguments: lanes 1 and 3 vanish, lane 2 is the low
  Möbius–log sum and lane 4 is the long Möbius–log sum.
* `fourLaneValue_eq_longMobiusValue`: the two charts agree *literally* at `V = 2` on odd
  arguments — no mass is lost in either direction.
-/
import Gate1B.R11.LongMobius

namespace Gate1B.R11

open Finset ArithmeticFunction

noncomputable section

/-! ## 1. Cutoff truncations -/

/-- Low truncation: `f` restricted to arguments `≤ U`. -/
def truncLE (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- High truncation: `f` restricted to arguments `> U`. -/
def truncGT (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] theorem truncLE_apply (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    truncLE U f n = if n ≤ U then f n else 0 := rfl

@[simp] theorem truncGT_apply (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    truncGT U f n = if U < n then f n else 0 := rfl

/-- The cutoff decomposition is exact: nothing is lost at the cut. -/
theorem truncLE_add_truncGT (U : ℕ) (f : ArithmeticFunction ℝ) :
    truncLE U f + truncGT U f = f := by
  ext n
  simp only [ArithmeticFunction.add_apply, truncLE_apply, truncGT_apply]
  by_cases h : n ≤ U
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

/-! ## 2. The four-lane Vaughan identity -/

/-- The Möbius function as a real-valued arithmetic function. -/
def muR : ArithmeticFunction ℝ := (moebius : ArithmeticFunction ℝ)

/-- The constant-one arithmetic function (`ζ`) as a real-valued arithmetic function. -/
def zetaR : ArithmeticFunction ℝ := (zeta : ArithmeticFunction ℝ)

/-- **Vaughan's identity, four-lane form (exact).**

`Λ = Λ_{≤V} + μ_{≤U}*log − μ_{≤U}*Λ_{≤V}*ζ + μ_{>U}*Λ_{>V}*ζ` in `ArithmeticFunction ℝ`. -/
theorem vaughan_identity (U V : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ)
      = truncLE V vonMangoldt
        + truncLE U muR * ArithmeticFunction.log
        - truncLE U muR * truncLE V vonMangoldt * zetaR
        + truncGT U muR * truncGT V vonMangoldt * zetaR := by
  have h1 : muR * zetaR = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have h2 : (vonMangoldt : ArithmeticFunction ℝ) * zetaR = ArithmeticFunction.log :=
    ArithmeticFunction.vonMangoldt_mul_zeta
  have h3 : truncLE U muR + truncGT U muR = muR := truncLE_add_truncGT U muR
  have h4 : truncLE V vonMangoldt + truncGT V vonMangoldt = vonMangoldt :=
    truncLE_add_truncGT V vonMangoldt
  linear_combination (truncLE U muR) * h2 - (truncGT V vonMangoldt) * h1
    - (truncGT V vonMangoldt * zetaR) * h3 + (truncLE U muR * zetaR - 1) * h4

/-! ## 3. Vanishing lemmas on odd arguments -/

/-- If `g` vanishes on every odd number, then `(f * g)` vanishes on every odd number:
in the convolution every second factor divides the odd argument, hence is odd. -/
theorem mul_apply_eq_zero_of_odd {N : ℕ} (hN : Odd N) (f g : ArithmeticFunction ℝ)
    (hg : ∀ m : ℕ, Odd m → g m = 0) : (f * g) N = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have hdvd : x.2 ∣ N := ⟨x.1, by rw [← hx.1]; ring⟩
  rw [hg x.2 (odd_of_dvd_odd hN hdvd), mul_zero]

/-- **Lane 1 at `V* = 2` vanishes on odd arguments.**  The only odd `n ≤ 2` is `n = 1`,
where `Λ` vanishes. -/
theorem truncLE_two_vonMangoldt_odd {N : ℕ} (hN : Odd N) :
    truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) N = 0 := by
  rw [truncLE_apply]
  by_cases h : N ≤ 2
  · have hN1 : N = 1 := by
      rcases hN with ⟨k, hk⟩
      omega
    simp [hN1]
  · simp [h]

/-- **Lane 3 at `V* = 2` vanishes on odd arguments.** -/
theorem lane_three_two_eq_zero {N : ℕ} (hN : Odd N) (U : ℕ) :
    (truncLE U muR * truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR) N = 0 := by
  have hcomm : truncLE U muR * truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR
      = (truncLE U muR * zetaR) * truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) := by
    ring
  rw [hcomm]
  exact mul_apply_eq_zero_of_odd hN _ _ fun m hm => truncLE_two_vonMangoldt_odd hm

/-- **`(Λ_{>2} * ζ)(N) = log N` for odd `N`.** -/
theorem truncGT_two_vonMangoldt_mul_zeta_odd {N : ℕ} (hN : Odd N) :
    (truncGT 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR) N = Real.log N := by
  have hsplit : (truncLE 2 (vonMangoldt : ArithmeticFunction ℝ)
      + truncGT 2 (vonMangoldt : ArithmeticFunction ℝ)) * zetaR
        = (vonMangoldt : ArithmeticFunction ℝ) * zetaR := by
    rw [truncLE_add_truncGT]
  have hlow : (truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR) N = 0 := by
    have hcomm : truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR
        = zetaR * truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) := by ring
    rw [hcomm]
    exact mul_apply_eq_zero_of_odd hN _ _ fun m hm => truncLE_two_vonMangoldt_odd hm
  have := congrArg (fun f => f N) hsplit
  simp only [add_mul, ArithmeticFunction.add_apply, hlow, zero_add] at this
  rw [this]
  simp only [zetaR]
  rw [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply]

/-! ## 4. The two surviving lanes are exactly the Möbius–log pieces -/

/-- **Lane 2 is the low Möbius–log sum**, for every `N ≠ 0` (no parity needed). -/
theorem lane_two_eq_lowMobiusLog (N U : ℕ) :
    (truncLE U muR * ArithmeticFunction.log) N = lowMobiusLog U N := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => truncLE U muR a * ArithmeticFunction.log b),
    lowMobiusLog, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : d ≤ U <;> simp [h, truncLE_apply, muR, ArithmeticFunction.log_apply]

/-- **Lane 4 at `V* = 2` is the long Möbius–log sum**, for odd `N`. -/
theorem lane_four_eq_longMobiusLog {N : ℕ} (hN : Odd N) (U : ℕ) :
    (truncGT U muR * truncGT 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR) N
      = longMobiusLog U N := by
  have hassoc : truncGT U muR * truncGT 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR
      = truncGT U muR * (truncGT 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR) := by ring
  rw [hassoc, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b => truncGT U muR a * (truncGT 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR) b),
    longMobiusLog, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mem_divisors] at hd
  have hodd : Odd (N / d) := odd_of_dvd_odd hN (Nat.div_dvd_of_dvd hd.1)
  rw [truncGT_two_vonMangoldt_mul_zeta_odd hodd]
  by_cases h : U < d <;> simp [h, truncGT_apply, muR]

/-! ## 5. The `V* = 2` Möbius–log compiler -/

/-- **`V* = 2` Vaughan compiler (exact).**  For odd `N`, the four-lane Vaughan chart at
`V = 2` collapses to the two-term Möbius–log split at the cutoff `U`:

`Λ(N) = ∑_{d ∣ N, d ≤ U} μ(d) log(N/d) + ∑_{d ∣ N, d > U} μ(d) log(N/d)`. -/
theorem vTwo_vaughan_eq_mobius_log_split {N : ℕ} (hN : Odd N) (U : ℕ) :
    vonMangoldt N
      = (∑ d ∈ N.divisors.filter (fun d => d ≤ U), (moebius d : ℝ) * Real.log ((N / d : ℕ) : ℝ))
        + ∑ d ∈ N.divisors.filter (fun d => U < d),
            (moebius d : ℝ) * Real.log ((N / d : ℕ) : ℝ) := by
  have hsub : ∀ (f g : ArithmeticFunction ℝ) (m : ℕ), (f - g) m = f m - g m := fun _ _ _ => rfl
  have h := congrArg (fun f => f N) (vaughan_identity U 2)
  simp only [ArithmeticFunction.add_apply, hsub] at h
  rw [truncLE_two_vonMangoldt_odd hN, lane_three_two_eq_zero hN U,
    lane_two_eq_lowMobiusLog N U, lane_four_eq_longMobiusLog hN U] at h
  simpa [lowMobiusLog, longMobiusLog] using h

/-! ## 6. Chart equivalence -/

/-- The value of the four-lane Vaughan chart with parameters `U, V` at `N`. -/
def FourLaneValue (U V N : ℕ) : ℝ :=
  (truncLE V vonMangoldt
    + truncLE U muR * ArithmeticFunction.log
    - truncLE U muR * truncLE V vonMangoldt * zetaR
    + truncGT U muR * truncGT V vonMangoldt * zetaR) N

/-- The value of the long-Möbius chart with cutoff `U` at `N`: the low Möbius–log block
plus the long Möbius–log block. -/
def LongMobiusValue (U N : ℕ) : ℝ := lowMobiusLog U N + longMobiusLog U N

/-- The four-lane chart computes `Λ` exactly, for every `U, V, N`. -/
theorem fourLaneValue_eq_vonMangoldt (U V N : ℕ) : FourLaneValue U V N = vonMangoldt N := by
  rw [FourLaneValue, ← congrArg (fun f => f N) (vaughan_identity U V)]

/-- The long-Möbius chart computes `Λ` exactly, for every `U, N`. -/
theorem longMobiusValue_eq_vonMangoldt (U N : ℕ) : LongMobiusValue U N = vonMangoldt N :=
  (vonMangoldt_split U N).symm

/-- **Chart equivalence (literal equality, not an estimate).**  On odd arguments the
four-lane Vaughan chart at `V = 2` and the long-Möbius chart carry exactly the same value.
Both are equal to `Λ(N)`, so no source mass is lost in either direction. -/
theorem fourLaneValue_eq_longMobiusValue (U N : ℕ) :
    FourLaneValue U 2 N = LongMobiusValue U N := by
  rw [fourLaneValue_eq_vonMangoldt, longMobiusValue_eq_vonMangoldt]

/-- **No mass lost, lane by lane, at `V* = 2` on odd arguments.**  Lane 1 and lane 3 are
zero, lane 2 is the low block and lane 4 is the long block. -/
theorem vTwo_lane_ledger {N : ℕ} (hN : Odd N) (U : ℕ) :
    truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) N = 0
      ∧ (truncLE U muR * truncLE 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR) N = 0
      ∧ (truncLE U muR * ArithmeticFunction.log) N = lowMobiusLog U N
      ∧ (truncGT U muR * truncGT 2 (vonMangoldt : ArithmeticFunction ℝ) * zetaR) N
          = longMobiusLog U N :=
  ⟨truncLE_two_vonMangoldt_odd hN, lane_three_two_eq_zero hN U,
    lane_two_eq_lowMobiusLog N U, lane_four_eq_longMobiusLog hN U⟩

end

end Gate1B.R11
