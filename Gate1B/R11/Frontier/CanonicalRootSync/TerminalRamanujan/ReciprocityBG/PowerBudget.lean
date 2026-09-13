/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
power-budget arithmetic  (B9)

Append-only module.  **Exponent arithmetic only.**  Every statement here is a rational
inequality; none of them implies, or is intended to imply, any analytic theorem.  Nothing
pre-existing is edited.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.HighFrequencyOwner

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

/-! ## 1. The low-frequency exponent box -/

/-- The low-frequency cutoff exponent `1/40000` (the range of the external low-frequency
claim). -/
def bgLowExponent : ℚ := 1 / 40000

/-- The reserve exponent `1/20000` available to the consumer. -/
def bgReserveExponent : ℚ := 1 / 20000

/-- `1/40000 < 1/20000`. -/
theorem bgLowExponent_lt_reserve : bgLowExponent < bgReserveExponent := by
  unfold bgLowExponent bgReserveExponent; norm_num

/-- The net low-frequency reserve is exactly `1/40000`, and it is positive. -/
theorem bg_net_reserve :
    bgReserveExponent - bgLowExponent = 1 / 40000 ∧ (0 : ℚ) < bgReserveExponent - bgLowExponent := by
  unfold bgLowExponent bgReserveExponent
  constructor <;> norm_num

/-- The reciprocal-power weight of the `k₁ = k₂ = 4` call is `1/(2·4) = 1/8`, which leaves a
fixed positive gap above the low-frequency cutoff exponent.  **Exponent arithmetic only**: this
says nothing about the validity of any analytic estimate. -/
theorem k4_exponent_gap : (0 : ℚ) < 1 / 8 - bgLowExponent := by
  unfold bgLowExponent; norm_num

/-- Both `k₁ = k₂ = 4` reciprocal weights are equal and positive. -/
theorem k4_weights : (1 : ℚ) / (2 * 4) = 1 / 8 ∧ (0 : ℚ) < 1 / 8 := by
  constructor <;> norm_num

/-! ## 2. Consistency with the previously banked wedge arithmetic -/

/-- The banked tiny-wedge inequality `206μ + 274θ < 1` at the recorded feasible point
`μ = 1/400`, `θ = 1/10000`, with the exact value `0.5424`. -/
theorem wedge_point_feasible :
    206 * ((1 : ℚ) / 400) + 274 * ((1 : ℚ) / 10000) = 5424 / 10000
      ∧ 206 * ((1 : ℚ) / 400) + 274 * ((1 : ℚ) / 10000) < 1 := by
  constructor <;> norm_num

/-! ## 3. Firewall: exponent arithmetic proves no analytic bound -/

/-- **No analytic conclusion follows from the exponent arithmetic.**  All the rational
inequalities above hold, and the low-frequency analytic owner is still not a theorem. -/
theorem power_budget_does_not_close_owner :
    bgLowExponent < bgReserveExponent ∧ (0 : ℚ) < 1 / 8 - bgLowExponent
      ∧ ∃ D : DualData, ¬ LowDualBourgainGaraevBound D 0 :=
  ⟨bgLowExponent_lt_reserve, k4_exponent_gap, lowDualBourgainGaraevBound_open⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
