import Mathlib

/-!
# Ford–Maynard positivity window (§11)

`FORD_MAYNARD_POSITIVITY_WINDOW`.

Interface recording the Ford–Maynard prime-producing sieve positivity data at
`(γ, θ) = (1/2, 0)`:

* `ν ≥ 0.1663 ⟹ C⁻ > 0` (positive lower bound);
* `ν = 0.1616 ⟹ C⁻ = 0` (no positivity);
* `ν ≥ 1/3` in the asymptotic regime.

The *certified positivity threshold* is only known to lie in the interval
`[0.1616, 0.1663]`; `0.1663` is **not** claimed as the exact threshold.

The numerical facts banked here are the ordering relations of the window
endpoints (`LEAN_PROVED`).  The sieve implication itself is a
`LITERATURE_VERIFIED` interface, recorded as the `FordMaynardWindow` structure.
-/

namespace PrimeShortWindow.FordMaynard

/-- Interface recording the Ford–Maynard positivity data at fixed `(γ, θ)`.
`positivityThreshold` is the value `≥ 0.1663` guaranteeing `C⁻ > 0`;
`zeroThreshold` is the value `0.1616` at which `C⁻ = 0`;
`asymptoticThreshold` is `1/3`. -/
structure FordMaynardWindow where
  γ : ℝ
  θ : ℝ
  /-- Value guaranteeing positivity `C⁻ > 0`. -/
  positivityThreshold : ℝ
  /-- Value at which `C⁻ = 0`. -/
  zeroThreshold : ℝ
  /-- Asymptotic-regime threshold `1/3`. -/
  asymptoticThreshold : ℝ

/-- The banked Ford–Maynard window at `(γ, θ) = (1/2, 0)`. -/
noncomputable def fordMaynardHalfZero : FordMaynardWindow where
  γ := 1 / 2
  θ := 0
  positivityThreshold := 0.1663
  zeroThreshold := 0.1616
  asymptoticThreshold := 1 / 3

/-- The certified positivity threshold is only pinned to the interval
`[0.1616, 0.1663]`. -/
noncomputable def certifiedWindow : Set ℝ := Set.Icc 0.1616 0.1663

/-- The window is a genuine (nonempty) interval: the zero threshold is strictly
below the positivity threshold. -/
theorem zero_lt_positivity : (0.1616 : ℝ) < 0.1663 := by norm_num

/-- The positivity threshold is strictly below the asymptotic threshold `1/3`. -/
theorem positivity_lt_asymptotic : (0.1663 : ℝ) < 1 / 3 := by norm_num

/-- The certified positivity window `[0.1616, 0.1663]` is nonempty. -/
theorem certifiedWindow_nonempty : certifiedWindow.Nonempty :=
  ⟨0.1616, by constructor <;> norm_num⟩

/-- `0.1663` is only the *upper* end of the certified window, not proven to be
the exact threshold: it lies strictly above the known-zero value `0.1616`. -/
theorem threshold_not_exact :
    (0.1616 : ℝ) ∈ certifiedWindow ∧ (0.1663 : ℝ) ∈ certifiedWindow ∧
      (0.1616 : ℝ) ≠ 0.1663 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by norm_num⟩

end PrimeShortWindow.FordMaynard
