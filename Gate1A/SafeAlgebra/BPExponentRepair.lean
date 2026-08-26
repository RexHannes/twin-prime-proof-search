/-
# Gate 1A — corrected BP exponent ledger (rational arithmetic only)

This file proves ONLY rational exponent arithmetic.
It does NOT prove the Gate-to-BP dictionary,
the Blomer–Pascadi estimate,
common-frame synthesis,
or Gate 1A closure.

All computations are exact over `ℚ`; no floating point, no real powers.
-/
import Mathlib

namespace Gate1A.SafeAlgebra

/-- The Heath-Brown/Gate normalisation parameter used throughout this ledger. -/
def mParam : ℚ := 1 / 3

/-- Gate dual-height exponents at the three vertices. -/
def h1 : ℚ := 5 / 18
def h2 : ℚ := 11 / 36
def h3 : ℚ := 7 / 24

/-- Corrected candidate amplitude exponent `σ(h, m) = h/16 − 5m/32`. -/
def sigmaExp (h m : ℚ) : ℚ := h / 16 - 5 * m / 32

/-- Energy exponent `ρ(h, m) = 2σ(h, m) = h/8 − 5m/16`. -/
def rhoExp (h m : ℚ) : ℚ := h / 8 - 5 * m / 16

/-- Required Gate exponent `τ(h, m) = h − m`. -/
def tauExp (h m : ℚ) : ℚ := h - m

theorem rhoExp_eq_two_mul_sigmaExp (h m : ℚ) : rhoExp h m = 2 * sigmaExp h m := by
  unfold rhoExp sigmaExp; ring

/-- Worst amplitude exponent at vertex 1. -/
theorem bp_vertex1_amplitude : sigmaExp h1 mParam = -5 / 144 := by
  unfold sigmaExp h1 mParam; norm_num

theorem bp_vertex1_energy : rhoExp h1 mParam = -5 / 72 := by
  unfold rhoExp h1 mParam; norm_num

theorem bp_vertex1_required : tauExp h1 mParam = -1 / 18 := by
  unfold tauExp h1 mParam; norm_num

theorem bp_vertex1_surplus : tauExp h1 mParam - rhoExp h1 mParam = 1 / 72 := by
  unfold tauExp rhoExp h1 mParam; norm_num

theorem bp_vertex2_energy : rhoExp h2 mParam = -19 / 288 := by
  unfold rhoExp h2 mParam; norm_num

theorem bp_vertex2_required : tauExp h2 mParam = -1 / 36 := by
  unfold tauExp h2 mParam; norm_num

theorem bp_vertex2_surplus : tauExp h2 mParam - rhoExp h2 mParam = 11 / 288 := by
  unfold tauExp rhoExp h2 mParam; norm_num

theorem bp_vertex3_energy : rhoExp h3 mParam = -13 / 192 := by
  unfold rhoExp h3 mParam; norm_num

theorem bp_vertex3_required : tauExp h3 mParam = -1 / 24 := by
  unfold tauExp h3 mParam; norm_num

theorem bp_vertex3_surplus : tauExp h3 mParam - rhoExp h3 mParam = 5 / 192 := by
  unfold tauExp rhoExp h3 mParam; norm_num

/-- **Worst energy surplus over the three vertices is `1/72`.** -/
theorem bp_worst_energy_surplus :
    min (min (1 / 72 : ℚ) (11 / 288)) (5 / 192) = 1 / 72 := by
  norm_num

/-- The same statement written directly in terms of the three vertex surpluses. -/
theorem bp_worstEnergyMargin :
    min (min (tauExp h1 mParam - rhoExp h1 mParam) (tauExp h2 mParam - rhoExp h2 mParam))
        (tauExp h3 mParam - rhoExp h3 mParam) = 1 / 72 := by
  rw [bp_vertex1_surplus, bp_vertex2_surplus, bp_vertex3_surplus]
  norm_num

/-- Amplitude-level tax corresponding to the squared-energy surplus: half of `1/72`. -/
theorem bp_amplitudeTaxMargin :
    (tauExp h1 mParam - rhoExp h1 mParam) / 2 = 1 / 144 := by
  rw [bp_vertex1_surplus]; norm_num

end Gate1A.SafeAlgebra
