/-
# NANC Gate 1A v9 — maximal amplifier budget arithmetic (exact identities)

With a free parameter `Z ≥ 1`,

    AmpLen             = M² · Z,
    amplifierPrefactor = L·M / AmpLen²  =  L / (M³ Z²),
    DTarget            = H·L²·M³·Z²,
    DDiag              = H·L²·M³·Z,

so that `amplifierPrefactor · DTarget = H·L³` and `DDiag / DTarget = 1/Z`.
Specialising to the maximal choice `Z = L/M` gives `AmpLen = L·M`,
`amplifierPrefactor = 1/(L·M)`, `DTarget = H·M·L⁴`, `DDiag = H·M²·L³`, and the
spare-factor identity `(M/L)·(L/M) = 1`.

**FIREWALL.**  This is budget algebra.  A budget identity is not an
amplifier-family cancellation.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

/-- Amplifier length. -/
def ampLen (M Z : ℝ) : ℝ := M ^ 2 * Z

/-- Amplifier prefactor `L·M / AmpLen²`. -/
noncomputable def amplifierPrefactor (L M Z : ℝ) : ℝ := L * M / (ampLen M Z) ^ 2

/-- Target second moment. -/
def dTarget (H L M Z : ℝ) : ℝ := H * L ^ 2 * M ^ 3 * Z ^ 2

/-- Diagonal second moment. -/
def dDiag (H L M Z : ℝ) : ℝ := H * L ^ 2 * M ^ 3 * Z

/-- The prefactor in closed form. -/
theorem amplifierPrefactor_eq (L M Z : ℝ) (hM : M ≠ 0) (hZ : Z ≠ 0) :
    amplifierPrefactor L M Z = L / (M ^ 3 * Z ^ 2) := by
  unfold amplifierPrefactor ampLen
  field_simp

/-- **General budget identity.**  Prefactor times target is exactly `H·L³`. -/
theorem amplifier_budget_general (H L M Z : ℝ) (hM : M ≠ 0) (hZ : Z ≠ 0) :
    amplifierPrefactor L M Z * dTarget H L M Z = H * L ^ 3 := by
  rw [amplifierPrefactor_eq L M Z hM hZ]
  unfold dTarget
  field_simp

/-- **Diagonal-to-target ratio** is exactly `1/Z`. -/
theorem amplifier_diag_ratio (H L M Z : ℝ) (hH : H ≠ 0) (hL : L ≠ 0) (hM : M ≠ 0)
    (hZ : Z ≠ 0) :
    dDiag H L M Z / dTarget H L M Z = 1 / Z := by
  unfold dDiag dTarget
  field_simp

/-- **Maximal amplifier.**  With `Z = L/M` the four budget quantities take the
maximal-amplifier values. -/
theorem amplifier_budget_maximal (H L M : ℝ) (hL : L ≠ 0) (hM : M ≠ 0) :
    ampLen M (L / M) = L * M ∧
    amplifierPrefactor L M (L / M) = 1 / (L * M) ∧
    dTarget H L M (L / M) = H * M * L ^ 4 ∧
    dDiag H L M (L / M) = H * M ^ 2 * L ^ 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ampLen; field_simp
  · unfold amplifierPrefactor ampLen; field_simp
  · unfold dTarget; field_simp
  · unfold dDiag; field_simp

/-- **Spare factor pays the family tax.**  `(M/L)·(L/M) = 1`. -/
theorem amplifier_spare_pays_familyTax_identity (L M : ℝ) (hL : L ≠ 0) (hM : M ≠ 0) :
    (M / L) * (L / M) = 1 := by
  field_simp

end TwinPrimeProject.NANC.Gate1A.V9
