/-
# Gate 1B safe extension — the physical-splice abstract budget theorem

Purely abstract ordered-field implications between nonnegative real quantities

    A2, B2, E_AK, U_mass, V_mass, X_mass, spectralFactor, savingFactor,
    physicalTarget.

**The analytic AK estimate is an INPUT.**  The hypothesis

    E_AK ≤ spectralFactor * U_mass * B2

is supplied from outside; nothing in this file proves it, and no `X^{o(1)}`
factor is hard-coded anywhere.
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- **Physical splice from a supplied AK bound.**  Given the mass ledger
`A2 ≤ U_mass`, `B2 ≤ V_mass`, `U_mass · V_mass ≤ X_mass`, the *externally
supplied* bound `E_AK ≤ spectralFactor · U_mass · B2` and
`spectralFactor ≤ savingFactor`, one gets `E_AK ≤ savingFactor · X_mass`. -/
theorem akPhysicalSplice_of_suppliedBound
    (B2 E_AK U_mass V_mass X_mass spectralFactor savingFactor : ℝ)
    (hB2 : 0 ≤ B2) (hU : 0 ≤ U_mass) (hsave : 0 ≤ savingFactor)
    (hB2V : B2 ≤ V_mass) (hUV : U_mass * V_mass ≤ X_mass)
    (hAK : E_AK ≤ spectralFactor * U_mass * B2)
    (hspec : spectralFactor ≤ savingFactor) :
    E_AK ≤ savingFactor * X_mass := by
  have h1 : spectralFactor * U_mass * B2 ≤ savingFactor * U_mass * B2 := by
    have := mul_le_mul_of_nonneg_right hspec hU
    exact mul_le_mul_of_nonneg_right this hB2
  have h2 : savingFactor * U_mass * B2 ≤ savingFactor * U_mass * V_mass := by
    exact mul_le_mul_of_nonneg_left hB2V (by positivity)
  have h3 : savingFactor * U_mass * V_mass ≤ savingFactor * X_mass := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hUV hsave
  linarith

/-- The budget form: the same chain, stated against an abstract
`physicalTarget`, and combined with the source mass ledger `A2 ≤ U_mass`. -/
theorem akPhysicalSpliceBudget
    (A2 B2 E_AK U_mass V_mass X_mass spectralFactor savingFactor physicalTarget : ℝ)
    (hB2 : 0 ≤ B2) (hU : 0 ≤ U_mass) (hsave : 0 ≤ savingFactor) (hEnn : 0 ≤ E_AK)
    (hA2 : A2 ≤ U_mass) (hB2V : B2 ≤ V_mass) (hUV : U_mass * V_mass ≤ X_mass)
    (hAK : E_AK ≤ spectralFactor * U_mass * B2)
    (hspec : spectralFactor ≤ savingFactor)
    (hmargin : savingFactor * X_mass ≤ physicalTarget) :
    A2 * E_AK ≤ U_mass * physicalTarget := by
  have hE : E_AK ≤ physicalTarget :=
    le_trans (akPhysicalSplice_of_suppliedBound B2 E_AK U_mass V_mass X_mass
      spectralFactor savingFactor hB2 hU hsave hB2V hUV hAK hspec) hmargin
  calc A2 * E_AK ≤ U_mass * E_AK := mul_le_mul_of_nonneg_right hA2 hEnn
    _ ≤ U_mass * physicalTarget := mul_le_mul_of_nonneg_left hE hU

/-- **Closure of the splice given a margin.**  Combining the abstract budget
with the outer Cauchy step: if the amplitude square is bounded by `A2 · E_AK`
and `A2 ≤ U_mass` with the supplied AK bound and margin, then the amplitude
square meets `U_mass · physicalTarget`.  Still no analytic content. -/
theorem akPhysicalSplice_closes_of_margin
    (P2 A2 B2 E_AK U_mass V_mass X_mass spectralFactor savingFactor physicalTarget : ℝ)
    (hB2 : 0 ≤ B2) (hU : 0 ≤ U_mass) (hsave : 0 ≤ savingFactor) (hEnn : 0 ≤ E_AK)
    (hP2 : P2 ≤ A2 * E_AK)
    (hA2 : A2 ≤ U_mass) (hB2V : B2 ≤ V_mass) (hUV : U_mass * V_mass ≤ X_mass)
    (hAK : E_AK ≤ spectralFactor * U_mass * B2)
    (hspec : spectralFactor ≤ savingFactor)
    (hmargin : savingFactor * X_mass ≤ physicalTarget) :
    P2 ≤ U_mass * physicalTarget :=
  hP2.trans (akPhysicalSpliceBudget A2 B2 E_AK U_mass V_mass X_mass spectralFactor
    savingFactor physicalTarget hB2 hU hsave hEnn hA2 hB2V hUV hAK hspec hmargin)

end Gate1B.SafeExtensions
