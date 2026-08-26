import RequestProject.NANC.HPoissonComplementaryDivisor.ExponentGeometry
import RequestProject.NANC.HPoissonComplementaryDivisor.CenteringCore

/-!
# HPoissonComplementaryDivisor, Module 6: analytic interfaces and conditional arithmetic

Every analytic statement of the switched `r = 9`, `4|5` h-Poisson bridge is
represented here as a **named predicate**.  None of them is an axiom and none
of them is ever inhabited in this development:

* `SmoothPoissonIdentity`
* `SourceCenteringMatch`
* `NonCoprimeStrataNegligible`
* `CenteredIncidenceVariance`
* `GlobalSwitchedReassembly`
* `D2D3CoefficientDictionary`
* `FullTypeII`

What *is* proved: pure exponent arithmetic, and implications that carry their
analytic hypotheses explicitly.  In particular the `T_A` target exponent
`23/9 − 2δ` is proved **CONDITIONAL ON THE SOURCE NORMALIZATION**
`|S₄|² ≤ U · T_A / H₀`; it is *not* an unconditional Gate-1B theorem, and
`no_unconditional_TA_target` records that the normalization hypothesis cannot
be dropped.
-/

namespace TwinPrimeProject
namespace HPoissonCD

open Real

/-! ## 1. Explicit analytic interfaces (never inhabited) -/

/-- **INTERFACE.**  Poisson summation with the actual smooth source weight:
the `y`-sum equals the dual `h`-sum up to `tol`.  Not proved here. -/
def SmoothPoissonIdentity (spatialSum dualSum tol : ℝ) : Prop :=
  |spatialSum - dualSum| ≤ tol

/-- **INTERFACE.**  The source expected term coincides with the centering term
`1/q` up to `tol`.  Not proved here; see `CenteringCore` for why the two are
different objects. -/
def SourceCenteringMatch (sourceExpected centeringTerm tol : ℝ) : Prop :=
  |sourceExpected - centeringTerm| ≤ tol

/-- **INTERFACE.**  The non-coprime `(q₁, q₂) > 1` strata are negligible. -/
def NonCoprimeStrataNegligible (strataMass bound : ℝ) : Prop := |strataMass| ≤ bound

/-- **INTERFACE.**  The centered incidence variance bound. -/
def CenteredIncidenceVariance (variance target : ℝ) : Prop := variance ≤ target

/-- **INTERFACE.**  Global reassembly of the switched pieces. -/
def GlobalSwitchedReassembly (assembledTotal piecesTotal tol : ℝ) : Prop :=
  |assembledTotal - piecesTotal| ≤ tol

/-- **INTERFACE.**  The claim that the shifted equation is a genuine
`d₂ × d₃` divisor correlation, i.e. that the source prime-product /
Möbius–Λ coefficients equal divisor coefficients up to `tol`.  Not proved. -/
def D2D3CoefficientDictionary (sourceCoeff divisorCoeff tol : ℝ) : Prop :=
  |sourceCoeff - divisorCoeff| ≤ tol

/-- **INTERFACE.**  The full Type-II bound `|B| ≤ X^(1−δ)`. -/
def FullTypeII (typeIISum X delta : ℝ) : Prop := |typeIISum| ≤ X ^ (1 - delta)

/-! ## 2. Conditional target-exponent arithmetic -/

/-- Rational form of the target-exponent computation:
`exp(U) + (23/9 − 2δ) − exp(H₀) = 2 − 2δ`.  Pure `ℚ` arithmetic. -/
theorem TA_target_exponent_arith (delta : ℚ) :
    expU + (23 / 9 - 2 * delta) - expH0 = 2 - 2 * delta := by
  simp only [expU, expH0]; ring

/-- The `T_A` target exponent solving `exp(U) + t − exp(H₀) = 2 − 2δ`
is exactly `t = 23/9 − 2δ`, and it is unique. -/
theorem TA_target_exponent_unique (delta t : ℚ) :
    (expU + t - expH0 = 2 - 2 * delta) ↔ t = 23 / 9 - 2 * delta := by
  simp only [expU, expH0]
  constructor <;> intro h <;> linarith

/-- **CONDITIONAL ON THE SOURCE NORMALIZATION.**

If the source normalization gives `|S₄|² ≤ U · T_A / H₀` with `U = X^(4/9)`,
`H₀ = X`, and if `T_A ≤ X^(23/9 − 2δ)`, then `|S₄|² ≤ X^(2 − 2δ)`, i.e. the
desired bound `|S₄| ≤ X^(1−δ)`.

The hypothesis `hnorm` is the source normalization interface; this is **not**
an unconditional Gate-1B statement. -/
theorem S4_sq_bound_of_TA_bound_conditional
    {X S4sq U TA H0 delta : ℝ} (hX : 1 ≤ X)
    (hU : U = X ^ ((4 : ℝ) / 9)) (hH0 : H0 = X)
    (hnorm : S4sq ≤ U * TA / H0)
    (hTA : TA ≤ X ^ ((23 : ℝ) / 9 - 2 * delta)) :
    S4sq ≤ X ^ (2 - 2 * delta) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have hUpos : 0 ≤ U := by rw [hU]; positivity
  have hH0pos : 0 < H0 := by rw [hH0]; exact hX0
  have step : U * TA / H0 ≤ U * X ^ ((23 : ℝ) / 9 - 2 * delta) / H0 := by
    gcongr
  have hexp : (4 : ℝ) / 9 + ((23 : ℝ) / 9 - 2 * delta) = (2 - 2 * delta) + 1 := by ring
  have final : U * X ^ ((23 : ℝ) / 9 - 2 * delta) / H0 = X ^ (2 - 2 * delta) := by
    rw [hU, hH0, ← Real.rpow_add hX0, hexp, Real.rpow_add hX0, Real.rpow_one,
      mul_div_assoc, div_self hX0.ne', mul_one]
  calc S4sq ≤ U * TA / H0 := hnorm
    _ ≤ U * X ^ ((23 : ℝ) / 9 - 2 * delta) / H0 := step
    _ = X ^ (2 - 2 * delta) := final

/-- **The source normalization hypothesis cannot be dropped.**  Without it the
`T_A` bound alone implies nothing about `S₄`, so `X^(23/9)` is not a globally
authoritative target. -/
theorem no_unconditional_TA_target :
    ¬ ∀ (S4sq TA X delta : ℝ), TA ≤ X ^ ((23 : ℝ) / 9 - 2 * delta) →
        S4sq ≤ X ^ (2 - 2 * delta) := by
  intro h
  have := h 2 0 1 0 (by norm_num)
  norm_num at this

/-! ## 3. Guards against the four documented repairs -/

/-- **REPAIR GUARD (exponent inequalities carry no analytic content).**  The
arithmetic fact `L_ℓ`-exponent `< 1/2` cannot by itself imply an arbitrary
proposition — in particular it does not supply a Bombieri–Vinogradov input. -/
theorem exponent_inequality_has_no_analytic_content :
    ¬ ∀ P : Prop, ellExponent (4 / 9) < 1 / 2 → P := by
  intro h
  exact h False (by rw [ellExponent_top]; norm_num)

/-- **REPAIR GUARD (`−W(0)` is not source centering).**  Exact agreement of an
arbitrary `−W(0)` correction with an arbitrary source expected term is false;
`SourceCenteringMatch` is a genuine hypothesis. -/
theorem negW0_not_source_centering :
    ¬ ∀ w0 sourceExpected : ℝ, SourceCenteringMatch sourceExpected w0 0 := by
  intro h
  have := h 0 1
  simp [SourceCenteringMatch] at this
  linarith

/-- **REPAIR GUARD (no free `d₂ × d₃` dictionary).**  Source coefficients are
not automatically divisor coefficients. -/
theorem no_free_d2d3_dictionary :
    ¬ ∀ sourceCoeff divisorCoeff : ℝ, D2D3CoefficientDictionary sourceCoeff divisorCoeff 0 := by
  intro h
  have := h 0 1
  simp [D2D3CoefficientDictionary] at this
  linarith

/-- **REPAIR GUARD (deleting `h = 0` is not subtracting `1/q`).**  Finite
restatement, reusing `CenteringCore`. -/
theorem deletion_not_inverse_modulus :
    ∃ (S : Finset ℤ) (a : ℤ → ℚ) (q : ℕ),
      deleteZeroFrequency S a ≠ subtractInverseModulus S a q := by
  obtain ⟨S, a, q, _, _, h₁, _⟩ := centering_ops_pairwise_distinct
  exact ⟨S, a, q, h₁⟩

/-! ## 4. Conditional chain (all analytic inputs explicit) -/

/-- A conditional statement of the shape actually available: if Poisson holds
with tolerance `tolP`, the source centering matches with tolerance `tolC`, and
the non-coprime strata are bounded by `bnd`, then the corresponding total
error is bounded by the sum of the three tolerances plus `bnd`.  Purely the
triangle inequality: no analytic input is manufactured. -/
theorem conditional_error_assembly
    {spatial dual sourceExpected centering strata bnd tolP tolC : ℝ}
    (hP : SmoothPoissonIdentity spatial dual tolP)
    (hC : SourceCenteringMatch sourceExpected centering tolC)
    (hS : NonCoprimeStrataNegligible strata bnd) :
    |spatial - dual| + |sourceExpected - centering| + |strata| ≤ tolP + tolC + bnd := by
  unfold SmoothPoissonIdentity at hP
  unfold SourceCenteringMatch at hC
  unfold NonCoprimeStrataNegligible at hS
  linarith

end HPoissonCD
end TwinPrimeProject
