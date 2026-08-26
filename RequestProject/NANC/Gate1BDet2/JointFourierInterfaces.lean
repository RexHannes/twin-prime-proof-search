import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 28: joint-Fourier interfaces

Every proposition in this module is an **interface**: an ordinary `Prop`-valued
definition which this development neither proves nor assumes.  **No `axiom` is
introduced**, and none of the analytic interfaces below is inhabited.  Only
deterministic transfers — statements that are tautological consequences of the
interface *definitions* — are proved.

Deliberately **not** proved:

  `ExactJointFourierRepresentation → JointFourierProducesNewOrthogonality`,

because the audit found that the direct Fourier coordinate change closes a loop:
an exact representation of the same quantity in new coordinates is not new
orthogonality.  A guard exhibits data satisfying the first and violating the
second.

`JointFourierAntiLoopDiagnosed` is declared but left uninhabited: the exact
finite statement of the diagnosis has not been encoded here.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace JF

/-! ## 1. Interfaces -/

/-- **INTERFACE.**  The joint-Fourier expansion represents the on-shell quantity
exactly: `lhs = rhs`. -/
def ExactJointFourierRepresentation (lhs rhs : ℂ) : Prop := lhs = rhs

/-- **INTERFACE (OPEN).**  The joint-Fourier coordinates produce genuinely new
orthogonality: the residual is bounded by `bound`. -/
def JointFourierProducesNewOrthogonality (residual bound : ℝ) : Prop := |residual| ≤ bound

/-- **INTERFACE (OPEN).**  A determinant-conditioned generalized von Neumann
inequality for the on-shell sum. -/
def DeterminantConditionedGeneralizedVonNeumann (sum bound : ℝ) : Prop := |sum| ≤ bound

/-- **INTERFACE (OPEN).**  A determinant-weighted spectral inequality. -/
def DeterminantWeightedSpectralInequality (lhs rhs : ℝ) : Prop := lhs ≤ rhs

/-- **INTERFACE (OPEN).**  The quotient weight is spectrally separated: it agrees
with a separated model up to `tol`. -/
def QuotientWeightSpectrallySeparated (weight separated tol : ℝ) : Prop :=
  |weight - separated| ≤ tol

/-- **INTERFACE (OPEN).**  A genuine two-sequence Kloosterman kernel has been
manufactured, with the corresponding kernel sum bounded. -/
def TwoSequenceKloostermanManufactured (kernelSum bound : ℝ) : Prop := |kernelSum| ≤ bound

/-- **INTERFACE (OPEN).**  The on-shell mixed fourth moment bound. -/
def OnShellMixedFourthMomentBound (moment bound : ℝ) : Prop := |moment| ≤ bound

/-- **INTERFACE (OPEN).**  The pre-Cauchy `P45` bound. -/
def PreCauchyP45Bound (p45 bound : ℝ) : Prop := |p45| ≤ bound

/-- **INTERFACE, DELIBERATELY UNINHABITED.**  The statement that the direct
joint-Fourier coordinate change is an anti-loop, i.e. returns the quantity it
started from.  The exact finite/formal content of the diagnosis has *not* been
encoded, so this proposition is declared and never proved. -/
def JointFourierAntiLoopDiagnosed (before after : ℝ) : Prop := before = after

/-! ## 2. Deterministic transfers -/

/-- **Tautological transfer.**  If the pre-Cauchy `P45` quantity splits exactly
as the mixed fourth moment plus a remainder, then the moment interface plus a
remainder bound gives the `P45` interface.  This proves neither premise. -/
theorem preCauchyP45Bound_of_moment_of_remainder
    {p45 moment remainder b t : ℝ}
    (hsplit : p45 = moment + remainder)
    (hmom : OnShellMixedFourthMomentBound moment b)
    (hrem : |remainder| ≤ t) :
    PreCauchyP45Bound p45 (b + t) := by
  unfold PreCauchyP45Bound OnShellMixedFourthMomentBound at *
  rw [hsplit]
  have := abs_add_le moment remainder
  linarith

/-- **Tautological transfer.**  A determinant-weighted spectral inequality
composes with a bound on its right-hand side. -/
theorem spectral_transfer {lhs rhs bound : ℝ}
    (hspec : DeterminantWeightedSpectralInequality lhs rhs) (hrhs : rhs ≤ bound) :
    lhs ≤ bound := le_trans hspec hrhs

/-- **Tautological transfer.**  Spectral separation of the quotient weight
transports a bound from the separated model to the weight itself. -/
theorem weight_bound_of_separated {weight separated tol b : ℝ}
    (hsep : QuotientWeightSpectrallySeparated weight separated tol)
    (hb : |separated| ≤ b) : |weight| ≤ b + tol := by
  unfold QuotientWeightSpectrallySeparated at hsep
  have : |weight| ≤ |weight - separated| + |separated| := by
    have := abs_add_le (weight - separated) separated
    simpa using this
  linarith

/-! ## 3. Guards -/

/-- **Guard (the anti-loop).**  An exact joint-Fourier representation does *not*
by itself deliver new orthogonality: here the representation holds (trivially,
`lhs = lhs`) while the orthogonality interface fails for the corresponding
residual.  Hence the implication
`ExactJointFourierRepresentation → JointFourierProducesNewOrthogonality`
is not provable, and is not proved. -/
theorem orthogonality_not_implied_by_representation :
    ExactJointFourierRepresentation 1 1 ∧ ¬ JointFourierProducesNewOrthogonality 1 0 := by
  constructor
  · unfold ExactJointFourierRepresentation; rfl
  · unfold JointFourierProducesNewOrthogonality; norm_num

/-- **Guard.**  The interfaces are not automatically true. -/
theorem mixedFourthMoment_not_automatic : ¬ OnShellMixedFourthMomentBound 1 0 := by
  unfold OnShellMixedFourthMomentBound; norm_num

/-- **Guard.**  Nor are they false: they are satisfiable, hence genuine open
inputs. -/
theorem mixedFourthMoment_satisfiable : OnShellMixedFourthMomentBound 1 1 := by
  unfold OnShellMixedFourthMomentBound; norm_num

/-- **Guard.**  A manufactured two-sequence kernel bound alone does not give the
pre-Cauchy `P45` bound at the same numerical value. -/
theorem p45_needs_more_than_kernel :
    TwoSequenceKloostermanManufactured 0 1 ∧ ¬ PreCauchyP45Bound 2 1 := by
  constructor
  · unfold TwoSequenceKloostermanManufactured; norm_num
  · unfold PreCauchyP45Bound; norm_num

end JF
end Gate1BDet2
end TwinPrimeProject
