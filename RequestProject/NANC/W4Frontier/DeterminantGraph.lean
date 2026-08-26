import RequestProject.NANC.W4Frontier.DeltaShift

namespace TwinPrimeProject.NANC.W4Frontier

/-- Affine orbit coordinates used by the determinant calculation. -/
def affineA (A0 m t : ℤ) : ℤ := A0 + m * t
def affineB (B0 mPrime t : ℤ) : ℤ := B0 + mPrime * t

theorem affine_differences (A0 B0 m mPrime s t : ℤ) :
    affineA A0 m s - affineA A0 m t = m * (s - t) ∧
    affineB B0 mPrime s - affineB B0 mPrime t = mPrime * (s - t) := by
  constructor <;> simp [affineA, affineB] <;> ring

/-- The exact pre-shift determinant identity. -/
theorem determinant_identity
    (A0 B0 m mPrime k s t : ℤ)
    (horbit : mPrime * A0 - m * B0 = 2 * k) :
    affineA A0 m t * affineB B0 mPrime s -
      affineA A0 m s * affineB B0 mPrime t = 2 * k * (s - t) := by
  calc
    affineA A0 m t * affineB B0 mPrime s -
        affineA A0 m s * affineB B0 mPrime t =
        (mPrime * A0 - m * B0) * (s - t) := by
          simp [affineA, affineB]
          ring
    _ = 2 * k * (s - t) := by rw [horbit]

/-- The determinant derivation directly from the two affine differences and
base relation. This is the active algebraic identity. -/
theorem jointHitDeterminantIdentity
    {A_t B_t A_s B_s m mPrime k z : ℤ}
    (hA : A_s = A_t + m * z)
    (hB : B_s = B_t + mPrime * z)
    (hBase : mPrime * A_t - m * B_t = 2 * k) :
    A_t * B_s - A_s * B_t = 2 * k * z := by
  rw [hA, hB]
  calc
    A_t * (B_t + mPrime * z) - (A_t + m * z) * B_t =
        (mPrime * A_t - m * B_t) * z := by ring
    _ = 2 * k * z := by rw [hBase]

/-- Substituting four hit factorizations gives the corrected frontier
 determinant `p q' u v' - p' q u' v = 2 k z`. -/
theorem four_hit_determinant
    (p q pPrime qPrime u v uPrime vPrime k z A_t B_t A_s B_s : ℤ)
    (hdet : A_t * B_s - A_s * B_t = 2 * k * z)
    (hAt : A_t = p * u) (hBt : B_t = q * v)
    (hAs : A_s = pPrime * uPrime) (hBs : B_s = qPrime * vPrime) :
    p * qPrime * u * vPrime - pPrime * q * uPrime * v = 2 * k * z := by
  subst A_t
  subst B_t
  subst A_s
  subst B_s
  nlinarith

/-- Data for the corrected signed joint-hit determinant graph. `delta`, `k`,
and `r` remain separate; no integer division is used. -/
structure JointHitData where
  r : ℤ
  k : ℤ
  delta : ℤ
  z : ℤ
  p : ℤ
  q : ℤ
  pPrime : ℤ
  qPrime : ℤ
  u : ℤ
  v : ℤ
  uPrime : ℤ
  vPrime : ℤ
  hDelta : delta = k * r

def determinantLHS (J : JointHitData) : ℤ :=
  J.p * J.qPrime * J.u * J.vPrime -
    J.pPrime * J.q * J.uPrime * J.v

def correctDeterminantRHS (J : JointHitData) : ℤ := 2 * J.k * J.z

/-- RETIRED_FALSE_GRAPH: this is retained only to state and diagnose the old
incorrect right-hand side. It is not used by the active frontier. -/
def retiredDeltaRHS (J : JointHitData) : ℤ := 2 * J.delta * J.z

/-- The active determinant graph. -/
def CorrectJointHitGraph (J : JointHitData) : Prop :=
  determinantLHS J = correctDeterminantRHS J

/-- The old RHS has exactly one extra factor `r`. -/
theorem delta_rhs_is_r_times_correct_rhs (J : JointHitData) :
    J.r * correctDeterminantRHS J = retiredDeltaRHS J := by
  simp [correctDeterminantRHS, retiredDeltaRHS, J.hDelta]
  ring

/-- Regression: for `k = 1`, `r = 2`, `delta = 2`, and `z = 1`, the correct
RHS is 2 while the retired RHS is 4. -/
theorem twoDeltaZ_extraFactorRegression :
    (2 : ℤ) * 1 * 1 ≠ 2 * (1 * 2) * 1 := by
  norm_num

/-- Division-free active frontier data. It records simultaneously
`delta = k*r`, `mPrime = m + delta`, and the determinant with RHS `2*k*z`. -/
structure FrontierPoint extends JointHitData where
  m : ℤ
  mPrime : ℤ
  hMPrime : mPrime = m + delta
  determinant : determinantLHS toJointHitData = correctDeterminantRHS toJointHitData
  reconstructM : z * m = pPrime * uPrime - p * u
  reconstructShift : z * mPrime = qPrime * vPrime - q * v

/-- Membership in the shifted P3 graph and the support condition on delta are
analytic/arithmetic predicates to be supplied by the eventual census. -/
structure ShiftedP3FrontierInterface extends ConditionalInterface

def twoKZDeterminantGraphStatus : BankStatus := .provedAlgebraic

/-- FALSE_ROUTE / RETIRED: the graph with RHS `2*delta*z`. -/
def twoDeltaZDeterminantGraphStatus : BankStatus := .falseRoute

/-- The graph algebra is proved, while its signed analytic census remains open. -/
def determinantGraphStatus : BankStatus := .provedAlgebraic

end TwinPrimeProject.NANC.W4Frontier
