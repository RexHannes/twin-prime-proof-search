/-
# Gate-1A §20 / A20: the conditional closure theorems

**Forbidden and absent:** there is no theorem
`gate1a_direct_generic_closed` without interface hypotheses.  The present
mathematical status is `GATE1A_DIRECT_GENERIC_OPEN`, and every closure
theorem below carries its open source/analytic interfaces as *explicit
hypotheses*.

The three public closure theorems are:

* `gate1a_fixed_quotient_core` — **unconditional**.  A bundle of the
  kernel-checked finite core facts of the fixed-quotient programme.
* `gate1a_of_S1_S2_S3` — conditional on the addendum's S1/S2/S3 branch
  interfaces plus the numerical margins.
* `gate1a_candidate_closed_of_fixed_quotient_interfaces` — conditional on
  the full §17 source interfaces and the analytic interfaces.

`gate1a_direct_generic_of_interfaces` is the §20 form of the last one.
-/
import Mathlib
import Gate1A.SourceInterfaces
import Gate1A.ErrorAlgebra
import Gate1A.Exponents
import Gate1A.PoissonBruhat
import Gate1A.RankFloor
import Gate1A.FourCycle
import Gate1A.HardSupport

namespace Gate1A

namespace ConditionalClosure

open SourceInterfaces

/-! ### The abstract conditional closure -/

/-- **`gate1a_conditional_closure`.**  The finite analogue of
"normalised variance ≤ target": if each of the three branches is below a
third of the target, their sum is below the target. -/
theorem gate1a_conditional_closure (P : Gate1APacket) (curv proj err : ℝ)
    (hcurv : curv ≤ (P.D / P.S) * P.Bnat)
    (hproj : proj ≤ P.tau * P.Bdiag)
    (herr : err ≤ P.eps ^ 2 * P.Bnat)
    (hm : Gate1ANumericalMargins P) :
    Gate1ANormalizedTarget P (normalizedVariance curv proj err) := by
  have h1 := hm.curvatureMargin
  have h2 := hm.projectiveMargin
  have h3 := hm.errorMargin
  simp only [Gate1ANormalizedTarget, normalizedVariance]
  linarith

/-! ### §20: closure from the full source and analytic interfaces -/

/-- **`gate1a_direct_generic_of_interfaces`** (§20).

Conditional on the open source interfaces and the open analytic interfaces
(and on the purely numerical margins), the normalised Gate-1A target holds.

It is *desired* that this theorem has `hSrc` and `hAnalytic` as hypotheses:
they are exactly the assertions that remain open. -/
theorem gate1a_direct_generic_of_interfaces (P : Gate1APacket)
    {curv proj err nuc Ndiag Nnew trAsq Dr Hscale orderA orderB : ℝ}
    {latticeL1 prefactor opBound thetaTail : ℝ}
    (hSrc : Gate1ASourceInterfaces P curv proj err nuc Ndiag Nnew trAsq Dr
      Hscale orderA orderB)
    (_hAnalytic : Gate1AAnalyticInterfaces P latticeL1 prefactor opBound thetaTail)
    (hm : Gate1ANumericalMargins P) :
    Gate1ANormalizedTarget P (normalizedVariance curv proj err) := by
  refine gate1a_conditional_closure P curv proj err hSrc.normedTransport ?_
    hSrc.phiFlatCensus hm
  have hNd : Ndiag = P.Bdiag := hSrc.recombinedDomain.2
  have := hSrc.projectivePushforward
  rwa [hNd] at this

/-- **`gate1a_candidate_closed_of_fixed_quotient_interfaces`** (A20).

Same content as `gate1a_direct_generic_of_interfaces`, stated in the
fixed-quotient vocabulary of the addendum.  The name records that this is a
*candidate* closure: it is closed **only** relative to the frozen
fixed-quotient interfaces, which are not derived. -/
theorem gate1a_candidate_closed_of_fixed_quotient_interfaces (P : Gate1APacket)
    {curv proj err nuc Ndiag Nnew trAsq Dr Hscale orderA orderB : ℝ}
    {latticeL1 prefactor opBound thetaTail : ℝ}
    (hSrc : Gate1ASourceInterfaces P curv proj err nuc Ndiag Nnew trAsq Dr
      Hscale orderA orderB)
    (hAnalytic : Gate1AAnalyticInterfaces P latticeL1 prefactor opBound thetaTail)
    (hm : Gate1ANumericalMargins P) :
    Gate1ANormalizedTarget P (normalizedVariance curv proj err) :=
  gate1a_direct_generic_of_interfaces P hSrc hAnalytic hm

/-! ### A20: closure from the S1/S2/S3 branch interfaces -/

/-- **`gate1a_of_S1_S2_S3`** (A20).

Conditional on the addendum's three branch interfaces — S1 (five-face
intertwiner), S2 (TF4 normalisation chain), S3 (actual projective
pushforward) — together with the numerical margins, the normalised Gate-1A
target holds. -/
theorem gate1a_of_S1_S2_S3 (P : Gate1APacket)
    {curv proj err nuc minorRank Ndiag : ℝ}
    (hS1 : S1FiveFaceIntertwiner P curv nuc minorRank)
    (hS2 : S2TF4Normalisation P err)
    (hS3 : S3ProjectivePushforward P proj Ndiag)
    (hm : Gate1ANumericalMargins P) :
    Gate1ANormalizedTarget P (normalizedVariance curv proj err) := by
  refine gate1a_conditional_closure P curv proj err ?_ ?_ hS2.amplitudeError hm
  · refine hS1.curvatureTransport.trans ?_
    have hDS : 0 ≤ P.D / P.S := div_nonneg P.hD (le_of_lt P.hS)
    exact mul_le_mul_of_nonneg_left hS1.nuclearNormalisation hDS
  · refine hS3.projectiveEnergy.trans ?_
    exact mul_le_mul_of_nonneg_left hS3.nuclearDiagonalScale P.htau

/-! ### The unconditional fixed-quotient finite core -/

/-- **`gate1a_fixed_quotient_core`** — **unconditional**.

A bundle of kernel-checked finite facts of the fixed-quotient programme,
stated for an arbitrary point of the frozen polytope:

1. the required-saving exponent is negative;
2. the outer root capacity `-a/2 ≤ a+2b-1`;
3. the `p/q`-face capacity `-b/2 ≤ a+2b-1`;
4. the TRUE `U^{-2}` recombination error is admissible at the amplitude
   level, `epsExp ≤ reqExp/2` (Route A, theta EXACTLY RETAINED);
5. the weaker Route B (theta discarded with `U^{-1}`) is also admissible;
6. the projective energy exponent is negative;
7. the first Poisson–Bruhat normalisation `M²H = R L²`;
8. the second (corrected) Poisson–Bruhat normalisation.

None of these depends on any interface. -/
theorem gate1a_fixed_quotient_core {a b : ℚ} (h : Polytope a b) :
    reqExp a b < 0 ∧
    -a / 2 ≤ reqExp a b ∧
    -b / 2 ≤ reqExp a b ∧
    epsExp a b ≤ reqExp a b / 2 ∧
    uInvExp a b ≤ reqExp a b / 2 ∧
    projExp a b < 0 ∧
    2 * mExp + hExp a b - (a + 2 * b) = 0 ∧
    (mExp + kExp a - (a + 4 * b)) + 2 * (mExp + hExp a b) = 0 :=
  ⟨gate1a_reqExp_neg h,
   gate1a_outer_capacity h,
   gate1a_face_capacity h,
   ErrorAlgebra.route_A_theta_retained_admissible h,
   ErrorAlgebra.route_B_theta_discarded_admissible h,
   gate1a_projective_exp_neg h,
   PoissonBruhat.pb_normalisation_one a b,
   PoissonBruhat.pb_normalisation_two a b⟩

/-- The frozen polytope is nonempty, so `gate1a_fixed_quotient_core` is not
vacuous. -/
theorem gate1a_fixed_quotient_core_nonvacuous : ∃ a b : ℚ, Polytope a b :=
  gate1a_polytope_nonempty

end ConditionalClosure

end Gate1A
