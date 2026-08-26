import RequestProject.NANC.FiniteGramFourthMoment
import RequestProject.NANC.RouteANames

/-!
# Route-A fibre frame: conditional FF4 dependency interfaces

The analytic content of `FF4`, `FF4_MIX` and the Route-A edge variance
`V_ROUTE_A` is **not** proved anywhere in this development.  It appears only as
the `bound` field of the interface structures below, i.e. as a proposition
supplied from outside.

The two dependency theorems of this file are pure packaging: they take the
supplied propositions, together with the finite Gram fourth-moment inequality
`RouteAFibreFrame.finite_gram_fourth_moment_cauchy` (which *is* proved) and an
explicit numerical comparison, and return the corresponding interface object
whose `bound` field is exactly the conjunction of what was supplied.  No new
analytic bound is created.
-/

namespace RouteAFibreFrame

/-- Interface carrying a one-row fourth-moment (FF4) statement. -/
structure FF4Hypothesis where
  /-- The analytic FF4 proposition, supplied from outside Lean. -/
  bound : Prop

/-- Interface carrying the remaining one-row mixed-prime covariance statement. -/
structure FF4MixHypothesis where
  /-- The analytic FF4_MIX proposition, supplied from outside Lean. -/
  bound : Prop

/-- Interface carrying the Route-A edge variance statement `V_ROUTE_A`. -/
structure RouteAVarianceHypothesis where
  /-- The analytic Route-A variance proposition. -/
  bound : Prop

/-- The finite Gram fourth-moment inequality, packaged as a proposition, in the
form in which the Route-A variance argument uses it. -/
def gramFourthMomentStatement : Prop :=
  ∀ (J T : Type) [Fintype J] [Fintype T] (x y : J → T → ℂ),
    crossFourth x y ≤ Real.sqrt (gramFourth x) * Real.sqrt (gramFourth y)

theorem gramFourthMomentStatement_holds : gramFourthMomentStatement := by
  intro J T _ _ x y
  exact finite_gram_fourth_moment_cauchy x y

/-- **Route-A variance from two FF4 rows.**

Given the FF4 statements for the two rows (`b` and `d`), the numerical
comparison `R M D² ≤ H M D²`, and proofs of the two supplied bounds, we may form
the Route-A variance interface whose proposition is *exactly* the conjunction of
the supplied data with the proved Gram inequality.  Nothing analytic is
invented: `V_ROUTE_A` remains open, see `RouteAFibreFrame.status`. -/
def routeA_variance_from_ff4 (R M D H : ℝ)
    (hff4_b : FF4Hypothesis) (hff4_d : FF4Hypothesis)
    (h_numeric : R * M * D ^ 2 ≤ H * M * D ^ 2) :
    hff4_b.bound → hff4_d.bound → RouteAVarianceHypothesis :=
  fun _ _ =>
    -- the numerical comparison is recorded inside the packaged proposition
    let _numeric := h_numeric
    ⟨hff4_b.bound ∧ hff4_d.bound ∧ R * M * D ^ 2 ≤ H * M * D ^ 2 ∧
      gramFourthMomentStatement⟩

/-- The packaged Route-A proposition produced by `routeA_variance_from_ff4` is
true under the supplied hypotheses. -/
theorem routeA_variance_from_ff4_bound_holds (R M D H : ℝ)
    (hff4_b : FF4Hypothesis) (hff4_d : FF4Hypothesis)
    (h_numeric : R * M * D ^ 2 ≤ H * M * D ^ 2)
    (hb : hff4_b.bound) (hd : hff4_d.bound) :
    (routeA_variance_from_ff4 R M D H hff4_b hff4_d h_numeric hb hd).bound :=
  ⟨hb, hd, h_numeric, gramFourthMomentStatement_holds⟩

/-- Interface for the row-diagonal contribution. -/
structure RowDiagonalHypothesis where
  /-- The row-diagonal proposition. -/
  bound : Prop

/-- Interface for the same-prime sector. -/
structure SamePrimeSectorHypothesis where
  /-- The same-prime sector proposition. -/
  bound : Prop

/-- Interface for the single-frequency corrections. -/
structure SingleFrequencyCorrectionHypothesis where
  /-- The single-frequency correction proposition. -/
  bound : Prop

/-- **FF4 from its four declared inputs.**

FF4 is assembled from the row diagonal, the same-prime sector, the
single-frequency corrections and `FF4_MIX`.  Again this is packaging only: the
resulting `bound` is the conjunction of the four supplied propositions, so no
analytic statement is created here.  `FF4` and `FF4_MIX` remain open. -/
def ff4_from_mix_and_closed_sectors
    (hrow : RowDiagonalHypothesis) (hsame : SamePrimeSectorHypothesis)
    (hsingle : SingleFrequencyCorrectionHypothesis) (hmix : FF4MixHypothesis) :
    hrow.bound → hsame.bound → hsingle.bound → hmix.bound → FF4Hypothesis :=
  fun _ _ _ _ => ⟨hrow.bound ∧ hsame.bound ∧ hsingle.bound ∧ hmix.bound⟩

/-- The packaged FF4 proposition produced by `ff4_from_mix_and_closed_sectors` is
true under the supplied hypotheses. -/
theorem ff4_from_mix_and_closed_sectors_bound_holds
    (hrow : RowDiagonalHypothesis) (hsame : SamePrimeSectorHypothesis)
    (hsingle : SingleFrequencyCorrectionHypothesis) (hmix : FF4MixHypothesis)
    (h1 : hrow.bound) (h2 : hsame.bound) (h3 : hsingle.bound) (h4 : hmix.bound) :
    (ff4_from_mix_and_closed_sectors hrow hsame hsingle hmix h1 h2 h3 h4).bound :=
  ⟨h1, h2, h3, h4⟩

end RouteAFibreFrame
