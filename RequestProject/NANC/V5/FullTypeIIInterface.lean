/-
NANC V5 — THE FULL FORD–MAYNARD TYPE-II HYPOTHESIS ON THE 1/6 INTERVAL.

The Type-II predicate itself is the V4 one (`FMTypeIIAtScale`), in which the
universal quantifier over arbitrary divisor-bounded `ξ, κ` appears literally.
This file assembles it over the whole exponent interval `[ε, 1/6 - ε]`.

UNINHABITED: `FullFMTypeIIAtOneSixth`, `Gate1ABFullReassemblyCertificate`.

PERMANENT FIREWALL:
    Gate1AOutput + Gate1BOutput  ≠  FullFMTypeIIAtOneSixth
without a full reassembly certificate.
-/
import Mathlib
import RequestProject.NANC.V5.EpsilonLedger

namespace NANC.V5

open scoped BigOperators
open NANC.V4

/-- **Full Ford–Maynard Type-II hypothesis at `1/6` (UNINHABITED).**

For every exponent `σ` in the interval `[ε, 1/6 - ε]`, and for **all**
divisor-bounded complex coefficients `ξ, κ` (the quantifier lives in the V4
predicate `FMTypeIIAtScale`), the bilinear sum over the block attached to `σ` is
bounded by `target`. -/
def FullFMTypeIIAtOneSixth (X : ℕ) (mRangeOf nRangeOf : ℚ → Finset ℕ)
    (dwM dwN : ℕ → ℝ) (w : ℕ → ℂ) (eps : ℚ) (target : ℝ) : Prop :=
  ∀ sigma : ℚ, eps ≤ sigma → sigma ≤ 1 / 6 - eps →
    FMTypeIIAtScale X (mRangeOf sigma) (nRangeOf sigma) dwM dwN w target

/-- Every exponent in the interval is covered: an immediate projection. -/
theorem fullTypeII_at (X : ℕ) {mRangeOf nRangeOf : ℚ → Finset ℕ} {dwM dwN : ℕ → ℝ}
    {w : ℕ → ℂ} {eps sigma : ℚ} {target : ℝ}
    (h : FullFMTypeIIAtOneSixth X mRangeOf nRangeOf dwM dwN w eps target)
    (h1 : eps ≤ sigma) (h2 : sigma ≤ 1 / 6 - eps) :
    FMTypeIIAtScale X (mRangeOf sigma) (nRangeOf sigma) dwM dwN w target :=
  h sigma h1 h2

/-- **The full reassembly certificate (UNINHABITED).**

It carries the V4 bookkeeping obligations *and*, separately, the conversion of
those obligations into the full Type-II hypothesis on the whole interval.  The
conversion is external analytic content and is therefore a field, not a proof. -/
structure Gate1ABFullReassemblyCertificate (A : Gate1AOutput) (B : Gate1BOutput)
    (D : FMTypeIIReassemblyData) (X : ℕ) (mRangeOf nRangeOf : ℚ → Finset ℕ)
    (dwM dwN : ℕ → ℝ) (w : ℕ → ℂ) (eps : ℚ) (target : ℝ) : Prop where
  /-- The V4 packet-level reassembly certificate. -/
  packetCertificate : Gate1ABReassemblyCertificate A B D
  /-- The conversion of the reassembly obligations into the full interval statement. -/
  conversion : FullFMTypeIIReassembly D →
    FullFMTypeIIAtOneSixth X mRangeOf nRangeOf dwM dwN w eps target

/-- With the certificate — and only with it — the source packets yield the full
Type-II hypothesis on the interval. -/
theorem fullReassembly_certificate_imp_fullTypeII {A : Gate1AOutput} {B : Gate1BOutput}
    {D : FMTypeIIReassemblyData} {X : ℕ} {mRangeOf nRangeOf : ℚ → Finset ℕ}
    {dwM dwN : ℕ → ℝ} {w : ℕ → ℂ} {eps : ℚ} {target : ℝ}
    (h : Gate1ABFullReassemblyCertificate A B D X mRangeOf nRangeOf dwM dwN w eps target) :
    FullFMTypeIIAtOneSixth X mRangeOf nRangeOf dwM dwN w eps target :=
  h.conversion (gate1AB_certificate_imp_full_reassembly h.packetCertificate)

/-- **Firewall (finite counterexample).**  Gate-1A and Gate-1B source outputs can
both hold on data where the full interval Type-II hypothesis fails.  Hence the two
must never be identified without a reassembly certificate. -/
theorem gate1AB_not_fullTypeIIAtOneSixth :
    ∃ (A : Gate1AOutput) (B : Gate1BOutput) (mRangeOf nRangeOf : ℚ → Finset ℕ)
      (dwM dwN : ℕ → ℝ) (eps : ℚ),
      A.X = B.X ∧ A.w = B.w ∧ A.target = B.target ∧
      ¬ FullFMTypeIIAtOneSixth A.X mRangeOf nRangeOf dwM dwN A.w eps A.target := by
  classical
  refine ⟨{ X := 1, mRange := {1}, nRange := {1}, w := fun _ => 1, xi0 := fun _ => 0,
            kappa0 := fun _ => 0, target := 0,
            bound := by simp [SourceSpecificTypeII, typeIISum] },
          { X := 1, mRange := {1}, nRange := {1}, w := fun _ => 1, xi0 := fun _ => 0,
            kappa0 := fun _ => 0, target := 0,
            bound := by simp [SourceSpecificTypeII, typeIISum] },
          fun _ => {1}, fun _ => {1}, fun _ => 1, fun _ => 1, 0, rfl, rfl, rfl, ?_⟩
  intro h
  have h0 := h 0 (le_refl 0) (by norm_num)
  have h1 := h0 (fun _ => 1) (fun _ => 1) (fun m _ => by norm_num) (fun m _ => by norm_num)
  simp [typeIISum, dyadicSupport] at h1

/-- Provenance: the full Type-II hypothesis is an external analytic input. -/
def fullTypeIIProvenance : Provenance :=
  provenanceExternalTheorem "Full arbitrary-coefficient Ford–Maynard Type-II on [ε, 1/6-ε]"
    "arXiv:2407.14368 (hypothesis, not theorem)" "no inhabitant in this bank"

theorem fullTypeIIProvenance_not_leanEvidence :
    Provenance.IsLeanEvidence fullTypeIIProvenance = false := rfl

end NANC.V5
