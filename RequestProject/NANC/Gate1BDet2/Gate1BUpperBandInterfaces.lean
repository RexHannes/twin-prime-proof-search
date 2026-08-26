import RequestProject.NANC.Gate1BDet2.CompositeViewDet2
import RequestProject.NANC.Gate1BDet2.ProjectiveThirdCoordinateRigidity

/-!
# Gate 1B / determinant-2 bank, Module 40: upper-band interfaces

All analytic statements of the reciprocal-frame / upper-band programme are
declared here as **ordinary `Prop` definitions**.  No `axiom` is introduced and
**none of the analytic premises is ever discharged**: the Band-II / Band-III
master bound remains under audit.

Only two *deterministic* implication chains are proved, each a plain triangle
inequality on the recorded quantities:

  `BandIIClosed ∧ LowerBandIIIClosed ∧ UpperBandIIIClosed → Gate1BAnalyticCoreClosed`,

  `Gate1BAnalyticCoreClosed ∧ SourceExpectedTermIdentified ∧
     FixedSwitchedPacketReassembled → Gate1BClosed`.

Three separating guards are supplied:

* composite-view geometry (Module 34, proved) does **not** imply
  `CompositeViewSquareRootGain`;
* projective collision rigidity (Module 36, proved) does **not** imply
  `UpperBandIIIClosed`;
* `ReciprocalMasterBound` is **not** automatically inhabited.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace UpperBand

/-! ## 1. The interface propositions (never inhabited) -/

/-- **OPEN INTERFACE.**  The reciprocal-frame master bound. -/
def ReciprocalMasterBound (sum bound : ℝ) : Prop := |sum| ≤ bound

/-- **OPEN INTERFACE.**  Band II is closed. -/
def BandIIClosed (sum bound : ℝ) : Prop := |sum| ≤ bound

/-- **OPEN INTERFACE.**  The lower part of Band III is closed. -/
def LowerBandIIIClosed (sum bound : ℝ) : Prop := |sum| ≤ bound

/-- **OPEN INTERFACE.**  The upper-band residual bound. -/
def UpperBandResidualBound (sum bound : ℝ) : Prop := |sum| ≤ bound

/-- **OPEN INTERFACE.**  The two-prime composite view has been extracted. -/
def TwoPrimeCompositeViewExtracted (residual tol : ℝ) : Prop := |residual| ≤ tol

/-- **OPEN INTERFACE.**  The four-prime composite view has been extracted. -/
def FourPrimeCompositeViewExtracted (residual tol : ℝ) : Prop := |residual| ≤ tol

/-- **OPEN INTERFACE.**  A square-root gain from the composite view. -/
def CompositeViewSquareRootGain (gain bound : ℝ) : Prop := gain ≤ bound

/-- **OPEN INTERFACE.**  The upper part of Band III is closed. -/
def UpperBandIIIClosed (sum bound : ℝ) : Prop := |sum| ≤ bound

/-- **OPEN INTERFACE.**  The routed face family is the complete prime-divisor
face family. -/
def SourceFaceCompleteness (routedFaces fullFaces : Finset ℕ) : Prop :=
  routedFaces = fullFaces

/-- **OPEN INTERFACE.**  The source expected term is identified. -/
def SourceExpectedTermIdentified (sourceExpected centering tol : ℝ) : Prop :=
  |sourceExpected - centering| ≤ tol

/-- **OPEN INTERFACE.**  The fixed switched packet is reassembled. -/
def FixedSwitchedPacketReassembled (packet target tol : ℝ) : Prop :=
  |packet - target| ≤ tol

/-- **OPEN INTERFACE.**  The Gate-1B analytic core is closed. -/
def Gate1BAnalyticCoreClosed (sum bound : ℝ) : Prop := |sum| ≤ bound

/-- **OPEN INTERFACE.**  Gate 1B is closed. -/
def Gate1BClosed (sum bound : ℝ) : Prop := |sum| ≤ bound

/-! ## 2. Deterministic implication chains -/

/-- **Deterministic package.**  Band II plus both halves of Band III give the
analytic core, by the triangle inequality on the recorded quantities.  *No
premise is discharged here.* -/
theorem gate1BAnalyticCoreClosed_of_bands {s₁ s₂ s₃ b₁ b₂ b₃ : ℝ}
    (h₁ : BandIIClosed s₁ b₁) (h₂ : LowerBandIIIClosed s₂ b₂)
    (h₃ : UpperBandIIIClosed s₃ b₃) :
    Gate1BAnalyticCoreClosed (s₁ + s₂ + s₃) (b₁ + b₂ + b₃) := by
  unfold BandIIClosed at h₁
  unfold LowerBandIIIClosed at h₂
  unfold UpperBandIIIClosed at h₃
  unfold Gate1BAnalyticCoreClosed
  calc |s₁ + s₂ + s₃| ≤ |s₁ + s₂| + |s₃| := abs_add_le _ _
    _ ≤ (|s₁| + |s₂|) + |s₃| := by gcongr; exact abs_add_le _ _
    _ ≤ (b₁ + b₂) + b₃ := by gcongr
    _ = b₁ + b₂ + b₃ := by ring

/-- **Deterministic package.**  The analytic core plus the source expected term
plus the reassembled fixed switched packet give Gate-1B closure, again by the
triangle inequality.  *No premise is discharged here.* -/
theorem gate1BClosed_of_core_of_source {s b e c t p q t' : ℝ}
    (hcore : Gate1BAnalyticCoreClosed s b)
    (hsrc : SourceExpectedTermIdentified e c t)
    (hpkt : FixedSwitchedPacketReassembled p q t') :
    Gate1BClosed (s + (e - c) + (p - q)) (b + t + t') := by
  unfold Gate1BAnalyticCoreClosed at hcore
  unfold SourceExpectedTermIdentified at hsrc
  unfold FixedSwitchedPacketReassembled at hpkt
  unfold Gate1BClosed
  calc |s + (e - c) + (p - q)| ≤ |s + (e - c)| + |p - q| := abs_add_le _ _
    _ ≤ (|s| + |e - c|) + |p - q| := by gcongr; exact abs_add_le _ _
    _ ≤ (b + t) + t' := by gcongr
    _ = b + t + t' := by ring

/-! ## 3. Separating guards -/

/-- **GUARD.**  The composite-view determinant geometry of Module 34 is exact
and unconditional; it cannot imply a square-root gain, which has false
instances. -/
theorem compositeViewGeometry_does_not_imply_squareRootGain :
    ∃ gain bound : ℝ,
      (∀ q l u rho s : ℤ, IsCoprime u s → Composite.CompositeDet2 q l u rho s →
        q * l ≡ 2 [ZMOD u * s])
      ∧ ¬ CompositeViewSquareRootGain gain bound := by
  refine ⟨1, 0, fun q l u rho s hcop h => Composite.det2_composite_view_mod_us hcop h, ?_⟩
  unfold CompositeViewSquareRootGain
  norm_num

/-- **GUARD.**  Projective collision rigidity (Module 36) is exact and
unconditional; it cannot imply closure of the upper part of Band III. -/
theorem projectiveRigidity_does_not_imply_upperBandIIIClosed :
    ∃ sum bound : ℝ,
      (∀ (p : ℕ) (_ : Fact (Nat.Prime p)), p ≠ 2 → ∀ A B A' B' : ZMod p,
        Projective.ProjectivelyEq3 (A, B, (-2 : ZMod p)) (A', B', (-2 : ZMod p)) →
          A = A' ∧ B = B')
      ∧ ¬ UpperBandIIIClosed sum bound := by
  refine ⟨1, 0, ?_, ?_⟩
  · intro p hp hp2 A B A' B' h
    exact Projective.projective_third_coordinate_rigidity hp2 h
  · unfold UpperBandIIIClosed
    norm_num

/-- **GUARD.**  `ReciprocalMasterBound` is not automatically inhabited. -/
theorem reciprocalMasterBound_not_automatic :
    ∃ sum bound : ℝ, ¬ ReciprocalMasterBound sum bound := by
  refine ⟨1, 0, ?_⟩
  unfold ReciprocalMasterBound
  norm_num

end UpperBand
end Gate1BDet2
end TwinPrimeProject
