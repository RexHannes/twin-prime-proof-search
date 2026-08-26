import RequestProject.NANC.HFMVGate1B.HFMVDiagonal

/-!
# HFMV Gate 1B, Module 6: analytic interfaces (declared, never inhabited)

Every proposition in this module is an **interface**: a named predicate that
this development never proves and never instantiates.  The only theorems here
are deterministic implications which take the interfaces as hypotheses.

Interfaces:

* `MobiusDyadicLogSaving`;
* `DivisorBoundDyadic`;
* `GSDVBound`;
* `SmallProperGCDBound`;
* `SourceExpectedTermMatchesHFMVCentering`.

Target predicate: `HFMVBound`.  **`Gate1BClosed` is not stated anywhere.**
-/

namespace TwinPrimeProject
namespace HFMVGate1B

/-! ## 1. Interfaces -/

/-- **EXTERNAL ANALYTIC INTERFACE.**  Dyadic Möbius logarithmic saving: the
dyadic Möbius-weighted quantity `S` is at most `bound` in absolute value.  Not
proved here. -/
def MobiusDyadicLogSaving (S bound : ℝ) : Prop := |S| ≤ bound

/-- **EXTERNAL ANALYTIC INTERFACE.**  Dyadic divisor bound: the divisor-sum
quantity `T` is at most `bound`.  Not proved here. -/
def DivisorBoundDyadic (T bound : ℝ) : Prop := T ≤ bound

/-- **OPEN ANALYTIC.**  The generic off-diagonal GSDV bound.  This is the open
theorem of the programme; it is never proved or assumed to hold. -/
def GSDVBound (offDiagonal bound : ℝ) : Prop := |offDiagonal| ≤ bound

/-- **OPEN / EXTERNAL.**  Bound for the sectors with a small proper common
divisor. -/
def SmallProperGCDBound (gcdSector bound : ℝ) : Prop := |gcdSector| ≤ bound

/-- **OPEN SOURCE.**  The assertion that the source's switched expected term
coincides, up to `tol`, with the HFMV centering term.  This identification is
not supplied by the present development. -/
def SourceExpectedTermMatchesHFMVCentering (sourceExpected hfmvCentering tol : ℝ) : Prop :=
  |sourceExpected - hfmvCentering| ≤ tol

/-- The HFMV target predicate. -/
def HFMVBound (total bound : ℝ) : Prop := |total| ≤ bound

/-- Interface for a supplied diagonal bound (the finite diagonal identity of
`HFMVDiagonal` is proved, its size is *not*). -/
def DiagonalBound (diagonal bound : ℝ) : Prop := |diagonal| ≤ bound

/-! ## 2. Deterministic implication -/

/-- **The deterministic assembly.**  If the HFMV total decomposes exactly as

  `total = offDiagonal + diagonal + gcdSector + (sourceExpected - hfmvCentering)`

and each of the four pieces is controlled by its interface, then the HFMV
target holds with the sum of the four bounds.  This theorem proves **none** of
its premises: `GSDVBound` in particular remains open. -/
theorem hfmv_bound_of_interfaces
    {total offDiagonal diagonal gcdSector sourceExpected hfmvCentering : ℝ}
    {b₁ b₂ b₃ tol : ℝ}
    (hsplit : total = offDiagonal + diagonal + gcdSector
      + (sourceExpected - hfmvCentering))
    (hgsdv : GSDVBound offDiagonal b₁)
    (hdiag : DiagonalBound diagonal b₂)
    (hgcd : SmallProperGCDBound gcdSector b₃)
    (hcent : SourceExpectedTermMatchesHFMVCentering sourceExpected hfmvCentering tol) :
    HFMVBound total (b₁ + b₂ + b₃ + tol) := by
  unfold HFMVBound GSDVBound DiagonalBound SmallProperGCDBound
    SourceExpectedTermMatchesHFMVCentering at *
  rw [hsplit]
  calc |offDiagonal + diagonal + gcdSector + (sourceExpected - hfmvCentering)|
      ≤ |offDiagonal + diagonal + gcdSector| + |sourceExpected - hfmvCentering| :=
        abs_add_le _ _
    _ ≤ (|offDiagonal + diagonal| + |gcdSector|) + |sourceExpected - hfmvCentering| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ((|offDiagonal| + |diagonal|) + |gcdSector|) + |sourceExpected - hfmvCentering| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ((b₁ + b₂) + b₃) + tol := by
        exact add_le_add (add_le_add (add_le_add hgsdv hdiag) hgcd) hcent
    _ = b₁ + b₂ + b₃ + tol := by ring

/-- Variant in which the diagonal bound is *derived* from a supplied dyadic
divisor bound together with an exact comparison between the diagonal and the
divisor quantity.  Still nothing analytic is proved here. -/
theorem diagonalBound_of_divisorBound {diagonal T bound : ℝ}
    (hcmp : |diagonal| ≤ T) (hdiv : DivisorBoundDyadic T bound) :
    DiagonalBound diagonal bound :=
  le_trans hcmp hdiv

/-- Variant in which the centering tolerance is supplied by a dyadic Möbius
log-saving statement about the difference itself. -/
theorem centering_of_mobius_saving {sourceExpected hfmvCentering bound : ℝ}
    (hmob : MobiusDyadicLogSaving (sourceExpected - hfmvCentering) bound) :
    SourceExpectedTermMatchesHFMVCentering sourceExpected hfmvCentering bound := hmob

/-! ## 3. Guards -/

/-- **Guard.**  The interfaces are not vacuous and not automatically true: for
`offDiagonal = 1`, `bound = 0` the GSDV interface fails.  Hence no theorem of
this module can produce an inhabitant for free. -/
theorem gsdv_not_automatic : ¬ GSDVBound 1 0 := by
  unfold GSDVBound; norm_num

/-- **Guard.**  Neither is any interface refutable in general (they hold for
suitable data), so the interfaces are genuine open inputs, not false
statements. -/
theorem gsdv_satisfiable : GSDVBound 1 1 := by
  unfold GSDVBound; norm_num

end HFMVGate1B
end TwinPrimeProject
