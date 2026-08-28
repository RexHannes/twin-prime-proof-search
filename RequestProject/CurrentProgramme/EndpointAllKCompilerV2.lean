import Mathlib
import RequestProject.CurrentProgramme.EndpointShiftedMAMOperatorSocket
import RequestProject.CurrentProgramme.EndpointHighKBandKernel
import RequestProject.CurrentProgramme.EndpointCharacterSquareSocket
import RequestProject.CurrentProgramme.EndpointAllKCompiler

/-!
# Revised all-`k` compilers

Two purely logical compilers, both **conditional**:

* `allK_endpoint_compiler_v2` — small-`k` character-square input `+` mid-`k`
  shift-averaged MAM input `+` top-`k` finite-shift MAM input `+` an exact
  frequency partition ⟹ the all-`k` endpoint budget.  **No `K^{-δ}` frequency
  gain hypothesis appears anywhere in its statement**, which is precisely why
  the earlier `HighKFrequencyGainInput` lane is superseded (but not deleted).

* `allK_operator_compiler` — the canonical operator route: an exact Fourier
  decomposition into shift packets `+` membership of the kernel in the physical
  class `+` `ShiftedMAMFivefoldOperatorInput` ⟹ the all-`k` endpoint budget.

Comparison is **not** part of either theorem.  The Pure5 packet, which needs the
independent `PURE5-COMPARISON-MAINTERM-PIN`, is kept in a separate structure.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AllKV2

open Finset ShiftedMAM MAMOperator BandKernel

/-! ## 1. Exact frequency decomposition -/

/-- An exact three-way split of the endpoint quantity into the small-, mid- and
top-`k` contributions.  Exhaustiveness is an *equality*: nothing is dropped. -/
structure AllKFrequencyDecomposition where
  /-- The total endpoint quantity. -/
  total : ℝ
  /-- The small-`k` contribution. -/
  smallPart : ℝ
  /-- The mid-`k` contribution. -/
  midPart : ℝ
  /-- The top-`k` contribution. -/
  topPart : ℝ
  /-- Exhaustiveness. -/
  partition : total = smallPart + midPart + topPart

/-- **`allK_endpoint_compiler_v2`.**  Three budgets and an exact partition give
the all-`k` budget.  No frequency-gain hypothesis is used. -/
theorem allK_endpoint_compiler_v2 (D : AllKFrequencyDecomposition) (Bs Bm Bt : ℝ)
    (hs : D.smallPart ≤ Bs) (hm : D.midPart ≤ Bm) (ht : D.topPart ≤ Bt) :
    D.total ≤ Bs + Bm + Bt := by
  rw [D.partition]
  linarith

/-! ## 2. Glue lemmas from the three analytic sockets -/

/-- Small-`k` glue: the character-square socket bounds the small-`k` part. -/
theorem smallPart_le_of_charSquareInput
    (I : CharSquareSocket.EndpointCharTwistedFactorModSquareInput) :
    I.data.TwoStageSquareBundle I.L I.k ≤ I.desiredTarget := I.bound

/-- Mid-`k` glue: the shift-averaged socket bounds the weighted shift family. -/
theorem midPart_le_of_midKInput (S : ShiftedMAMSourceData)
    (I : MidKShiftAveragedMAMInput S) :
    ‖∑ h ∈ I.shiftSet, I.weight h * S.C h‖ ≤ I.target := I.bound

/-- Top-`k` glue: a uniform bound over a finite shift set with bounded weights
costs exactly the cardinality of the shift set. -/
theorem topPart_le_of_topKInput (S : ShiftedMAMSourceData)
    (I : TopKFiniteShiftMAMInput S) (w : ℤ → ℂ) (hw : ∀ h ∈ I.shiftSet, ‖w h‖ ≤ 1) :
    ‖∑ h ∈ I.shiftSet, w h * S.C h‖ ≤ I.shiftSet.card * I.target := by
  calc ‖∑ h ∈ I.shiftSet, w h * S.C h‖
      ≤ ∑ h ∈ I.shiftSet, ‖w h * S.C h‖ := norm_sum_le _ _
    _ = ∑ h ∈ I.shiftSet, ‖w h‖ * ‖S.C h‖ :=
        Finset.sum_congr rfl fun h _ => norm_mul _ _
    _ ≤ ∑ _h ∈ I.shiftSet, I.target := by
        refine Finset.sum_le_sum fun h hh => ?_
        calc ‖w h‖ * ‖S.C h‖ ≤ 1 * ‖S.C h‖ :=
              mul_le_mul_of_nonneg_right (hw h hh) (norm_nonneg _)
          _ = ‖S.C h‖ := one_mul _
          _ ≤ I.target := I.bound h hh
    _ = I.shiftSet.card * I.target := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The assembled conditional all-`k` theorem.**  Given the exact partition and
the three sockets (with the linking equalities supplied as hypotheses), the
all-`k` endpoint budget follows. -/
theorem allK_endpoint_of_three_sockets (S : ShiftedMAMSourceData)
    (D : AllKFrequencyDecomposition)
    (Ismall : CharSquareSocket.EndpointCharTwistedFactorModSquareInput)
    (Imid : MidKShiftAveragedMAMInput S) (Itop : TopKFiniteShiftMAMInput S)
    (w : ℤ → ℂ) (hw : ∀ h ∈ Itop.shiftSet, ‖w h‖ ≤ 1)
    (hsmall : D.smallPart = Ismall.data.TwoStageSquareBundle Ismall.L Ismall.k)
    (hmid : D.midPart = ‖∑ h ∈ Imid.shiftSet, Imid.weight h * S.C h‖)
    (htop : D.topPart = ‖∑ h ∈ Itop.shiftSet, w h * S.C h‖) :
    D.total ≤ Ismall.desiredTarget + Imid.target + Itop.shiftSet.card * Itop.target := by
  refine allK_endpoint_compiler_v2 D _ _ _ ?_ ?_ ?_
  · rw [hsmall]; exact smallPart_le_of_charSquareInput Ismall
  · rw [hmid]; exact midPart_le_of_midKInput S Imid
  · rw [htop]; exact topPart_le_of_topKInput S Itop w hw

/-! ## 3. The canonical operator compiler -/

/-- **`allK_operator_compiler`.**  If the endpoint quantity is *exactly* the
`η`-weighted centered shift operator for a kernel of the admissible physical
class, then the operator socket gives the all-`k` budget directly. -/
theorem allK_operator_compiler (S : ShiftedMAMSourceData) (M : CanonicalLocalTerm)
    (I : ShiftedMAMFivefoldOperatorInput S M) (K : PhysicalShiftKernel)
    (hK : I.kernelClass K) (total : ℝ)
    (hdecomp : total = ‖∑ h ∈ K.shiftSet, K.eta h * Csharp S M h‖) :
    total ≤ I.requiredBudget := by
  rw [hdecomp]
  exact I.bound K hK

/-- The band-to-shift identity feeds the operator compiler: the exact finite
Fourier decomposition of a band pairing is a weighted shift sum, with no decay
assumption. -/
theorem bandPairing_is_shift_operator {M : ℕ} [NeZero M] (P : AddPhase M)
    (omega Z B : ZMod M → ℂ) :
    (M : ℂ)⁻¹ * ∑ k : ZMod M, omega k * (dft P Z k * (starRingEnd ℂ) (dft P B k))
      = ∑ r : ZMod M, bandKernel P omega r * shiftCorrelation Z B r :=
  bandPairing_eq_shiftSum P omega Z B

/-! ## 4. Firewalls -/

/-- **`allKV2_not_unconditional`.**  Without the analytic inputs the conclusion
fails: an endpoint total can exceed any sum of budgets one has not proved. -/
theorem allKV2_not_unconditional :
    ∃ D : AllKFrequencyDecomposition, ¬ (D.total ≤ 0) := by
  refine ⟨⟨1, 1, 0, 0, by norm_num⟩, ?_⟩
  norm_num

/-- **`allKV2_comparison_not_included`.**  The compilers say nothing about the
comparison main term: an all-`k` bound is consistent with the physical and
residue main terms differing. -/
theorem allKV2_comparison_not_included (D : AllKFrequencyDecomposition) (B : ℝ)
    (h : D.total ≤ B) :
    ∃ physicalMain residueMain : ℝ, D.total ≤ B ∧ physicalMain ≠ residueMain :=
  ⟨0, 1, h, by norm_num⟩

/-- The downstream Pure5 endpoint certificate needs the all-`k` bound **and** the
independent comparison pin.  Not inhabited: the pin is `SOURCE_OPEN`. -/
structure Pure5EndpointCertificateInput (D : AllKFrequencyDecomposition) where
  /-- The all-`k` budget. -/
  budget : ℝ
  /-- The all-`k` bound. -/
  allK : D.total ≤ budget
  /-- The comparison main-term pin, still `SOURCE_OPEN`. -/
  comparisonPin : Interfaces.Pure5ComparisonMainTermPin

/-- Both components are recoverable, and neither is implied by the other. -/
theorem pure5Certificate_projections (D : AllKFrequencyDecomposition)
    (C : Pure5EndpointCertificateInput D) :
    D.total ≤ C.budget ∧
      C.comparisonPin.physicalMain = C.comparisonPin.residueMain :=
  ⟨C.allK, C.comparisonPin.identified⟩

/-- **The superseded lane is not needed.**  The revised compiler derives the
all-`k` budget with no frequency-gain input: this restates
`allK_endpoint_compiler_v2` with the gain interface explicitly absent from the
hypotheses, and is the formal content of

`RANKONE-HIGHK-FREQUENCY-GAIN45 : SUPERSEDED AS FIRST TARGET`. -/
theorem allK_v2_needs_no_frequency_gain (D : AllKFrequencyDecomposition) (Bs Bm Bt : ℝ)
    (hs : D.smallPart ≤ Bs) (hm : D.midPart ≤ Bm) (ht : D.topPart ≤ Bt) :
    D.total ≤ Bs + Bm + Bt :=
  allK_endpoint_compiler_v2 D Bs Bm Bt hs hm ht

end AllKV2
end CurrentProgramme
end TwinPrimeProject
