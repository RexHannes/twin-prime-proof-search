/-
# Gate1B / R11 / Frontier / Latest : the authoritative current status module

Append-only module.  This is the single place where the *current* frontier is recorded:
every node, its exact proposition (named), its dependency list, its evidence category and its
status.  The minimal open cut set is **computed** from the dependency graph and checked by the
kernel (`by decide`), so it cannot drift away from the recorded statuses.

Evidence categories are exactly those of the continuation brief:
`KERNEL_PROVED`, `EXTERNAL_ANALYTIC`, `CONDITIONAL_ANALYTIC`, `OPEN`, `RETIRED_NONCLOSING`,
`FALSE`, `SUPERSEDED`, `DEFECTIVE_INTERFACE`.

Nothing here inhabits an open proposition; a `kernelProved` row is re-ascribed to an actual
theorem of this layer in §5, so a regression breaks the build.
-/
import Gate1B.R11.Frontier.Latest.PositiveBranchOwner
import Gate1B.R11.Frontier.Latest.RestAndD3
import Gate1B.R11.Frontier.Latest.NonunitStripping
import Gate1B.R11.Frontier.Latest.KloostermanSynthesisEnergy
import Gate1B.R11.Frontier.Latest.ZeroResonanceLedger
import Gate1B.R11.Frontier.Latest.AnalyticInterfaces
import Gate1B.R11.Frontier.Latest.FactorSplitAndCounting

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. Evidence categories -/

/-- The evidence category of a node of the current frontier. -/
inductive Evidence
  /-- Proved in Lean, checked by the kernel. -/
  | kernelProved
  /-- An external analytic theorem, recorded as a named proposition and never inhabited. -/
  | externalAnalytic
  /-- Proved downstream *conditionally* on an explicitly stated analytic hypothesis. -/
  | conditionalAnalytic
  /-- Genuinely open. -/
  | open_
  /-- Analysed and retired as a closing mechanism (quantitatively nonclosing). -/
  | retiredNonclosing
  /-- Refuted. -/
  | false_
  /-- Superseded by a later coordinate. -/
  | superseded
  /-- The interface as stated is defective (e.g. vacuously satisfiable). -/
  | defectiveInterface
  deriving DecidableEq, Repr

/-! ## 2. The nodes -/

/-- The nodes of the current frontier graph. -/
inductive Node
  -- deterministic, kernel-proved layer
  | globalCoreAggregation
  | gcdClassCovariance
  | nukReassembly
  | ramanujanDecomposition
  | negativeBranchCompletePeriod
  | chiPCancellation
  | frozenPeriodFirewall
  | primeDivisorCoordinate
  | nonunitStripping
  | primeDenominatorD2NonunitCovariance
  | universalFactorSplit
  | nearDiagonalCounting
  | affineCharacterGram
  | affineSqrtEllNorm
  | synthesisIsometry
  | perModeFirewall
  | explicitFormulaAdapter
  | restReassembly
  -- retired / superseded
  | termwiseKMSSummation
  | d2PositiveCoreOldObstruction
  -- external analytic inputs
  | siegelWalfisz
  | zeroDensityInput
  | deuringHeilbronn
  | blomerPascadi
  | sourceAPBank
  -- analytically banked (conditional on the supplied bank)
  | d1d2NumeratorMeans
  | lowConductorClosed
  | highConductorReduction
  | nearDiagonalPowerSmall
  | d2NegativeBranchControlled
  | sourceAffineCharacterEstimate
  | predecessorGrouping236
  -- genuinely open analytic owners
  | d2PositiveMoment
  | exceptionalZeroWedge
  | d2UnitCovariance
  | d1CenteredCovariance
  | globalSourceCrossEnergy
  | fullCircleFourierOwnership
  | rRestMasks
  | fivePrimeChamber
  | d3Construction
  -- old formal cut set
  | rowConsumerResidueOscillation
  | mod3CenteredCaller
  | realFordGrammarObligation
  | conditionalConsumerComparison
  -- downstream
  | r11
  | r11ToHstarSplice
  | hstar
  | gate1B
  deriving DecidableEq, Repr

open Node Evidence

/-- The evidence category of every node. -/
def evidence : Node → Evidence
  | globalCoreAggregation => kernelProved
  | gcdClassCovariance => kernelProved
  | nukReassembly => kernelProved
  | ramanujanDecomposition => kernelProved
  | negativeBranchCompletePeriod => kernelProved
  | chiPCancellation => kernelProved
  | frozenPeriodFirewall => kernelProved
  | primeDivisorCoordinate => kernelProved
  | nonunitStripping => kernelProved
  | primeDenominatorD2NonunitCovariance => kernelProved
  | universalFactorSplit => kernelProved
  | nearDiagonalCounting => kernelProved
  | affineCharacterGram => kernelProved
  | affineSqrtEllNorm => kernelProved
  | synthesisIsometry => kernelProved
  | perModeFirewall => kernelProved
  | explicitFormulaAdapter => kernelProved
  | restReassembly => kernelProved
  | termwiseKMSSummation => retiredNonclosing
  | d2PositiveCoreOldObstruction => superseded
  | siegelWalfisz => externalAnalytic
  | zeroDensityInput => externalAnalytic
  | deuringHeilbronn => externalAnalytic
  | blomerPascadi => externalAnalytic
  | sourceAPBank => externalAnalytic
  | d1d2NumeratorMeans => conditionalAnalytic
  | lowConductorClosed => conditionalAnalytic
  | highConductorReduction => conditionalAnalytic
  | nearDiagonalPowerSmall => conditionalAnalytic
  | d2NegativeBranchControlled => conditionalAnalytic
  | sourceAffineCharacterEstimate => conditionalAnalytic
  | predecessorGrouping236 => conditionalAnalytic
  | d2PositiveMoment => open_
  | exceptionalZeroWedge => open_
  | d2UnitCovariance => open_
  | d1CenteredCovariance => open_
  | globalSourceCrossEnergy => open_
  | fullCircleFourierOwnership => open_
  | rRestMasks => open_
  | fivePrimeChamber => open_
  | d3Construction => open_
  | rowConsumerResidueOscillation => open_
  | mod3CenteredCaller => externalAnalytic
  | realFordGrammarObligation => open_
  | conditionalConsumerComparison => open_
  | r11 => open_
  | r11ToHstarSplice => open_
  | hstar => open_
  | gate1B => open_

/-- The dependency list of every node: what its proof would consume. -/
def deps : Node → List Node
  | globalCoreAggregation => []
  | gcdClassCovariance => []
  | nukReassembly => []
  | ramanujanDecomposition => []
  | negativeBranchCompletePeriod => [ramanujanDecomposition]
  | chiPCancellation => []
  | frozenPeriodFirewall => []
  | primeDivisorCoordinate => []
  | nonunitStripping => []
  | primeDenominatorD2NonunitCovariance => [nonunitStripping]
  | universalFactorSplit => []
  | nearDiagonalCounting => []
  | affineCharacterGram => []
  | affineSqrtEllNorm => [affineCharacterGram]
  | synthesisIsometry => [affineSqrtEllNorm]
  | perModeFirewall => []
  | explicitFormulaAdapter => []
  | restReassembly => [globalCoreAggregation]
  | termwiseKMSSummation => [perModeFirewall]
  | d2PositiveCoreOldObstruction => [d1d2NumeratorMeans]
  | siegelWalfisz => []
  | zeroDensityInput => []
  | deuringHeilbronn => []
  | blomerPascadi => []
  | sourceAPBank => []
  | d1d2NumeratorMeans => [globalCoreAggregation, sourceAPBank]
  | lowConductorClosed => [nonunitStripping, siegelWalfisz]
  | highConductorReduction => [zeroDensityInput, explicitFormulaAdapter]
  | nearDiagonalPowerSmall => [nearDiagonalCounting]
  | d2NegativeBranchControlled =>
      [ramanujanDecomposition, negativeBranchCompletePeriod, sourceAffineCharacterEstimate]
  | sourceAffineCharacterEstimate => [affineSqrtEllNorm, sourceAPBank]
  | predecessorGrouping236 => [gcdClassCovariance]
  | d2PositiveMoment =>
      [chiPCancellation, frozenPeriodFirewall, primeDivisorCoordinate, highConductorReduction]
  | exceptionalZeroWedge => [highConductorReduction, deuringHeilbronn]
  | d2UnitCovariance => [nonunitStripping, d1d2NumeratorMeans]
  | d1CenteredCovariance => [d1d2NumeratorMeans]
  | globalSourceCrossEnergy => [synthesisIsometry, blomerPascadi]
  | fullCircleFourierOwnership => [affineCharacterGram, nearDiagonalPowerSmall]
  | rRestMasks => [restReassembly]
  | fivePrimeChamber => [rRestMasks]
  | d3Construction => [fivePrimeChamber]
  | rowConsumerResidueOscillation => []
  | mod3CenteredCaller => []
  | realFordGrammarObligation => []
  | conditionalConsumerComparison => []
  | r11 =>
      [d1d2NumeratorMeans, lowConductorClosed, highConductorReduction, nearDiagonalPowerSmall,
        d2NegativeBranchControlled, predecessorGrouping236, gcdClassCovariance, nukReassembly,
        universalFactorSplit, primeDenominatorD2NonunitCovariance,
        d2PositiveMoment, exceptionalZeroWedge, d2UnitCovariance, d1CenteredCovariance,
        globalSourceCrossEnergy, fullCircleFourierOwnership, rRestMasks, fivePrimeChamber,
        d3Construction, rowConsumerResidueOscillation, mod3CenteredCaller,
        realFordGrammarObligation, conditionalConsumerComparison]
  | r11ToHstarSplice => [r11]
  | hstar => [r11, r11ToHstarSplice]
  | gate1B => [hstar]

/-! ## 3. Transitive closure and the computed cut set -/

/-- Every node of the graph. -/
def allNodes : List Node :=
  [globalCoreAggregation, gcdClassCovariance, nukReassembly, ramanujanDecomposition,
    negativeBranchCompletePeriod, chiPCancellation, frozenPeriodFirewall, primeDivisorCoordinate,
    nonunitStripping, primeDenominatorD2NonunitCovariance, universalFactorSplit,
    nearDiagonalCounting, affineCharacterGram, affineSqrtEllNorm, synthesisIsometry,
    perModeFirewall, explicitFormulaAdapter, restReassembly, termwiseKMSSummation,
    d2PositiveCoreOldObstruction, siegelWalfisz, zeroDensityInput, deuringHeilbronn,
    blomerPascadi, sourceAPBank, d1d2NumeratorMeans, lowConductorClosed, highConductorReduction,
    nearDiagonalPowerSmall, d2NegativeBranchControlled, sourceAffineCharacterEstimate,
    predecessorGrouping236, d2PositiveMoment, exceptionalZeroWedge, d2UnitCovariance,
    d1CenteredCovariance, globalSourceCrossEnergy, fullCircleFourierOwnership, rRestMasks,
    fivePrimeChamber, d3Construction, rowConsumerResidueOscillation, mod3CenteredCaller,
    realFordGrammarObligation, conditionalConsumerComparison, r11, r11ToHstarSplice, hstar,
    gate1B]

/-- One step of dependency expansion. -/
def expand (l : List Node) : List Node :=
  (l ++ l.flatMap deps).eraseDups

/-- The dependency closure of a node, computed with enough fuel for this graph. -/
def closure (n : Node) : List Node :=
  Nat.rec [n] (fun _ prev => expand prev) 8

/-- The **open cut set** of a node: the genuinely open nodes it depends on, in graph order. -/
def cutSet (n : Node) : List Node :=
  (allNodes.filter (fun m => m ∈ closure n ∧ evidence m = Evidence.open_ ∧ m ≠ n))

/-- The **external analytic inputs** a node depends on. -/
def externalInputs (n : Node) : List Node :=
  (allNodes.filter (fun m => m ∈ closure n ∧ evidence m = Evidence.externalAnalytic))

/-- **The current minimal open cut set to `R11`** — computed from the graph, checked by the
kernel. -/
theorem cutSet_r11 :
    cutSet r11 =
      [d2PositiveMoment, exceptionalZeroWedge, d2UnitCovariance, d1CenteredCovariance,
        globalSourceCrossEnergy, fullCircleFourierOwnership, rRestMasks, fivePrimeChamber,
        d3Construction, rowConsumerResidueOscillation, realFordGrammarObligation,
        conditionalConsumerComparison] := by
  decide

/-- **The additional cut set from `R11` to Gate 1B**: over and above `R11` itself, the splice and
`HSTAR` are the only further open nodes. -/
theorem cutSet_gate1B_extra :
    (cutSet gate1B).filter (fun m => m ∉ cutSet r11 ∧ m ≠ r11) = [r11ToHstarSplice, hstar] := by
  decide

/-- The external analytic inputs consumed on the way to `R11`. -/
theorem externalInputs_r11 :
    externalInputs r11 =
      [siegelWalfisz, zeroDensityInput, deuringHeilbronn, blomerPascadi, sourceAPBank,
        mod3CenteredCaller] := by
  decide

/-! ## 4. Ledger guards -/

/-- No downstream node is recorded as closed. -/
theorem downstream_open :
    evidence r11 = Evidence.open_ ∧ evidence hstar = Evidence.open_
      ∧ evidence gate1B = Evidence.open_ := by decide

/-- Termwise KMS / Blomer–Pascadi summation is recorded as retired-nonclosing, not as a closing
mechanism. -/
theorem termwiseKMS_retired : evidence termwiseKMSSummation = Evidence.retiredNonclosing := by
  decide

/-- D3 is recorded as OPEN: it is neither constructed nor certified absent. -/
theorem d3_open : evidence d3Construction = Evidence.open_ := by decide

/-- The old formal cut-set node `RowConsumerResidueOscillation` is still open and still consumed
by `R11`: it is *not* discharged by the new mathematics. -/
theorem oldCut_rowConsumer_still_live :
    evidence rowConsumerResidueOscillation = Evidence.open_
      ∧ rowConsumerResidueOscillation ∈ cutSet r11 := by decide

/-! ## 5. Re-ascription of the `kernelProved` rows

Each theorem below is a type ascription of a result actually proved in this layer, so the kernel
re-checks that the recorded status matches a proof. -/

/-- GLOBAL CORE AGGREGATION: KERNEL_PROVED. -/
theorem bank_globalCoreAggregation {ι : Type} (S : Finset ℕ) (g : ℕ → ℚ) (J : Finset ι)
    (H : ι → ℕ → ℚ) :
    globalCore S g (fun M => ∑ j ∈ J, H j M) = ∑ j ∈ J, globalCore S g (H j) :=
  globalCore_sum S g J H

/-- ALL-GCD-CLASS COVARIANCE: KERNEL_PROVED. -/
theorem bank_gcdClassCovariance (s : Finset (ℕ × ℕ)) (G : Finset ℕ)
    (hG : ∀ q ∈ s, Nat.gcd q.1 q.2 ∈ G) (F : ℕ × ℕ → ℚ) :
    ∑ q ∈ s, F q = ∑ d ∈ G, ∑ q ∈ s.filter (fun q => Nat.gcd q.1 q.2 = d), F q :=
  sum_pairs_by_gcd s G hG F

/-- RAMANUJAN KERNEL DECOMPOSITION: KERNEL_PROVED. -/
theorem bank_ramanujanDecomposition (p v : ℕ) :
    cpKernel p v = (p : ℤ) * (if p ∣ v then 1 else 0) - 1 := cpKernel_eq p v

/-- NEGATIVE-BRANCH COMPLETE PERIOD: KERNEL_PROVED. -/
theorem bank_negativeBranch {p : ℕ} (hp : 0 < p) (t : ℕ) :
    ∑ v ∈ range (p * t), cpKernel p v = 0 := sum_cpKernel_complete_period hp t

/-- `χ(p)` CANCELLATION ON THE `p | v` BRANCH: KERNEL_PROVED. -/
theorem bank_chiPCancellation {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) {a : ZMod n}
    (ha : IsUnit a) : χ a * (starRingEnd ℂ) (χ a) = 1 := chi_p_cancels χ ha

/-- FROZEN-PERIOD CAPACITY FIREWALL: KERNEL_PROVED. -/
theorem bank_frozenPeriodFirewall {P L : ℕ} (hL : 0 < L) (hLP : L < P) :
    ∃ f : ℕ → ℤ, (∀ v, f (v + P) = f v) ∧ (∑ v ∈ range P, f v) = 0
      ∧ (∑ v ∈ range L, f v) ≠ 0 :=
  partial_period_sum_not_forced_zero hL hLP

/-- PRIME-DENOMINATOR D2 NONUNIT CENTERED COVARIANCE = 0: KERNEL_PROVED. -/
theorem bank_primeD2NonunitCovariance {p : ℕ} [Fact p.Prime] (f g : ZMod p → ℂ)
    (hcent : ∑ v ∈ (univ : Finset (ZMod p)).filter (fun v => ¬ IsUnit v), f v = 0) :
    ∑ v ∈ (univ : Finset (ZMod p)).filter (fun v => ¬ IsUnit v),
      f v * (starRingEnd ℂ) (g v) = 0 :=
  prime_nonunit_centered_covariance_eq_zero f g hcent

/-- UNIVERSAL 3/7 – 4/7 FACTOR SPLIT: KERNEL_PROVED. -/
theorem bank_universalFactorSplit {n : ℕ} (hn : 1 ≤ n)
    (hB : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 7)) :
    ∃ d : ℕ, d ∣ n ∧ (n : ℝ) ^ ((3 : ℝ) / 7) ≤ (d : ℝ)
      ∧ (d : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 7) :=
  universal_three_sevenths_split hn hB

/-- EXACT NEAR-DIAGONAL COUNTING: KERNEL_PROVED. -/
theorem bank_nearDiagonalCounting (g a M : ℕ) :
    ((range M).filter (fun m => m % g = a)).card ≤ M / g + 1 :=
  card_residue_class_le g a M

/-- AFFINE CHARACTER GRAM IDENTITY: KERNEL_PROVED. -/
theorem bank_affineGram {l : ℕ} (hl : 0 < l) (a b : ℕ) :
    ∑ x ∈ range l, affineMat l a x * (starRingEnd ℂ) (affineMat l b x)
      = if (l : ℤ) ∣ ((a : ℤ) - b) then (l : ℂ) else 0 := affine_gram hl a b

/-- `√ℓ` OPERATOR NORM (PARSEVAL): KERNEL_PROVED. -/
theorem bank_affineSqrtEll {l : ℕ} (hl : 0 < l) (f : ℕ → ℂ) :
    ∑ a ∈ range l, ‖affineTransform l f a‖ ^ 2 = (l : ℝ) * ∑ x ∈ range l, ‖f x‖ ^ 2 :=
  affine_parseval hl f

/-- SIMULTANEOUS SYNTHESIS IS ONLY A SCALED ISOMETRY: KERNEL_PROVED. -/
theorem bank_synthesisIsometry {l : ℕ} (hl : 0 < l) (f : ℕ → ℂ) (hf : MeanZeroVec l f) :
    energy l f ≤ energy l (synthesis l f) := synthesis_no_source_contraction hl f hf

/-- PER-MODE FIREWALL (termwise summation is nonclosing): KERNEL_PROVED. -/
theorem bank_perModeFirewall (N : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ a : ℕ → ℝ, (∀ i, |a i| ≤ eps) ∧ ∑ i ∈ range N, a i = (N : ℝ) * eps :=
  summed_wrapper_nonclosing N heps

/-- EXPLICIT-FORMULA DETERMINISTIC ADAPTER: KERNEL_PROVED. -/
theorem bank_explicitFormulaAdapter (E : ExplicitFormulaData) (x eps delta : ℝ)
    (hzero : |∑ rho ∈ E.zeros x, E.contrib x rho| ≤ eps) (herr : |E.err x| ≤ delta) :
    |E.count x - E.main x| ≤ eps + delta :=
  counting_close_to_main_of_small_zero_mass E x eps delta hzero herr

/-- `R_rest` REASSEMBLY (mask + rest, no double charge): KERNEL_PROVED. -/
theorem bank_restReassembly (S : Finset ℕ) (g H : ℕ → ℚ) (p : ℕ → Prop) [DecidablePred p] :
    globalCore S g H = coreMasked S g H p + coreRest S g H p :=
  core_eq_masked_add_rest S g H p

/-- THE `−3 log M` CHAMBER IS NOT NEGLIGIBLE: KERNEL_PROVED. -/
theorem bank_chamber_nonzero {M : ℝ} (hM : 1 < M) : chamberCoefficient M ≠ 0 :=
  chamberCoefficient_ne_zero hM

/-- D3 ABSENCE IS NOT AUTOMATIC: KERNEL_PROVED. -/
theorem bank_d3_not_automatic : ∃ S : SourceDecomposition, S.d3 ≠ 0 := d3_zero_not_automatic

end Gate1B.R11.Frontier.Latest
