import RequestProject.NANC.Status
import RequestProject.NANC.BasicSigns
import RequestProject.NANC.CompressionSelector
import RequestProject.NANC.K0ParitySplit
import RequestProject.NANC.K0RoughRecombination
import RequestProject.NANC.PrimeReinjection
import RequestProject.NANC.GlobalRecombinationTautology
import RequestProject.NANC.PatternCount69
import RequestProject.NANC.HalfSieveCounterexample
import RequestProject.NANC.ROWPhase
import RequestProject.NANC.ROWResonance
import RequestProject.NANC.ROWDiophantineReduction
import RequestProject.NANC.ROWDiagonal
import RequestProject.NANC.ROWConcentrationInterface
import RequestProject.NANC.SameRConditional
import RequestProject.NANC.ROWFailedWeilRoute
import RequestProject.NANC.T0CRTRepair
import RequestProject.NANC.T0Compensation
import RequestProject.NANC.T0ExponentLedger
import RequestProject.NANC.T0CollisionMargin
import RequestProject.NANC.VStarVariance
import RequestProject.NANC.VStarInterfaces
import RequestProject.NANC.CDVForm
import RequestProject.NANC.CDVDiagonal
import RequestProject.NANC.CDVDoubleRepeat
import RequestProject.NANC.CDVRedundancy
import RequestProject.NANC.CDVImpliesCOOLSConditional
import RequestProject.NANC.CDVMixedCovarianceInterface
import RequestProject.NANC.ShortMassPivotFailure
import RequestProject.NANC.AnalyticInterfaces
import RequestProject.NANC.FCPTDependencyGraph
import RequestProject.NANC.CurrentBankStatus
import RequestProject.NANC.TwoPhaseCollapse
import RequestProject.NANC.WOperator
import RequestProject.NANC.D4
import RequestProject.NANC.D4.RouteABLedger

-- W4 / Salié / signed joint-hit determinant frontier supplement.
import RequestProject.NANC.W4Frontier.Basic
import RequestProject.NANC.W4Frontier.Exponents
import RequestProject.NANC.W4Frontier.PrimitiveKernel
import RequestProject.NANC.W4Frontier.DeltaShift
import RequestProject.NANC.W4Frontier.DeterminantGraph
import RequestProject.NANC.W4Frontier.Salie
import RequestProject.NANC.W4Frontier.RetiredRoutes
import RequestProject.NANC.W4Frontier.CurrentFrontier
import RequestProject.NANC.W4Frontier.BankStatus

-- Route-A fibre frame: namespace repair, fibre model, determinant identity,
-- finite Gram fourth moment, FF4 interfaces, rational exponent ledger.
import RequestProject.NANC.RouteANames
import RequestProject.NANC.FibreModel
import RequestProject.NANC.FibreDeterminant
import RequestProject.NANC.FiniteGramFourthMoment
import RequestProject.NANC.FF4Interfaces
import RequestProject.NANC.FF4ExponentLedger

-- Gate 0–1 finite bank: canonical congruence, generic CRT residue, h = 0
-- centering cancellation, same-prime / exceptional-row / Ramanujan strata,
-- the COMP completion interface, the open D* inputs with the conditional
-- AVG-COV reduction, the direct BC slot audit, and the Gate 0–1 status ledger.
import RequestProject.NANC.Gate01.CanonicalCongruence
import RequestProject.NANC.Gate01.GenericCRTResidue
import RequestProject.NANC.Gate01.HZeroCentering
import RequestProject.NANC.Gate01.SamePrimeAndExceptionalRow
import RequestProject.NANC.Gate01.CompletionInterface
import RequestProject.NANC.Gate01.DStarInterfaces
import RequestProject.NANC.Gate01.SlotDictionaryAudit
import RequestProject.NANC.Gate01.Ledger

-- ROOT-COLLAPSE / R4C / PPD finite delta (Gate01Root), built on top of the
-- Gate 0–1 bank and the standalone finite core in `Gate04Root`:
-- affine root identities, root gcd lemmas, BAL residues and CRT projections,
-- exact CRT roots, ROOT-COLLAPSE divisibility / residues / rational identity,
-- root-collision determinants, divisor-relaxed rows, the exact fourth-moment
-- row/column duality, the conditional R4C and repeated-p implications, the PPD
-- interface, the SOURCE-G exact identities, the rational exponent ledger and
-- the route status ledger.  All analytic items remain uninhabited interfaces.
import RequestProject.NANC.Gate01Root.Main

-- Switched high-P₃ finite bank (Gate01Switch), incremental on top of the
-- direct/root bank: the residue `-2` repair, the exact `λ₃` prime-power and
-- squarefree expansions, SW0 → SW1 → SW2, the prime / higher-prime-power and
-- repeated-prime splits, the generic switched operator, rational switched
-- exponent geometry, the finite local well-factorability obstruction, the
-- Vaughan divisor-switch identity audit, the `r = 9` cell audit and the Q5
-- equation, the uninhabited analytic interfaces with the finite implication
-- chain, and the switched status ledger.
import RequestProject.NANC.Gate01Switch.Main

-- The combined direct / switched gate ledger.
import RequestProject.NANC.Gate01CombinedLedger

-- Gate 0–1 consolidation bank (Gate01Consolidation): the abstract source
-- discrepancy, exact E-separation, nonzero additive orthogonality and RES_EQ,
-- natural and abstract-source CRT centering with the product-frequency CRT
-- bijection, the shift-inverse transfer and divisor multiplicity, the prime
-- covariance kernel and the exact second-moment expansion, the ANOVA
-- product-mode obstruction, the determinant identity, direct Gauss / character
-- reassembly with non-unit stratification, the nine-block family and the 4|5
-- regrouping with multiplicity conventions, the completion-threshold exponent
-- arithmetic, the uninhabited analytic / source interfaces with conditional
-- implications, the overclaim kill tests and the status ledger.
import RequestProject.NANC.Gate01Consolidation.Main

-- Switched r = 9 / 4|5 h-Poisson bridge, finite bank
-- (HPoissonComplementaryDivisor): CRT existence/uniqueness and the additive
-- inverse phase identity, the post-Poisson congruence reindexing core, the
-- complementary-divisor bijection y v − q ℓ = 2, the corrected dyadic
-- complementary-divisor exponent geometry, the centered divisor indicator and
-- its CRT expansion with the four separated centering operations, and the
-- never-inhabited analytic interfaces with conditional target-exponent
-- arithmetic.
import RequestProject.NANC.HPoissonComplementaryDivisor.Main

-- Twin Prime Gate 1B: source-native HFMV determinant bank
-- (HFMVGate1B): the complementary-divisor equivalence u v + 2 = d p l with
-- uniqueness and dyadic range variants, the exact determinant identity
-- v₂ d₁p₁l₁ − v₁ d₂p₂l₂ = 2(v₂ − v₁) with its explicit converse, the tuple
-- diagonal identity and its exact finite fibre decomposition (no analytic
-- negligibility asserted), the exact rational exponent ledger
-- 4/9, 5/9, 13/18, the B1 determinant multiplicity-one lemma and the abstract
-- finite energy inequality, and the never-inhabited analytic interfaces with
-- the deterministic HFMV assembly.
import RequestProject.NANC.HFMVGate1B.Main

-- Twin Prime Gate 1B: post-MAM45 determinant-2 deterministic bank
-- (Gate1BDet2): the Möbius prime-cofactor sign identity μ d = −μ q and the
-- weighted-cell collapse λ_{D,P}(q) = −μ(q) L_{D,P}(q) with abstract ring-valued
-- prime weight, the congruence ↔ complementary-divisor equivalence for the
-- fixed shift 2 with its integer determinant normal form, divisor rigidity
-- (gcd(u,l) ∣ 2, gcd(v,q) ∣ 2) and odd-sector coprimality, the exact affine-line
-- parametrisation of the integral points of a determinant-2 line with
-- uniqueness of the affine parameter, affine-form coprimality, the rational
-- exponent ledger (4/9, 5/9, ω, 1−ω, and ω − 4/9 = 5/18 at ω = 13/18), the
-- deterministic Phase-B measure lemmas (small-measure correlation and dyadic
-- amplitude-unbalanced layers), and the never-inhabited analytic/source
-- interfaces with their deterministic implications.
import RequestProject.NANC.Gate1BDet2.Main
