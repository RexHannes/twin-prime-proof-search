/-
# Gate04Root.Main

Aggregator for the ROOT-COLLAPSE / R4C / PPD **finite** bank.

Everything imported here is finite algebra, modular arithmetic, finite
combinatorics or finite-dimensional linear algebra.  No analytic theorem is
proved anywhere in this library:

* `Gate04Root.Rows.DivisorGrowthInterface` (divisor bound `τ(n) ≤ X^ε`),
* `Gate04Root.R4CBound` (the R4C fourth-moment hypothesis),
* `Gate04Root.PPD` (the off-diagonal column hypothesis)

are *definitions of hypotheses*, never assumed and never proved here.
-/
import Gate04Root.Affine
import Gate04Root.GCD
import Gate04Root.BAL
import Gate04Root.CRTRoots
import Gate04Root.RootCollapse
import Gate04Root.Rows
import Gate04Root.Collisions
import Gate04Root.MatrixDuality
import Gate04Root.R4CInterfaces
import Gate04Root.PPDInterfaces
import Gate04Root.ExponentLedger

-- Appended: Gate 1B punctured / product-Fourier safe bank (append-only).
-- Exact finite linear algebra and exact arithmetic only; no analytic theorem
-- is proved or assumed by these modules.
import Gate1B.PuncturedFourierFrame
import Gate1B.PrimitiveDeterminantProductPhase
import Gate1B.CurrentStatusGate1BPuncturedProductFourier
import Gate1B.AxiomAuditGate1BPuncturedProductFourier

-- Appended: Gate 1B row-local dictionary safe bank (append-only).
-- Unconditional Bezout-row / product-difference arithmetic, the formal Leaf-4
-- local tree, the Dirichlet/additive convolution firewall, the physical
-- row-local dictionary interface (E(q), Z_E(q), kappa_4 exposed as data only),
-- the two purely logical conditional compilers, the new status layer and its
-- axiom audit.  No analytic theorem is proved or assumed by these modules.
import Gate1B.Gate1BLeaf4FormalLocalTree
import Gate1B.Gate1BLeaf4RowLocalStatus
import Gate1B.Gate1BPhysicalRowLocalDictionaryInterface
import Gate1B.CurrentStatusGate1BRowLocalDictionary
import Gate1B.AxiomAuditGate1BRowLocalDictionary

-- Appended: Gate 1B canonical full-nine / h=0 / HNE effective-conductor safe
-- bank (append-only).  Exact finite algebra, exact arithmetic and purely
-- logical conditional compilers only; every analytic input remains an
-- explicit hypothesis or interface structure.
import Gate1B.CanonicalR9Comparison
import Gate1B.FullNineCanonicalOwner
import Gate1B.CanonicalSwitchedAggregate
import Gate1B.Gate1BComparisonStability
import Gate1B.R9GlobalComparisonAdapter
import Gate1B.CanonicalHZeroCompiler
import Gate1B.HNEEffectiveConductor
import Gate1B.HNESawtoothSmallR
import Gate1B.HNEAPIndexCongruence
import Gate1B.HNEProductResidueInterface
import Gate1B.CurrentStatusGate1BCanonicalHNE
import Gate1B.AxiomAuditGate1BCanonicalHNE

-- Appended: Gate 1B HSTAR source-template safe bank (append-only).
-- lambda3/P3 convolution typing, the switched finite reindexing, exact Vaughan
-- centering against an abstract comparison sequence, the HSTAR k=0 / J=empty
-- source grammar and source-factor firewall, the determinant shell, the
-- template family type, the deterministic finite nuclear compiler, the
-- scalar-versus-family scope firewall and the Gate 1A scope firewall, the
-- open template-uniformity interfaces, the new status layer and its axiom
-- audit.  No analytic theorem is proved or assumed by these modules.
import Gate1B.VaughanLambda3P3Bridge
import Gate1B.HStarK0J0VaughanCentering
import Gate1B.HStarK0J0SourceGrammar
import Gate1B.HStarK0J0DeterminantShell
import Gate1B.HStarTemplateFamily
import Gate1B.HStarFiniteNuclearCompiler
import Gate1B.Gate1BFamilyScopeFirewall
import Gate1B.HStarTemplateUniformityInterface
import Gate1B.CurrentStatusGate1BHStarTemplates
import Gate1B.AxiomAuditGate1BHStarTemplates

-- Appended: Gate 1B HSTAR two-anchor / centred-source / Cauchy-firewall safe
-- bank (append-only).  Exact +2 two-anchor physical source algebra, the derived
-- two-T difference relations, the non-converse and single-line/independent-H
-- source-loss firewalls, the one-T versus two-T congruence firewall, the exact
-- Cauchy majorant versus exact-square firewall, the H = 0 finite arithmetic
-- router under explicit finite length hypotheses, the centred additive
-- projector and its exact zero mode, the clean Moebius-prime source typing and
-- the finite LambdaSharp source, the anchor-preserving centred covariance
-- object, the uninhabited analytic interfaces, the new status layer and its
-- axiom audit.  No analytic theorem is proved or assumed by these modules.
import Gate1B.HStarTwoAnchorPhysicalSource
import Gate1B.HStarTwoAnchorDifferenceAlgebra
import Gate1B.HStarTwoAnchorCounterguards
import Gate1B.HStarOneTTwoTFirewall
import Gate1B.HStarCenteredAdditiveProjector
import Gate1B.HStarHZeroFiniteRouter
import Gate1B.HStarMobiusPrimeSource
import Gate1B.HStarAnchorPreservingCovariance
import Gate1B.HStarAnchorPreservingAnalyticInterface
import Gate1B.CurrentStatusGate1BHStarTwoAnchor
import Gate1B.AxiomAuditGate1BHStarTwoAnchor

-- Appended: Gate 1B FM722 centred-Kloosterman / generated-DFT safe bank
-- (append-only).  The generated-Gamma atomisation interface with an
-- uninhabited source-realisation field, the finite balanced-coagulation
-- exponent lemma, the centred one-factor completion and its zero-frequency
-- vanishing, the centred two-factor completion producing a complete
-- Kloosterman sum, the dual-axis zero, Parseval normalisation, the sparse
-- inverse-Fourier theorem together with the full-DFT-support and CRT
-- nonfactorisation countermodels, the CRT Kloosterman / Ramanujan algebra and
-- the deterministic centred CRT split, the prime-separation firewall, the
-- long-line Diophantine parametrisation, the finite generated-DFT cross-q
-- object with its uninhabited analytic interface and deterministic
-- conditional compiler, the new status layer and its axiom audit.  No
-- analytic theorem is proved or assumed by these modules.
import Gate1B.FM722GeneratedGammaSource
import Gate1B.FM722BalancedCoagulation
import Gate1B.FM722CenteredOneFactorCompletion
import Gate1B.FM722CenteredTwoFactorKloosterman
import Gate1B.FM722CenteredDualAxes
import Gate1B.FM722GeneratedDFTFourierSparsity
import Gate1B.FM722KloostermanCRT
import Gate1B.FM722PrimeSeparationFirewall
import Gate1B.FM722LongLineNormalForm
import Gate1B.FM722CrossQAnalyticInterface
import Gate1B.CurrentStatusGate1BFM722Kloosterman
import Gate1B.AxiomAuditGate1BFM722Kloosterman

-- Appended: Gate 1B FM722 long-line determinant-2 safe bank (append-only).
-- The determinant-(-2) long-line parametrisation and its converse, the
-- one-atom datum A = pi z with finite anchor metadata, the odd-coprimality
-- lemma with the factor-2 case separated and refuted by countermodel, the
-- hard second-atom opening with the boxed determinant preservation
-- (A y) c1 - ell q1 = -2 and its exact bijective fibre change, the iterated
-- determinant-two opening over a finite list of atoms, the symbolic
-- slope / line-length ledger with the hard-opening capacity firewall, the
-- finite additive divisibility projector with the exact h = 0 / h != 0 split,
-- the hard-versus-soft type firewall, the centering linearity guard, the three
-- UNINHABITED analytic interfaces with their deterministic conditional
-- reassembly, the new status layer and its axiom audit.  No analytic theorem
-- is proved or assumed by these modules.
import Gate1B.FM722LongLineDiophantine
import Gate1B.FM722OneAtomLongLine
import Gate1B.FM722AtomTypeInterface
import Gate1B.FM722SecondAtomHardOpening
import Gate1B.FM722IteratedDeterminantTwo
import Gate1B.FM722LongLineLengthLedger
import Gate1B.FM722SecondAtomSoftProjector
import Gate1B.FM722LongLineCenteredInterface
import Gate1B.FM722LongLineAnalyticInterface
import Gate1B.CurrentStatusGate1BFM722LongLine
import Gate1B.AxiomAuditGate1BFM722LongLine
