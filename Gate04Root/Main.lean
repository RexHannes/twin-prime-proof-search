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
