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
