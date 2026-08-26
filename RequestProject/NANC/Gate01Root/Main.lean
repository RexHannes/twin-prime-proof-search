import RequestProject.NANC.Gate01Root.AffineRoot
import RequestProject.NANC.Gate01Root.GCDRoot
import RequestProject.NANC.Gate01Root.BAL
import RequestProject.NANC.Gate01Root.CRTRoots
import RequestProject.NANC.Gate01Root.RootCollapse
import RequestProject.NANC.Gate01Root.RootCollisions
import RequestProject.NANC.Gate01Root.DivisorRows
import RequestProject.NANC.Gate01Root.MatrixFourthMoment
import RequestProject.NANC.Gate01Root.R4CInterfaces
import RequestProject.NANC.Gate01Root.RepeatedP
import RequestProject.NANC.Gate01Root.PPDInterfaces
import RequestProject.NANC.Gate01Root.SourceGConsistency
import RequestProject.NANC.Gate01Root.ExponentLedger
import RequestProject.NANC.Gate01Root.Ledger

/-!
# Gate01Root: aggregator

The ROOT-COLLAPSE / R4C / PPD **finite** delta on top of the Gate 0–1 bank.

Everything proved here is finite algebra, modular arithmetic, finite
combinatorics or finite-dimensional linear algebra.  The analytic statements
HIT-p, HIT, B-POINT, B-ROW, R4C, PPD and the Gate 0 coverage obligation exist
only as *definitions of hypotheses* and are never inhabited.
-/
