import RequestProject.Status
import RequestProject.PrimitiveLattice
import RequestProject.PrimitiveResidue
import RequestProject.PrimitiveProgression
import RequestProject.ReciprocalIdentity
import RequestProject.DispersionDeterminants
import RequestProject.DeficitArithmetic
import RequestProject.AdditiveDivisorCalibration
import RequestProject.ABLScaleArithmetic
import RequestProject.ParityDependencyGraph
import RequestProject.FrontierStatus
-- Audited prime short-window update (this run):
import RequestProject.FiniteFieldKloosterman
import RequestProject.KloostermanOrthogonality
import RequestProject.PrimeShortWindowFourier
import RequestProject.SingularValueLowerBound
import RequestProject.FKMSExponentArithmetic
import RequestProject.FactorabilityPolytope
import RequestProject.FordMaynardThresholds
-- Audited high-P3 frontier bank (source-independent portion):
import RequestProject.MobiusFiniteDepth
import RequestProject.R9P3Repair
import RequestProject.PascadiInterfaces
import RequestProject.HighP3FrontierLedger

/-!
# Banking aggregator (Primitive Form C / balanced two-outer update)

This module re-exports the banked, machine-checked content of the update:

* `PrimitiveLattice`  — §4, §6 exact lattice identities (`LEAN_PROVED`).
* `PrimitiveResidue`  — §5 residue class / reconstruction (`LEAN_PROVED_CORE`).
* `PrimitiveProgression` — §6 solvability & progression (`LEAN_PROVED`).
* `ReciprocalIdentity` — §9 modular reciprocity (`LEAN_PROVED`).
* `DispersionDeterminants` — §10 determinant definitions (`PROVISIONAL_REDUCTION`).
* `DeficitArithmetic` — §§7,11–14,16 exponent arithmetic & conditional
  interfaces (`LEAN_PROVED` / `LEAN_PROVED_CORE`).
* `AdditiveDivisorCalibration` — §17 calibration (`LEAN_PROVED_CORE`).
* `ABLScaleArithmetic` — §21 ABL saving algebra (`LEAN_PROVED_CORE`).
* `ParityDependencyGraph` — §23 conditional parity chain (`CONDITIONAL_INTERFACE`).
* `FrontierStatus` — §18,§30 status table.

See `LEDGER.md` for the full prose ledger, dependency DAG, and the two audit
notes (Ford–Maynard numerical thresholds; ABL scale substitution).
-/
