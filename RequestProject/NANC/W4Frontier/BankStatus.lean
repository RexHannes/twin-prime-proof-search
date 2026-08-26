import RequestProject.NANC.W4Frontier.CurrentFrontier

namespace TwinPrimeProject.NANC.W4Frontier

-- Established finite or algebraic bank.
def exponentLedgerStatus : BankStatus := .provedFinite
def covarianceNormalizationStatus : BankStatus := .provedAlgebraic
def unsignedJointMassStatus : BankStatus := .provedFinite
def deltaShiftStatus : BankStatus := .provedAlgebraic
def deltaShiftInjectivityLedgerStatus : BankStatus := .provedFinite
def determinantIdentitiesStatus : BankStatus := .provedAlgebraic

def twoKZDeterminantGraphLedger : LedgerItem :=
  ⟨"TWO_K_Z_DETERMINANT_GRAPH", .provedAlgebraic,
   "Active graph: pq'uv' - p'qu'v = 2kz."⟩

def twoDeltaZDeterminantGraphLedger : LedgerItem :=
  ⟨"TWO_DELTA_Z_DETERMINANT_GRAPH", .falseRoute,
   "RETIRED_FALSE_GRAPH: RHS 2delta z has an extra factor r; r(2kz) = 2delta z."⟩

def deltaShiftInjectivityLedger : LedgerItem :=
  ⟨"DELTA_SHIFT_INJECTIVITY", .provedFinite,
   "Under R^2 > M and the stated support bounds, an M-scale nonzero delta has at most one R-range prime divisor."⟩

-- Open analytic frontier and downstream gates.
def fcptStatus : BankStatus := .open
def fordTypeIIStatus : BankStatus := .open
def diffRStatus : BankStatus := .open
def cdvMixedCovarianceStatus : BankStatus := .open
def rowReciprocalConcentrationStatus : BankStatus := .open
def fullROWStatus : BankStatus := .conditional
def salieDUT3ClosureStatus : BankStatus := .open
def r2r3ExactOperatorMatchingStatus : BankStatus := .open
def fullR9CensusStatus : BankStatus := .open
def finalFordMarginAssemblyStatus : BankStatus := .open
def twinPrimesStatus : BankStatus := .open
def hardyLittlewoodStatus : BankStatus := .open

/-- The supplement deliberately has no theorem assembling FCPT. -/
def finalFCPTLedger : LedgerItem :=
  ⟨"FCPT", .open,
   "Requires the signed census, R2/R3 matching, full r=9 census, and Ford margin."⟩

end TwinPrimeProject.NANC.W4Frontier
