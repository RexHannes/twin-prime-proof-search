import RequestProject.NANC.W4Frontier.DeterminantGraph
import RequestProject.NANC.W4Frontier.PrimitiveKernel
import RequestProject.NANC.W4Frontier.Salie
import RequestProject.NANC.W4Frontier.RetiredRoutes

namespace TwinPrimeProject.NANC.W4Frontier

inductive FibreKind where
  | z_eq_zero
  | pprime_dvd_z
  | q_dvd_z
  | mprime_eq_zero_mod_qprime
  | A_eq_Aprime_mod_qprime
  | same_time_prime_collision
  | cross_time_prime_collision
  | salie_large_w_correlation
  deriving DecidableEq, Repr

inductive FibreStatus where
  | closed
  | harmless
  | lowerDimensionalButAboveTarget
  | newObstruction
  | open
  deriving DecidableEq, Repr

/-- No fibre is silently classified in this supplement. In particular, no
finite exponent identity is promoted to an analytic counting bound. -/
def initialFibreStatus (_ : FibreKind) : FibreStatus := .open

theorem all_fibres_initially_open (f : FibreKind) :
    initialFibreStatus f = .open := rfl

def signedJointHitDeterminantCensusStatus : BankStatus := .open
def genericSignedMeanValueStatus : BankStatus := .open
def salieLargeWFibres5And8Status : BankStatus := .open

def currentFrontier : LedgerItem :=
  ⟨"SIGNED_JOINT_HIT_CENSUS", .open,
   "Signed census on the corrected graph pq'uv' - p'qu'v = 2kz, with delta = kr and shifted P3 constraints."⟩

def genericSignedMeanValue : LedgerItem :=
  ⟨"GENERIC_SIGNED_MEAN_VALUE", .open,
   "Square-root cancellation for the generic signed census remains open."⟩

def salieLargeWFibres5And8 : LedgerItem :=
  ⟨"SALIE_LARGE_W_FIBRES_5_AND_8", .open,
   "Open pending exact assembly; no analytic fibre bound is claimed."⟩

def noDecouplingRule : LedgerItem :=
  ⟨"CENSUS_FIRST_NO_DECOUPLING_CAUCHY", .open,
   "The target has exponent 2 while unsigned joint mass has exponent 4."⟩

end TwinPrimeProject.NANC.W4Frontier
