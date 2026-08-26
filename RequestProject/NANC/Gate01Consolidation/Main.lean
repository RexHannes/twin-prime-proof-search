import RequestProject.NANC.Gate01Consolidation.Centering
import RequestProject.NANC.Gate01Consolidation.NonzeroOrthogonality
import RequestProject.NANC.Gate01Consolidation.ESeparation
import RequestProject.NANC.Gate01Consolidation.CRTCentering
import RequestProject.NANC.Gate01Consolidation.ShiftInverse
import RequestProject.NANC.Gate01Consolidation.PrimeCovariance
import RequestProject.NANC.Gate01Consolidation.ProductModeObstruction
import RequestProject.NANC.Gate01Consolidation.DeterminantIdentity
import RequestProject.NANC.Gate01Consolidation.DirectGaussReassembly
import RequestProject.NANC.Gate01Consolidation.R9Regrouping
import RequestProject.NANC.Gate01Consolidation.ExponentThresholds
import RequestProject.NANC.Gate01Consolidation.AnalyticInterfaces
import RequestProject.NANC.Gate01Consolidation.SourceInterfaces
import RequestProject.NANC.Gate01Consolidation.OverclaimKillTests
import RequestProject.NANC.Gate01Consolidation.StatusLedger

/-!
# Gate 0–1 consolidation bank: aggregator

Finite, algebraic, combinatorial and exponent-geometric material only:

* **A** centering / abstract source discrepancy (`Centering`);
* **B** exact E-separation (`ESeparation`);
* **C** nonzero additive orthogonality and RES_EQ (`NonzeroOrthogonality`);
* **D/E/T** CRT natural and source centering, product frequency bijection
  (`CRTCentering`);
* **F/G** shift-inverse transfer, divisor multiplicity (`ShiftInverse`);
* **H/I** prime covariance kernel and second moment (`PrimeCovariance`);
* **J** the ANOVA product-mode obstruction (`ProductModeObstruction`);
* **K** the determinant identity (`DeterminantIdentity`);
* **L/M** direct Gauss reassembly and non-unit stratification
  (`DirectGaussReassembly`);
* **N/O/P/Q** nine-block family, `4|5` regrouping, multiplicity conventions,
  optimal binary split (`R9Regrouping`);
* **R/S** completion threshold and pointwise deficit arithmetic
  (`ExponentThresholds`);
* the analytic and source interfaces, all uninhabited (`AnalyticInterfaces`,
  `SourceInterfaces`), together with the conditional implications;
* the overclaim kill tests (`OverclaimKillTests`) and the status ledger
  (`StatusLedger`).

No Gate 0, Gate 1A, Gate 1B, Ford–Maynard, FCPT, Hardy–Littlewood or twin-prime
statement is proved anywhere in this bank, and no analytic interface is ever
inhabited.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

section AxiomAudit

-- Representative theorems of the bank; each should depend only on the standard
-- axioms `propext`, `Classical.choice`, `Quot.sound`.
#print axioms esep1
#print axioms esep2
#print axioms sum_ec_nonzero
#print axioms dvd_add_two_inv_iff
#print axioms rho_mul_coprime
#print axioms rhoSrc_mul_coprime
#print axioms crtFreq_bijective
#print axioms shift_inverse
#print axioms shift_phase
#print axioms covKernel_diag
#print axioms sum_normSq_centeredForm
#print axioms zero_projections_not_imply_zero_mixed_mode
#print axioms det_identity
#print axioms gauss_phys
#print axioms linearCongruence_solution_class
#print axioms regroup_cong
#print axioms blockImbalance_min
#print axioms fourFive_crosses_completion_threshold
#print axioms weil_deficit
#print axioms finiteItems_provedFinite
#print axioms openItems_not_proved

end AxiomAudit

end Gate01Consolidation
end TwinPrimeProject
