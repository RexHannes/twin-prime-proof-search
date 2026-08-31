import Gate1B.CurrentStatusGate1BRowLocalDictionary
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

/-!
# Gate 1B · canonical full-nine / `h = 0` / HNE status layer (append-only)

This layer **appends** the canonical-R9 and HNE rows on top of
`LedgerGate1BRowLocalDictionary.full`, which is imported and never edited.  The
older status files are untouched; every historical row remains visible and
unchanged in its own module (`previous_layer_preserved`).

```
PUNCTURED FOURIER FRAME      : kernelProved   (previous layer, preserved)
PRODUCT FOURIER              : kernelProved   (previous layer, preserved)
PRIMITIVE DETERMINANT        : kernelProved   (previous layer, preserved)
FULL-NINE CANONICAL OWNER    : kernelProved   (this layer)
CANONICAL SWITCHED RESIDUAL  : kernelProved   (this layer, tautological)
CANONICAL h = 0              : analyticResearchClosed / formalConditionalCompiler
HISTORICAL h = 0             : sourcePin
HNE EFFECTIVE CONDUCTOR      : analyticResearchBanked (exact algebra kernelProved)
SAWTOOTH LARGE-r TAIL        : analyticResearchBanked
SMALL-r NORMAL FORM          : kernelProved (arithmetic factor)
AP-INDEX CONGRUENCE          : kernelProved
HNE                          : open / strictlyReduced
LOWER-D                      : open
GLOBAL R9 ADAPTER            : open
HISTORICAL E                 : sourcePin
GATE1B                       : open

CLOSURE LEVELS : C2 CLOSED, C3 STRICTLY REDUCED, C4 OPEN, C5 OPEN.

CURRENT FIRST ANALYTIC RESIDUAL :
  C4SHIFT-HNE-SMALLR-LOWCOND-APINDEX-CONGRUENCE45.
CURRENT GLOBAL SOURCE/COMPILER RESIDUAL :
  R9-CANONICAL-TO-GLOBAL-COMPARISON-ADAPTER45.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerGate1BCanonicalHNE

open Status

set_option maxRecDepth 40000

/-! ## The appended ledger -/

/-- The canonical-R9 / HNE layer, appended on top of
`LedgerGate1BRowLocalDictionary.full`. -/
def full : List LedgerEntry :=
  [ ⟨"R9-COORDINATE-CANONICAL-SPLIT45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: pi_i = m_i_can + rho_i - e_i_pp from pi_i = f_i + delta_i - e_i_pp, delta_i = lambda_i + rho_i, m_i_can = f_i + lambda_i. Exact; no approximation."⟩,
    ⟨"CANONICAL-OCCUPANCY-MODEL45", Status.provedAlgebraic,
     "b9CellCan with EXPLICIT factorial normalisation and Dirichlet convolution powers; b9Can is the finite sum over the physical occupancy family. Labelled source is never replaced by symmetric source."⟩,
    ⟨"CANONICAL-TOTALMASS-MULTINOMIAL45", Status.provedAlgebraic,
     "Exact finite degree-nine multinomial identity for the complete family, plus the exact finite polynomial for an arbitrary subfamily. Total mass is an INTERFACE (TotalMass), never inhabited."⟩,
    ⟨"ZERO-FREQUENCY-RHO-MASS45", Status.conditionalCompiler,
     "sum rho = 0 is derived from the projector interface ZeroFrequencyProjector (value 1 at zero frequency), which is an explicit hypothesis, not a theorem of this repository."⟩,
    ⟨"FULLNINE-FIRSTREMAINDER-TELESCOPE45", Status.provedAlgebraic,
     "BOXED: prod pi - prod m_can = sum_j (prod_{i<j} m_can) (rho_j - e_j_pp) (prod_{i>j} pi). Exact telescope; P_0 and P_9 identified."⟩,
    ⟨"FIRSTREMAINDER-OWNER-UNIQUE45", Status.provedFinite,
     "Unique smallest non-model coordinate; disjoint owner fibres; exact ownership partition of labelled expansion terms."⟩,
    ⟨"OCCUPANCY-SYMMETRISATION-FIREWALL45", Status.provedAlgebraic,
     "Finite occupancy summation with factorial normalisation preserves the linear telescoping identity. No hidden multiplicity, no double counting."⟩,
    ⟨"PRIMEPOWER-OWNER45", Status.conditionalCompiler,
     "The e_i_pp owner is explicit and counted exactly once. The analytic X^(-1/18+o(1)) saving is NOT formalised; PrimePowerCorrectionBound is an interface. Research analytic status: POWER-SPARSE CLOSED."⟩,
    ⟨"SWITCHED-MODULUS-TYPE-FIREWALL45", Status.provedFinite,
     "SwitchedModulus and MajorArcDenominator are distinct structures; no coercion exists; any identification is an explicit choice."⟩,
    ⟨"LAMBDA3-ORDERED-DIVISOR-PAIRS45", Status.provedAlgebraic,
     "lambda3Sw over Nat.divisorsAntidiagonal equals the divisors form; ordered divisor-pair multiplicity is retained (witness: q = 6 has four ordered pairs)."⟩,
    ⟨"CANONICAL-SWITCHED-RESIDUAL45", Status.provedAlgebraic,
     "BOXED: RCan = 0. TAUTOLOGICAL: it holds only because the canonical comparison aggregate is DEFINED from the same b9Can. Countermodel shows an arbitrary expected coefficient gives a nonzero residual."⟩,
    ⟨"HISTORICAL-E45", Status.sourceOpen,
     "SOURCE PIN. E_hist is an abstract parameter, is never defined by b9Can, and is provably not identified with the canonical expected coefficient."⟩,
    ⟨"R9-PACKET-COMPARISON-ADMISSIBILITY45", Status.provedAlgebraic,
     "R9CanonicalPacketComparison contains only the internal Gate1B needs. No positivity, no Euler multiplicativity, no global prime mass. A signed instance exists."⟩,
    ⟨"GLOBAL-B9CAN-PRIMEMASS-OBSTRUCTION45", Status.provedAlgebraic,
     "b9Can AS GLOBAL FM COMPARISON: FAIL by prime-mass obstruction. Kernel content: a ninefold convolution of coordinates whose supports exclude a prime p vanishes at p. No asymptotic Y^9 vs Y L^C claim."⟩,
    ⟨"P2-CANONICAL-CORRECTION45", Status.provedAlgebraic,
     "c9 - b9CanOdd = (c9 - b9Can) + Delta2, exactly. Delta2 is NOT claimed small; it is routed to the q = 2 local-owner interface."⟩,
    ⟨"COMPARISON-STABILITY45", Status.provedAlgebraic,
     "Deterministic compiler stability: T(w') = T(w) - T(Delta), Z(b') = Z(b) + Z(Delta), M(b') = M(b) + M(Delta), the compiler seminorm, and gate1B_comparison_stability."⟩,
    ⟨"R9-TWOCOMPARISON-ADAPTER-IDENTITY45", Status.provedAlgebraic,
     "PR9(a - bFM) = (c9 - b9Can) + DeltaAdapter under PR9(a) = c9. Exact linear algebra."⟩,
    ⟨"R9-CANONICAL-TO-GLOBAL-COMPARISON-ADAPTER45", Status.analyticOpen,
     "CURRENT GLOBAL SOURCE/COMPILER RESIDUAL. R9CanonicalToGlobalAdapterBound is an interface only; a countermodel shows it is not automatic."⟩,
    ⟨"CANONICAL-HZERO-HIGHHIGH45", Status.conditionalCompiler,
     "Research: ANALYTICALLY CLOSED for the fresh balanced-R9 packet. Formal: canonicalHZeroHighHigh_of_bank, a logical compiler whose twelve owner premises are explicit and unsupplied."⟩,
    ⟨"HNE-APRECIPROCAL-EFFECTIVE-CONDUCTOR45", Status.provedAlgebraic,
     "Exact conductor reduction e_ell(C m^-1 n^-1) = e_qEff(C0 (m mod qEff)^-1 (n mod qEff)^-1) with qEff = ell/gcd(C,ell), plus exact compressed-L2 fibre bounds. Research threshold qEff >= Y^(3/2) L^B is metadata only."⟩,
    ⟨"SAWTOOTH-R-NONZERO45", Status.provedAlgebraic,
     "r = d k - u rho is nonzero when gcd(d,u) = 1 and 0 < rho < d. Exact division identity d k = u rho + r."⟩,
    ⟨"SAWTOOTH-LARGE-R-TAIL45", Status.externallyAudited,
     "Research: arbitrary-log CLOSED for |r| > d L^B. Formal content: only the finite implication from a SUPPLIED decay bound to the L2 tail estimate. SawtoothCoefficientDecay is an interface."⟩,
    ⟨"SMALLR-RECIPROCAL-NORMALFORM45", Status.provedAlgebraic,
     "Exact frequency offset rho/d - k/u = -r/(du): the moving index k is absent from the normal form and survives only through r. Unit scalar and Archimedean phase are explicit parameters."⟩,
    ⟨"SMALLR-CR-GR-QR-DATA45", Status.provedAlgebraic,
     "C_r, g_r = gcd(C_r, ell), q_r = ell/g_r with exact divisibility and reduced coprimality."⟩,
    ⟨"C4SHIFT-HNE-SMALLR-LOWCOND-APINDEX-CONGRUENCE45", Status.analyticOpen,
     "CURRENT FIRST ANALYTIC RESIDUAL. The exact arithmetic (d h = r s mod g_r) is kernel-proved; the analytic closure of the residual operator is open."⟩,
    ⟨"HNE-APINDEX-CONGRUENCE45", Status.provedAlgebraic,
     "BOXED and unconditional: on the clean unit/odd sector, g_r | C_r iff d h = r s (mod g_r)."⟩,
    ⟨"HNE-APINDEX-SOURCE-ENERGY45", Status.analyticOpen,
     "OPEN INTERFACE. Explicitly NOT proved: a countermodel shows arbitrary coefficients saturate one residue class, so no coefficient-blind K/g bound follows from cardinality."⟩,
    ⟨"PRODUCT-RESIDUE-REFORMULATION45", Status.provedAlgebraic,
     "Exact finite algebra: sum over d h = r s (mod g) equals sum_x A_x B_x; Cauchy compiler; additive-Fourier indicator identity and the factorisation into two bilinear Fourier forms."⟩,
    ⟨"PRODUCT-RESIDUE-ENERGIES45", Status.analyticOpen,
     "ProductResidueEnergyDH and ProductResidueEnergyRS are interfaces; no physical bound is invented."⟩,
    ⟨"C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS FIRST HNE FRONTIER (historical label preserved in the earlier layers, unchanged)."⟩,
    ⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS FIRST CANONICAL h=0 FRONTIER for the fresh canonical R9 packet (historical label preserved in the earlier layers, unchanged)."⟩,
    ⟨"C2", Status.closed, "CLOSED (kernel-proved rows of the earlier layers)."⟩,
    ⟨"C3", Status.open_, "STRICTLY REDUCED."⟩,
    ⟨"C4", Status.open_, "OPEN."⟩,
    ⟨"C5", Status.open_, "OPEN."⟩,
    ⟨"HNE", Status.open_, "OPEN / STRICTLY REDUCED."⟩,
    ⟨"LOWER-D", Status.open_,
     "OPEN. Current first Lower-D vertex: the SAME AP-index congruence packet, with the research conditions D < Y^(3/4) L^(-B*), |r| <= d L^B, q_r < Y^(3/2) L^C, d h = r s (mod g_r) carried as Prop fields."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- The only `closed` row of this layer is the closure level `C2`, whose
justification is the kernel-proved algebra of the earlier layers. -/
theorem only_C2_closed :
    ∀ e ∈ full, e.status = Status.closed → e.label = "C2" := by decide

/-- **The layer is honest**: a `closed` row is backed by a kernel-proof
status. -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := by
  intro e _ hc
  rw [hc]
  rfl

/-- Gate 1B remains open at this layer. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by decide

/-- HNE and Lower-D remain open at this layer. -/
theorem hne_and_lowerD_open :
    ∀ e ∈ full, (e.label = "HNE" ∨ e.label = "LOWER-D" ∨ e.label = "GATE1B") →
      e.status.isOpenObligation = true := by decide

/-- **The current first analytic residual.** -/
theorem current_first_analytic_residual :
    ∃ e ∈ full,
      e.label = "C4SHIFT-HNE-SMALLR-LOWCOND-APINDEX-CONGRUENCE45" ∧
        e.status = Status.analyticOpen := by decide

/-- **The current global source/compiler residual.** -/
theorem current_global_source_residual :
    ∃ e ∈ full, e.label = "R9-CANONICAL-TO-GLOBAL-COMPARISON-ADAPTER45" ∧
      e.status = Status.analyticOpen := by decide

/-- **Superseded, not deleted and not false**: both historical labels are
recorded here as superseded frontiers only. -/
theorem superseded_frontiers :
    (∃ e ∈ full, e.label = "C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45" ∧
        e.status = Status.supersededAsControllingFrontier) ∧
      ∃ e ∈ full, e.label = "TOPBAND-BROAD-MAJOR-TREE-MATCH45" ∧
        e.status = Status.supersededAsControllingFrontier := by decide

/-- **The previous layers are preserved unchanged**: the row-local layer still
carries its own `GATE1B` row and its own superseded `C4SHIFT` row, and the
punctured/product-Fourier layer still carries its `analyticOpen` `C4SHIFT`
row. -/
theorem previous_layer_preserved :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈
        LedgerGate1BRowLocalDictionary.full ∧
      (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈
        LedgerPuncturedProductFourier.full ∧
      ∃ e ∈ LedgerPuncturedProductFourier.full,
        e.label = "C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45" ∧
          e.status = Status.analyticOpen := by
  refine ⟨by decide, by decide, ?_⟩
  exact LedgerPuncturedProductFourier.first_analytic_residual

/-- **The new exact rows are kernel-proved algebra.** -/
theorem new_exact_rows_kernel_proved :
    ∀ e ∈ full,
      (e.label = "R9-COORDINATE-CANONICAL-SPLIT45" ∨
        e.label = "FULLNINE-FIRSTREMAINDER-TELESCOPE45" ∨
        e.label = "FIRSTREMAINDER-OWNER-UNIQUE45" ∨
        e.label = "OCCUPANCY-SYMMETRISATION-FIREWALL45" ∨
        e.label = "CANONICAL-SWITCHED-RESIDUAL45" ∨
        e.label = "COMPARISON-STABILITY45" ∨
        e.label = "R9-TWOCOMPARISON-ADAPTER-IDENTITY45" ∨
        e.label = "HNE-APRECIPROCAL-EFFECTIVE-CONDUCTOR45" ∨
        e.label = "HNE-APINDEX-CONGRUENCE45" ∨
        e.label = "PRODUCT-RESIDUE-REFORMULATION45") →
      e.status.isKernelProved = true := by decide

/-- **The analytic/research rows are never kernel proofs.** -/
theorem analytic_rows_not_kernel_proved :
    ∀ e ∈ full,
      (e.label = "CANONICAL-HZERO-HIGHHIGH45" ∨
        e.label = "SAWTOOTH-LARGE-R-TAIL45" ∨
        e.label = "HNE-APINDEX-SOURCE-ENERGY45" ∨
        e.label = "PRODUCT-RESIDUE-ENERGIES45" ∨
        e.label = "R9-CANONICAL-TO-GLOBAL-COMPARISON-ADAPTER45" ∨
        e.label = "PRIMEPOWER-OWNER45" ∨
        e.label = "ZERO-FREQUENCY-RHO-MASS45" ∨
        e.label = "HISTORICAL-E45") →
      e.status.isKernelProved = false := by decide

/-- **The canonical `h = 0` compiler does not close Gate 1B.** -/
theorem canonicalHZero_does_not_close_gate1B :
    (∃ e ∈ full, e.label = "CANONICAL-HZERO-HIGHHIGH45" ∧
        e.status = Status.conditionalCompiler) ∧
      ∃ e ∈ full, e.label = "GATE1B" ∧ e.status = Status.open_ := by decide

/-- **Closure levels**, as recorded rows. -/
theorem closure_levels :
    (∃ e ∈ full, e.label = "C2" ∧ e.status = Status.closed) ∧
      (∃ e ∈ full, e.label = "C3" ∧ e.status = Status.open_) ∧
        (∃ e ∈ full, e.label = "C4" ∧ e.status = Status.open_) ∧
          ∃ e ∈ full, e.label = "C5" ∧ e.status = Status.open_ := by decide

end LedgerGate1BCanonicalHNE
end CurrentProgramme
end TwinPrimeProject
