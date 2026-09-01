import Gate1B.CurrentStatusGate1BHStarTemplates
import Gate1B.HStarOneTTwoTFirewall
import Gate1B.HStarHZeroFiniteRouter
import Gate1B.HStarMobiusPrimeSource
import Gate1B.HStarAnchorPreservingAnalyticInterface

/-!
# Gate 1B · HSTAR **two-anchor** status layer (append-only)

This layer **appends** the HSTAR two-anchor rows on top of
`LedgerGate1BHStarTemplates.full`, which is imported and never edited.  Every
older status file is untouched and remains visible in its own module
(`previous_layer_preserved`).

```
KERNEL-PROVED / SAFE (this layer)
  exact two-anchor source algebra        : g e_i wp_i l_i = T_i pi_i + 2, C_i = 2
  difference equations as consequences   : T1 pi1 - T2 pi2 = g H, e1 wp1 l1 - e2 wp2 l2 = H
  difference system + anchor equivalence : (anchors) <-> (two diff lines) + (C1 = 2)
  non-converse countermodel              : diff system holds, C1 = C2 = 0 != 2
  one-T / two-T congruence firewall      : T1 pi1 = T2 pi2 mod g does NOT give pi1 = pi2 mod g
  Cauchy exact-square firewall           : majorant != exact square (explicit gap)
  H = 0 finite arithmetic router         : impossible under explicit finite length hypotheses
  centred additive zero-mode algebra     : e_q(0) - c_q(0)/phi(q) = 0, two-copy cancellation
  common-g Moebius factor algebra        : mu(g e1) mu(g e2) = mu(e1) mu(e2)
  single-line source insufficiency       : SINGLE-LINE-DELTA45 retracted as source dictionary
  independent-H source insufficiency     : independent-H energy is not a physical source

OPEN ANALYTIC (never inhabited, never promoted)
  LambdaSharp nonzero-shift cancellation
  LambdaSharp mean-square (L2) input
  physical anchored Poisson / Kloosterman landing
  HSTAR anchor-preserving centred covariance
  FM722 anchor-preserving generated-source theorem

RESEARCH STATUS
  HSTAR-K0J0-PERRON-INTEGRATED-SMALLG-ANCHORPRESERVING-
  CENTERED-MOBIUSPRIME-COVARIANCE45 : OPEN
  GLOBAL GATE1B                     : OPEN
  TWIN PRIME                        : OPEN

RETIRED PROVIDER (not a refutation)
  HSTAR-K0J0-V13-QK56-GRAM-LIFT45 : source-ill-typed for the generated-Gamma
  HSTAR packet.  The historical V13 finite algebra itself remains valid and is
  untouched.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerGate1BHStarTwoAnchor

open Status

set_option maxRecDepth 40000

/-! ## The appended ledger -/

/-- The HSTAR two-anchor layer, appended on top of
`LedgerGate1BHStarTemplates.full`. -/
def full : List LedgerEntry :=
  [ ⟨"HSTAR-TWOANCHOR-PHYSICAL-SOURCE45", Status.provedAlgebraic,
     "KERNEL-PROVED. The literal two-anchor source type with the fixed shift +2 in both anchor fields (g e_i wp_i l_i = T_i pi_i + 2), positivity and primality fields, the exact defects C1 = C2 = 2, the moduli q_i = g e_i wp_i and the +2 divisibilities. The type is inhabited (explicit witness), so no statement about it is vacuous."⟩,
    ⟨"HSTAR-TWOANCHOR-DIFFERENCE-ALGEBRA45", Status.provedAlgebraic,
     "KERNEL-PROVED. The two-T difference system is a CONSEQUENCE of the anchors: T1 pi1 - T2 pi2 = g H and e1 wp1 l1 - e2 wp2 l2 = H, with the equivalence Hnum = g H <-> quotDiff = H, the source-exact three-line system, and the recovery of anchor 2 from both difference lines plus anchor 1."⟩,
    ⟨"HSTAR-DIFFERENCE-NONCONVERSE-FIREWALL45", Status.provedFinite,
     "KERNEL-PROVED COUNTERMODEL. The difference system implies only C1 = C2. An explicit strictly positive integer configuration satisfies both difference lines with C1 = C2 = 0 != 2, so neither anchor holds. The implication 'difference equations -> C1 = 2' is refuted."⟩,
    ⟨"HSTAR-ONET-RIGIDITY45", Status.provedAlgebraic,
     "KERNEL-PROVED, ONE-T ONLY. With T1 = T2 = T and T a unit mod g: g | pi1 - pi2, and after pi1 - pi2 = g h, q_i = g r_i, the length relation r1 l1 - r2 l2 = T h."⟩,
    ⟨"HSTAR-ONET-TWOT-FIREWALL45", Status.provedFinite,
     "KERNEL-PROVED FIREWALL. A general two-T physical source gives only T1 pi1 = T2 pi2 mod g. An ACTUAL inhabitant of the physical source type (all primes genuine) has pi1 != pi2 mod g. One-T rigidity may not be transported into the pre-Cauchy Perron source."⟩,
    ⟨"HSTAR-CAUCHY-EXACT-SQUARE-FIREWALL45", Status.provedAlgebraic,
     "KERNEL-PROVED. Both objects are constructed and proved: the one-T Cauchy majorant (sum |Gamma|^2)(sum |F|^2) bounding |V|^2, and the two-T exact square V conj V = sum_{T1,T2} Gamma(T1) conj Gamma(T2) F(T1) conj F(T2). They are provably different constructions (explicit gap 0 versus 4); no theorem transports Gamma-phase information through the majorant."⟩,
    ⟨"HSTAR-HZERO-FINITE-ROUTER45", Status.provedFinite,
     "KERNEL-PROVED, CONDITIONAL ON EXPLICIT FINITE LENGTH HYPOTHESES. For coprime m_i = e_i wp_i with m1 l1 = m2 l2 one has m1 | l2 and m2 | l1; with positive lengths and l2 < m1 the H = 0 off-diagonal cell is impossible. NO asymptotic scale inequality is formalised; the separation is an explicit finite hypothesis."⟩,
    ⟨"HSTAR-CENTERED-ZERO-MODE45", Status.provedAlgebraic,
     "KERNEL-PROVED. Finite Ramanujan sum c_q(0) = phi(q), unit-sector principal model of total mass 1, the centred projector's exact zero-frequency vanishing e_q(0) - c_q(0)/phi(q) = 0, the closed Ramanujan form of the centred Fourier coefficient, and the two-copy zero-mode cancellation (+1 -1 -1 +1 = 0)."⟩,
    ⟨"HSTAR-COMMON-G-MOEBIUS45", Status.provedAlgebraic,
     "KERNEL-PROVED. On a clean squarefree cell q = d wp (wp prime, wp not dividing d), mu(q) = -mu(d); and for d_i = g e_i with g squarefree and coprime to both e_i, mu(d1) mu(d2) = mu(e1) mu(e2). NO cancellation is claimed in e1, e2 and the overclaim mu(e1) mu(e2) = 1 is refuted."⟩,
    ⟨"HSTAR-PRIME-TYPING-FIREWALL45", Status.provedFinite,
     "KERNEL-PROVED. Extracted Ford primes and Vaughan primes are separate types with distinct role tags; value equality does not identify the roles; wp > g > 0 implies wp does not divide g; and wp | q1 with wp not dividing gcd(q1,q2) implies wp does not divide q2."⟩,
    ⟨"HSTAR-LAMBDASHARP-FINITE-SOURCE45", Status.provedAlgebraic,
     "KERNEL-PROVED (deterministic part only). LambdaSharp(m) = sum_{e wp = m} mu(e) w(wp) with an abstract prime weight; support lemma, divisor-multiplicity bound tau(m) W, finite Cauchy bound, and the opened nonzero-shift relation e1 wp1 - e2 wp2 = H. Non-vacuity guard: LambdaSharp is not identically zero."⟩,
    ⟨"HSTAR-ANCHORPRESERVING-COVARIANCE-OBJECT45", Status.provedAlgebraic,
     "KERNEL-PROVED (the OBJECT, not any bound). The finite covariance built from the physical source with the exact centred factors Delta_{g e_i wp_i}(T_i pi_i); both residues are proved to be exactly -2, so the two +2 projector conditions are preserved by construction. The free H-line replacement is refuted."⟩,
    ⟨"SINGLE-LINE-DELTA45", Status.supersededAsControllingFrontier,
     "RETRACTED AS PHYSICAL SOURCE DICTIONARY. The eliminated-H line T1 pi1 - T2 pi2 = g (e1 wp1 l1 - e2 wp2 l2) is exactly equivalent to C1 = C2 and is strictly weaker than the two-anchor system. The equation is NOT false; it is insufficient."⟩,
    ⟨"INDEPENDENT-H-ENERGY45", Status.falseRoute,
     "INVALID AS A PHYSICAL SOURCE. Summing an independent product A(H) B(H) of the two difference-line energies enforces only C1 = C2; its support contains configurations that are not the raw image of any physical two-anchor source."⟩,
    ⟨"HSTAR-K0J0-V13-QK56-GRAM-LIFT45", Status.notCurrentlyRequired,
     "RETIRED AS AN HSTAR PROVIDER: source-ill-typed for the generated-Gamma HSTAR packet. This is NOT a refutation of the historical V13 finite algebra, which remains valid and is left untouched in its own modules."⟩,
    ⟨"LAMBDASHARP-NONZERO-SHIFT-BOUND45", Status.analyticOpen,
     "OPEN INTERFACE. LambdaSharpNonzeroShiftBound is never inhabited and no axiom asserts it; only consequences GIVEN an argument of that type are proved."⟩,
    ⟨"LAMBDASHARP-L2-INPUT45", Status.analyticOpen,
     "OPEN INTERFACE. The mean-square input sum |LambdaSharp|^2 << M log W is never supplied: the number-theoretic counting inputs are not formalised here."⟩,
    ⟨"ANCHORED-POISSON-KLOOSTERMAN-LANDING45", Status.analyticOpen,
     "OPEN. No Poisson / Kloosterman landing for the anchored physical source is formalised anywhere in this bank."⟩,
    ⟨"HSTAR-K0J0-PERRON-INTEGRATED-SMALLG-ANCHORPRESERVING-CENTERED-MOBIUSPRIME-COVARIANCE45",
      Status.analyticOpen,
     "CURRENT RESEARCH FRONTIER. The sole analytic residual: a power-saving bound for the exact finite anchor-preserving centred covariance. Recorded as the UNINHABITED interface HStarK0J0AnchorPreservingCovarianceBound."⟩,
    ⟨"FM722-ANCHORPRESERVING-QUADRATICDIVISOR-GENERATEDSOURCE45", Status.analyticOpen,
     "OPEN TARGET. Metadata layer only; stated exclusively for generated coefficient families and never inhabited."⟩,
    ⟨"GLOBAL-GATE1B", Status.open_, "OPEN / NOT PROMOTED."⟩,
    ⟨"TWIN-PRIME", Status.open_, "OPEN / NOT PROMOTED."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row of this layer is closed.**  Nothing is promoted. -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- Every row of this layer is honest. -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := by
  intro e he hc
  exact absurd hc (no_closed_rows e he)

/-- **The research frontier label of this layer.** -/
theorem current_research_frontier :
    ∃ e ∈ full,
      e.label =
        "HSTAR-K0J0-PERRON-INTEGRATED-SMALLG-ANCHORPRESERVING-CENTERED-MOBIUSPRIME-COVARIANCE45" ∧
      e.status = Status.analyticOpen := by decide

/-- **Global Gate 1B is not promoted.** -/
theorem global_gate1B_open :
    ∃ e ∈ full, e.label = "GLOBAL-GATE1B" ∧ e.status.isOpenObligation = true := by decide

/-- **Twin primes are not promoted.** -/
theorem twin_prime_open :
    ∃ e ∈ full, e.label = "TWIN-PRIME" ∧ e.status.isOpenObligation = true := by decide

/-- Every analytic interface row of this layer is an open obligation. -/
theorem interfaces_open :
    ∀ e ∈ full,
      (e.label = "LAMBDASHARP-NONZERO-SHIFT-BOUND45" ∨
        e.label = "LAMBDASHARP-L2-INPUT45" ∨
        e.label = "ANCHORED-POISSON-KLOOSTERMAN-LANDING45" ∨
        e.label =
          "HSTAR-K0J0-PERRON-INTEGRATED-SMALLG-ANCHORPRESERVING-CENTERED-MOBIUSPRIME-COVARIANCE45" ∨
        e.label = "FM722-ANCHORPRESERVING-QUADRATICDIVISOR-GENERATEDSOURCE45") →
      e.status.isOpenObligation = true := by decide

/-- Every exact row of this layer is a kernel-proved status. -/
theorem new_exact_rows_kernel_proved :
    ∀ e ∈ full,
      (e.label = "HSTAR-TWOANCHOR-PHYSICAL-SOURCE45" ∨
        e.label = "HSTAR-TWOANCHOR-DIFFERENCE-ALGEBRA45" ∨
        e.label = "HSTAR-DIFFERENCE-NONCONVERSE-FIREWALL45" ∨
        e.label = "HSTAR-ONET-RIGIDITY45" ∨
        e.label = "HSTAR-ONET-TWOT-FIREWALL45" ∨
        e.label = "HSTAR-CAUCHY-EXACT-SQUARE-FIREWALL45" ∨
        e.label = "HSTAR-HZERO-FINITE-ROUTER45" ∨
        e.label = "HSTAR-CENTERED-ZERO-MODE45" ∨
        e.label = "HSTAR-COMMON-G-MOEBIUS45" ∨
        e.label = "HSTAR-PRIME-TYPING-FIREWALL45" ∨
        e.label = "HSTAR-LAMBDASHARP-FINITE-SOURCE45" ∨
        e.label = "HSTAR-ANCHORPRESERVING-COVARIANCE-OBJECT45") →
      e.status.isKernelProved = true := by decide

/-- The retired V13 provider row is **not** recorded as a refutation. -/
theorem v13_provider_retired_not_refuted :
    ∃ e ∈ full, e.label = "HSTAR-K0J0-V13-QK56-GRAM-LIFT45" ∧
      e.status = Status.notCurrentlyRequired ∧ e.status ≠ Status.falseRoute := by decide

/-- **The previous layers are preserved unchanged.** -/
theorem previous_layer_preserved :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈
        LedgerGate1BHStarTemplates.full ∧
      (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈
        LedgerGate1BCanonicalHNE.full := by
  exact ⟨by decide, by decide⟩

end LedgerGate1BHStarTwoAnchor
end CurrentProgramme
end TwinPrimeProject
