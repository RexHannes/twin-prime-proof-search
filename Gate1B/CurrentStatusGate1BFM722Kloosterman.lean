import Gate1B.CurrentStatusGate1BHStarTwoAnchor
import Gate1B.FM722GeneratedGammaSource
import Gate1B.FM722CenteredDualAxes
import Gate1B.FM722GeneratedDFTFourierSparsity
import Gate1B.FM722KloostermanCRT
import Gate1B.FM722LongLineNormalForm
import Gate1B.FM722PrimeSeparationFirewall
import Gate1B.FM722CrossQAnalyticInterface

/-!
# Gate 1B · FM722 **centred Kloosterman / generated-DFT** status layer
(append-only)

This layer **appends** the FM722 centred-Kloosterman rows on top of
`LedgerGate1BHStarTwoAnchor.full`, which is imported and never edited.  Every
older status file is untouched and remains visible in its own module
(`previous_layer_preserved`).

```
KERNEL-PROVED / SAFE (this layer)
  balanced coagulation finite exponent lemma : whole-atom first-crossing prefix
  centred one-factor completion              : exact finite DFT identity
  centred two-factor completion              : complete Kloosterman produced
  dual-axis zero                             : K_q(0,j;pi) = K_q(k,0;pi) = 0
  Parseval normalisation                     : sum_k |hat alpha(k)|^2 = q sum_A |alpha(A)|^2
  sparse inverse Fourier                     : support(invDFT(hat alpha)) <= |I|
  full DFT support allowed                   : explicit full-support example
  CRT Kloosterman algebra                    : S(a,b;mp) factorisation, Ramanujan
                                               multiplicativity, centred split
  CRT DFT nonfactorisation firewall          : explicit finite countermodel
  prime-separation firewall                  : wp1 != wp2 on coprime cofactors
  long-line Diophantine parametrisation      : q = q0 + pi t, T = T0 + ell t, iff

RESEARCH LEVEL (paper/source, NOT kernel-proved here)
  FM722-GAMMA-PRESUPREMUM-ATOMFORM45  : source realisation left uninhabited

OPEN ANALYTIC (never inhabited, never promoted)
  FM722-GENERATEDDFT-CENTEREDKLOOSTERMAN-CROSSQ45
  FM722-PRIMEWP-CRT-GENERATEDDFT-CROSSMOD-SPREAD45
  FM722-LONGLINE-MOBIUS-GAMMA-CORRELATION45

LITERATURE DICTIONARY (under research audit; no external theorem assumed)
  sparse-Fourier Kloosterman input
  Blomer-Pascadi critical-block input

RESEARCH STATUS
  HSTAR GATEEXPORT : OPEN
  GLOBAL GATE1B    : OPEN
  TWIN PRIME       : OPEN
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerGate1BFM722Kloosterman

open Status

set_option maxRecDepth 40000

/-! ## The appended ledger -/

/-- The FM722 centred-Kloosterman / generated-DFT layer, appended on top of
`LedgerGate1BHStarTwoAnchor.full`. -/
def full : List LedgerEntry :=
  [ ⟨"FM722-BALANCED-COAGULATION45", Status.provedAlgebraic,
     "KERNEL-PROVED. Finite real exponent lemma: for atom exponents 0 <= alpha_j <= sigma < 1/6 with total 1 - rho, rho < 1/6, the ordered first-crossing prefix A satisfies 1/3 <= alpha_A < 1/3 + sigma < 1/2 and the complement satisfies 1/3 < alpha_C <= 2/3. No atom is split; the prefix is literal."⟩,
    ⟨"FM722-ONEFACTOR-CENTERED-COMPLETION45", Status.provedAlgebraic,
     "KERNEL-PROVED. Exact finite identity sum_A alpha(A) Delta_q(A B pi) = q^{-1} sum_k hatAlpha(k) [ e_q(-2 k (B pi)^{-1}) - c_q(k)/phi(q) ], with the k = 0 coefficient proved zero. Unit hypotheses on B, pi are explicit."⟩,
    ⟨"FM722-TWOFACTOR-CENTERED-KLOOSTERMAN45", Status.provedAlgebraic,
     "KERNEL-PROVED. Exact finite identity sum_{A,C} alpha(A) gamma(C) Delta_q(A C pi) = q^{-2} sum_{k,j} hatAlpha(k) hatGamma(j) K_q(k,j;pi) with K_q(k,j;pi) = S(k, -2 j pi^{-1}; q) - c_q(k) c_q(j)/phi(q). This banks COMPLETE-KLOOSTERMAN-PRODUCED45. NO analytic bound (no Weil bound) is attached."⟩,
    ⟨"FM722-DUAL-AXES-ZERO45", Status.provedAlgebraic,
     "KERNEL-PROVED. K_q(0,j;pi) = 0 and K_q(k,0;pi) = 0 under the explicit 2-adic unit hypothesis; the axis terms of the two-factor expansion vanish identically."⟩,
    ⟨"FM722-PARSEVAL-NORMALIZATION45", Status.provedAlgebraic,
     "KERNEL-PROVED. sum_k |hatAlpha(k)|^2 = q sum_A |alpha(A)|^2 in the repository's DFT convention. No hidden q^{1/2} factor."⟩,
    ⟨"FM722-GENERATEDDFT-SPARSE-INVERSE-FOURIER45", Status.provedFinite,
     "KERNEL-PROVED. If alpha is supported in a finite set I then the inverse transform of hatAlpha is supported in I, hence has support cardinality at most |I|. The DFT coefficient vector itself may have FULL support: an explicit finite example with hatAlpha nowhere zero is proved. No short-support claim is made for hatAlpha."⟩,
    ⟨"FM722-CENTERED-KLOOSTERMAN-CRT45", Status.provedAlgebraic,
     "KERNEL-PROVED. Additive-character CRT, the exact Kloosterman CRT factorisation S(a,b;mp) = S(a inv_p, b inv_p; m) S(a inv_m, b inv_m; p) in the repository convention, finite Ramanujan multiplicativity, and the deterministic centred split S_m S_p - R_m R_p = (S_m - R_m)(S_p - R_p) + R_m (S_p - R_p) + (S_m - R_m) R_p. No analytic claim."⟩,
    ⟨"FM722-CRT-DFT-NONFACTORIZATION-FIREWALL45", Status.provedFinite,
     "KERNEL-PROVED COUNTERMODEL. hatAlpha_{mp} is ONE physical sum carrying both additive characters; the factorisation hatAlpha_{mp} = hatAlpha_m * hatAlpha_p is FALSE. An explicit finite counterexample modulo 6 is proved."⟩,
    ⟨"FM722-PRIME-SEPARATION-FIREWALL45", Status.provedFinite,
     "KERNEL-PROVED. If q_i = g r_i with gcd(r1,r2) = 1 and primes wp_i | r_i, then wp1 != wp2. Purely finite arithmetic."⟩,
    ⟨"FM722-ANCHOR-LONGLINE-NORMALFORM45", Status.provedAlgebraic,
     "KERNEL-PROVED. For gcd(ell,pi) = 1 and one solution (q0,T0) of q ell - T pi = 2, the integer solution set is exactly { (q0 + pi t, T0 + ell t) : t in Z }; both directions proved. Asymptotic length data Q/P is NOT formalised and is exposed as a supplied range interface only."⟩,
    ⟨"FM722-GAMMA-PRESUPREMUM-ATOMFORM45", Status.externallyAudited,
     "RESEARCH LEVEL / paper-source PASS ONLY. The generated-Gamma atomisation interface (finite atom index, coefficients, support intervals, product reconstruction, L1/L2 metadata, and explicitly NO arbitrary-beta field) is formalised, but the physical source-realisation field is left UNINHABITED. Ford's analytic source theorem is not fabricated and not assumed."⟩,
    ⟨"FM722-GAMMA-BALANCED-COAGULATION45", Status.provedAlgebraic,
     "KERNEL-PROVED at the finite exponent level: any generated-source atomisation satisfying the explicit exponent hypotheses admits the whole-atom balanced split. The analytic source realisation remains uninhabited."⟩,
    ⟨"FM722-GENERATEDDFT-CROSSQ-OBJECT45", Status.provedAlgebraic,
     "KERNEL-PROVED OBJECT. The finite generated-DFT atom J(q) (arbitrary supplied lambda3 weight, prime index pi, hatAlpha_q, hatGamma_q, centred Kloosterman kernel), its exact identity with the physical centred packet, the cross-q covariance under an abstract small-gcd predicate, and the deterministic split total = diagonal + cross. No analytic bound."⟩,
    ⟨"FM722-GENERATEDDFT-CENTEREDKLOOSTERMAN-CROSSQ45", Status.analyticOpen,
     "CURRENT ANALYTIC FRONTIER / OPEN. Recorded as the UNINHABITED interface FM722GeneratedDFTCenteredKloostermanCrossQBound. Only a deterministic conditional compiler from that interface to the finite FM722 packet bound is proved; the analytic input is never derived."⟩,
    ⟨"FM722-PRIMEWP-CRT-GENERATEDDFT-CROSSMOD-SPREAD45", Status.analyticOpen,
     "OPEN. No interface is inhabited and no bound is claimed."⟩,
    ⟨"FM722-LONGLINE-MOBIUS-GAMMA-CORRELATION45", Status.analyticOpen,
     "OPEN. No interface is inhabited and no bound is claimed."⟩,
    ⟨"FM722-LITERATURE-DICTIONARY-AUDIT45", Status.externallyAudited,
     "UNDER RESEARCH AUDIT, NOT KERNEL-PROVED. The sparse-Fourier Kloosterman input and the Blomer-Pascadi critical-block input exist only as UNINHABITED theorem-input structures. No external literature theorem is formalised as an axiom, and nothing is derived from them."⟩,
    ⟨"HSTAR-GATEEXPORT", Status.open_, "OPEN / NOT PROMOTED."⟩,
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

/-- **The analytic frontier label of this layer.** -/
theorem current_analytic_frontier :
    ∃ e ∈ full,
      e.label = "FM722-GENERATEDDFT-CENTEREDKLOOSTERMAN-CROSSQ45" ∧
      e.status = Status.analyticOpen := by decide

/-- Every open analytic row of this layer is an open obligation. -/
theorem analytic_rows_open :
    ∀ e ∈ full,
      (e.label = "FM722-GENERATEDDFT-CENTEREDKLOOSTERMAN-CROSSQ45" ∨
        e.label = "FM722-PRIMEWP-CRT-GENERATEDDFT-CROSSMOD-SPREAD45" ∨
        e.label = "FM722-LONGLINE-MOBIUS-GAMMA-CORRELATION45") →
      e.status.isOpenObligation = true := by decide

/-- Every exact row of this layer is a kernel-proved status. -/
theorem new_exact_rows_kernel_proved :
    ∀ e ∈ full,
      (e.label = "FM722-BALANCED-COAGULATION45" ∨
        e.label = "FM722-ONEFACTOR-CENTERED-COMPLETION45" ∨
        e.label = "FM722-TWOFACTOR-CENTERED-KLOOSTERMAN45" ∨
        e.label = "FM722-DUAL-AXES-ZERO45" ∨
        e.label = "FM722-PARSEVAL-NORMALIZATION45" ∨
        e.label = "FM722-GENERATEDDFT-SPARSE-INVERSE-FOURIER45" ∨
        e.label = "FM722-CENTERED-KLOOSTERMAN-CRT45" ∨
        e.label = "FM722-CRT-DFT-NONFACTORIZATION-FIREWALL45" ∨
        e.label = "FM722-PRIME-SEPARATION-FIREWALL45" ∨
        e.label = "FM722-ANCHOR-LONGLINE-NORMALFORM45" ∨
        e.label = "FM722-GAMMA-BALANCED-COAGULATION45" ∨
        e.label = "FM722-GENERATEDDFT-CROSSQ-OBJECT45") →
      e.status.isKernelProved = true := by decide

/-- **The generated-Gamma source row is research level only**, never kernel
proved here. -/
theorem gamma_source_row_not_kernel_proved :
    ∃ e ∈ full, e.label = "FM722-GAMMA-PRESUPREMUM-ATOMFORM45" ∧
      e.status = Status.externallyAudited ∧ e.status.isKernelProved = false := by decide

/-- **The literature dictionary row is research level only.** -/
theorem literature_row_not_kernel_proved :
    ∃ e ∈ full, e.label = "FM722-LITERATURE-DICTIONARY-AUDIT45" ∧
      e.status.isKernelProved = false := by decide

/-- **HSTAR GateExport is not promoted.** -/
theorem hstar_gateexport_open :
    ∃ e ∈ full, e.label = "HSTAR-GATEEXPORT" ∧ e.status.isOpenObligation = true := by decide

/-- **Global Gate 1B is not promoted.** -/
theorem global_gate1B_open :
    ∃ e ∈ full, e.label = "GLOBAL-GATE1B" ∧ e.status.isOpenObligation = true := by decide

/-- **Twin primes are not promoted.** -/
theorem twin_prime_open :
    ∃ e ∈ full, e.label = "TWIN-PRIME" ∧ e.status.isOpenObligation = true := by decide

/-- **The previous layers are preserved unchanged.** -/
theorem previous_layer_preserved :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈
        LedgerGate1BHStarTwoAnchor.full ∧
      (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈
        LedgerGate1BHStarTemplates.full := by
  exact ⟨by decide, by decide⟩

end LedgerGate1BFM722Kloosterman
end CurrentProgramme
end TwinPrimeProject
