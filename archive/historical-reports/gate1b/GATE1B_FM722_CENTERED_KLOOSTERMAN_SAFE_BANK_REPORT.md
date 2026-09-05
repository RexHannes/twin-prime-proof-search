# GATE 1B · FM722 CENTERED KLOOSTERMAN / GENERATED-DFT SAFE BANK REPORT

Append-only run.  No previous file was modified, weakened, renamed, deleted or
relocated.  The only change to an existing file is a block of **appended
imports** (with an explanatory comment) at the end of `Main.lean`.

Gate 1B is **not** proved.  Twin primes are **not** proved.  The final
generated-DFT cross-`q` analytic interface is **not** inhabited.

---

## 1. New modules

| Module | Content |
|---|---|
| `Gate1B/FM722GeneratedGammaSource.lean` | `GeneratedGammaAtomization` (finite atom index, atom coefficients, atom support intervals, product reconstruction, L1/L2 metadata, **no arbitrary-beta field**); the exponent list and its total; the **uninhabited** `FordGeneratedGammaSource` (physical source realisation left uninhabited, Ford's analytic theorem not fabricated); the balanced split for generated sources. |
| `Gate1B/FM722BalancedCoagulation.lean` | Finite real exponent lemma `balanced_coagulation` with the literal ordered first-crossing prefix; the window lemma `1/3 + sigma < 1/2`. |
| `Gate1B/FM722CenteredOneFactorCompletion.lean` | The normalised DFT convention `dftHat`/`invDFT`, Fourier inversion, Ramanujan twisting lemmas, the exact **one-factor centred completion**, the vanishing of the `k = 0` coefficient, and the **uninhabited** `RamanujanSquarefreeClosedForm` interface (arithmetic Möbius closed form, not invented). |
| `Gate1B/FM722CenteredTwoFactorKloosterman.lean` | Unit-sector sums, the **complete Kloosterman sum** `kloostermanSum`, the **centred Kloosterman kernel** `K_q(k,j;pi) = S(k, -2 j pi⁻¹; q) - c_q(k) c_q(j)/phi(q)`, and the exact **two-factor centred completion**. |
| `Gate1B/FM722CenteredDualAxes.lean` | `K_q(0,j;pi) = 0`, `K_q(k,0;pi) = 0`, and the vanishing of the axis terms in the two-factor expansion. |
| `Gate1B/FM722GeneratedDFTFourierSparsity.lean` | Parseval normalisation; `generatedDFT_sparseInverseFourier`; the full-DFT-support countermodel; the **CRT DFT nonfactorisation** countermodel. |
| `Gate1B/FM722KloostermanCRT.lean` | Additive-character CRT, the exact Kloosterman CRT factorisation, Ramanujan multiplicativity, and the deterministic centred split `S_m S_p - R_m R_p = (S_m-R_m)(S_p-R_p) + R_m(S_p-R_p) + (S_m-R_m)R_p`. |
| `Gate1B/FM722PrimeSeparationFirewall.lean` | `wp1 != wp2` for primes dividing coprime cofactors of `q_i = g r_i`. |
| `Gate1B/FM722LongLineNormalForm.lean` | The long-line Diophantine parametrisation (iff, both directions) plus the **uninhabited** `LongLineRangeData` range interface; no asymptotic `Q/P` length is formalised. |
| `Gate1B/FM722CrossQAnalyticInterface.lean` | The finite generated-DFT atom `J(q)`, its exact identity with the physical centred packet, `CrossQFamily`, `crossQCovariance` under an abstract small-gcd predicate, the deterministic split `total = diagonal + cross`, the **uninhabited** `FM722GeneratedDFTCenteredKloostermanCrossQBound`, the **uninhabited** literature-input placeholders, and the deterministic conditional compilers. |
| `Gate1B/CurrentStatusGate1BFM722Kloosterman.lean` | New authoritative append-only status layer with honesty invariants. |
| `Gate1B/AxiomAuditGate1BFM722Kloosterman.lean` | `#print axioms` for every principal new theorem. |

---

## 2. Semantic firewalls recorded

* **CRT DFT firewall.**  `hatAlpha_{m p}` is one physical sum carrying both
  additive characters; the factorisation `hatAlpha_{m p} = hatAlpha_m *
  hatAlpha_p` is **false** and is refuted by an explicit finite countermodel
  modulo 6.  No such factorisation is defined or used anywhere.
* **Full support vs sparse inverse transform.**  A DFT coefficient vector may
  have full support (proved for an explicit example).  What is proved is only
  that the *inverse* transform of `hatAlpha` is supported where `alpha` is.
  Nothing claims short support for `hatAlpha` itself.
* **No analytic bound on Kloosterman sums.**  `kloostermanSum` carries no Weil
  bound, no square-root cancellation, no analytic estimate.
* **Literature.**  Pascadi / Blomer–Pascadi inputs exist only as uninhabited
  theorem-input structures.  The literature dictionary is **under research
  audit**, not kernel-proved; no external theorem is asserted as an axiom, and
  nothing is derived from these placeholders.
* **Fixed shift.**  The shift is the fixed `+2` throughout; no averaging over
  the shift occurs anywhere.

---

## 3. Axiom audit

All `#print axioms` lines of `Gate1B/AxiomAuditGate1BFM722Kloosterman.lean`
report subsets of

```
propext, Classical.choice, Quot.sound
```

Specifically: the prime-separation theorems depend on `[propext, Quot.sound]`;
the ledger theorems on `[propext]` or on no axioms at all; every remaining
principal theorem on `[propext, Classical.choice, Quot.sound]`.

There is **no** `sorry`, **no** `sorryAx`, **no** custom `axiom`, **no**
`native_decide`, **no** `implemented_by`, **no** `unsafe` in any new module
(verified by search over all new files).

---

## 4. Build

Every new module was built individually and succeeded:

```
Gate1B.FM722GeneratedGammaSource              PASS
Gate1B.FM722BalancedCoagulation               PASS (1 linter warning, see below)
Gate1B.FM722CenteredOneFactorCompletion       PASS
Gate1B.FM722CenteredTwoFactorKloosterman      PASS
Gate1B.FM722CenteredDualAxes                  PASS
Gate1B.FM722GeneratedDFTFourierSparsity       PASS
Gate1B.FM722KloostermanCRT                    PASS
Gate1B.FM722PrimeSeparationFirewall           PASS (1 linter warning, see below)
Gate1B.FM722LongLineNormalForm                PASS
Gate1B.FM722CrossQAnalyticInterface           PASS
Gate1B.CurrentStatusGate1BFM722Kloosterman    PASS
Gate1B.AxiomAuditGate1BFM722Kloosterman       PASS
```

Warnings (both intentional, both documented in the source):

```
Gate1B/FM722BalancedCoagulation.lean:61:5  unused variable `hnonneg`
    (the source statement explicitly requires 0 <= alpha_j; the hypothesis is
     kept verbatim even though the prefix proof does not consume it)
Gate1B/FM722PrimeSeparationFirewall.lean:37:55  unused variable `hp2`
    (the source statement explicitly requires wp2 prime; kept verbatim)
```

Repository-wide build (`lake build`) — **pre-existing failure, not caused by
this run and not repaired, since repairing it would require editing or adding
legacy files**:

```
error: no such file or directory (error code: 2)
  file: /workspace/request-project/RequestProject/FixedCertificateAlgebra.lean
```

That file is absent from the repository as of its initial commit while
`K0K1Status.lean` and `RequestProject/CurrentProgramme/R9LeakageArithmetic.lean`
import it.

`lake build Gate1B` likewise fails on legacy targets only: 49 failing jobs,
comprising 13 missing legacy source files (e.g. `UniversalV8/BlockGram.lean`,
`UniversalV8/BoundedVariation.lean`, `Gate1A/Exponents.lean`,
`Gate1B/AdditiveCoordinate.lean`, …) and 51 induced `bad import` messages.
**None** of these involve any FM722 module: all twelve new modules replay
successfully inside the same invocation.

`Main.lean` elaboration stops at its pre-existing line 16 import
(`Gate04Root.*` is unavailable because the library-wide build fails above);
this is unchanged legacy behaviour.  Each newly appended import was verified to
resolve by building its module directly.

---

## 5. STRICT FINAL BLOCK

```
BALANCED COAGULATION:
KERNEL-PROVED (finite real exponent lemma, ordered whole-atom first-crossing
prefix; 1/3 <= alpha_A < 1/3 + sigma < 1/2 and 1/3 < alpha_C <= 2/3)

ONE-FACTOR CENTERED COMPLETION:
KERNEL-PROVED (exact finite identity; k = 0 coefficient proved zero)

TWO-FACTOR CENTERED COMPLETION:
KERNEL-PROVED (exact finite identity with kernel K_q(k,j;pi))

COMPLETE KLOOSTERMAN:
KERNEL-PROVED (COMPLETE-KLOOSTERMAN-PRODUCED45; no analytic bound attached)

DUAL AXES ZERO:
KERNEL-PROVED (K_q(0,j;pi) = K_q(k,0;pi) = 0 under explicit unit hypotheses)

PARSEVAL:
KERNEL-PROVED (sum_k |hatAlpha(k)|^2 = q sum_A |alpha(A)|^2; no hidden q^(1/2))

GENERATED DFT FULL SUPPORT:
ALLOWED (explicit finite example with hatAlpha nowhere zero)

GENERATED DFT SPARSE INVERSE FOURIER:
PROVED (support(inverseDFT(hatAlpha)) <= A; no short-support claim for hatAlpha)

CRT KLOOSTERMAN:
KERNEL-PROVED (character CRT, Kloosterman factorisation, Ramanujan
multiplicativity, deterministic centred split)

CRT DFT FACTORIZATION:
FALSE / FIREWALL (explicit finite countermodel; never defined or used)

PRIME-SEPARATION:
KERNEL-PROVED (wp1 != wp2, purely finite arithmetic)

LONG-LINE PARAMETRIZATION:
KERNEL-PROVED (q = q0 + pi t, T = T0 + ell t, both directions; range data
exposed as an uninhabited interface only)

FM722-GENERATEDDFT-CENTEREDKLOOSTERMAN-CROSSQ45:
UNINHABITED ANALYTIC INTERFACE (no axiom, no sorry, no instance, no default
constructor; only a deterministic conditional compiler is proved)

FM722-PRIMEWP-CRT-GENERATEDDFT-CROSSMOD-SPREAD45:
OPEN

FM722-LONGLINE-MOBIUS-GAMMA-CORRELATION45:
OPEN

HSTAR GATEEXPORT:
OPEN

GLOBAL GATE1B:
OPEN

TWIN PRIME:
OPEN

BUILD:
All 12 new modules build individually: PASS. Two intentional unused-hypothesis
linter warnings (source statements kept verbatim). Repository-wide `lake build`
fails on PRE-EXISTING missing legacy files (RequestProject/
FixedCertificateAlgebra.lean and 12 further absent legacy sources), none of
them FM722; this run neither caused nor repaired them.

AXIOM AUDIT:
PASS. Every principal new theorem depends only on subsets of
{propext, Classical.choice, Quot.sound}. No sorry, no sorryAx, no custom axiom,
no unsafe, no native_decide, no implemented_by.

STOP.
```
