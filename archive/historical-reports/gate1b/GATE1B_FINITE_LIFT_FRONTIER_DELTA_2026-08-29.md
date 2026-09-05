# GATE 1B — FINITE-LIFT FRONTIER DELTA (2026-08-29)

Tiny delta report for the recovery run.  Banking only: no new analytic estimate
was attacked, no historical status semantics was changed, and Gate 1B is not
closed.

## LARGE-LIFT

**RESEARCH CLOSED.**  At research/paper level the large-lift dispersion is
closed (`DETLINE-LARGE-LIFT-DISPERSION45`), together with
`DETLINE-CONDUCTOR-LE-Y45` (power closed) and the large-lift cells of
`TOPBAND-BETA-BROADMINOR-DETLINE45`.  Recorded as `externallyAudited`
metadata — **not** kernel-proved here, and no analytic antecedent is inhabited.

## FINITE-LIFT

**OPEN.**  Surviving range

```
1 ≤ e ≤ (log X)^{B_A},   ell = c·e ~ R,   c ~ R (log X)^{-O_A(1)}.
```

The research-level exact-lift energy consequences
`E_{G,2}(e) ≪ e^{-1} Y^{29/2} log^{O(1)} X`,
`E_{R,2}(e) ≪ R Y e^{-2} log^{O(1)} X`, hence
`|T_j(e)| ≪ X e^{-3/2} log^{O(1)} X` (uniform for j = 1,…,5), are recorded as
research results only.  The single formal consequence banked is the abstract
order-arithmetic tail budget
`LedgerFiniteLift.finiteLift_tail_budget`, whose per-lift bound and tail-sum
input are hypotheses; with `E = (log X)^{B_A}` this is the arbitrary-logarithmic
saving used at research level.

## CURRENT FIRST EXACT RESIDUAL

`DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45` — `analyticOpen`.

Supporting rows: `DETLINE-FINITELIFT-NEARPRIM-REDUCTION45` (pass / reduced),
`DETLINE-HIGHCOND-DENSE-SATURATION-EXCLUSION45` (closed for log-large lifts,
open for finite lifts), `DETLINE-HIGHCOND-BETA-RHO-CROSSPAIR45` (partially
closed / strictly reduced, not false), `DETLINE-CONDUCTOR-LOCAL-G-ENERGY45`
(exact fixed-lift form, partial gain).

## FORMAL OPERATOR SOCKET

`SHIFTED-MAM-FIVEFOLD-OPERATOR45` remains the broader **analytic-open formal
interface** (`MAMOperator.ShiftedMAMFivefoldOperatorInput`, uninhabited).  It is
kept explicitly distinct from the research residual
(`LedgerFiniteLift.formal_socket_distinct_from_research_frontier`).

## GATE1B

**OPEN.**

## New files this run

- `RequestProject/CurrentProgramme/CurrentStatusGate1BFiniteLift.lean`
  (status layer; targeted build PASS)
- `RequestProject/CurrentProgramme/AxiomAuditGate1BFiniteLift.lean`
  (trust audit; targeted build PASS)

Trust: every new declaration depends only on `propext`, `Classical.choice`,
`Quot.sound` or fewer; no `sorryAx`.  Token scan of the two new files finds no
`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]` outside documentation text.

Status-vocabulary note: the repository taxonomy has no `researchClosed` or
`partial` constructor.  No misleading `closed` was invented; the nearest honest
statuses were used and the finer meaning is carried in each row's note.

## GLOBAL BUILD

**BLOCKED BY PRE-EXISTING LEGACY FAILURE** (unrelated to this recovery run; not
repaired, per the banking-only scope).

- Exact file: `RequestProject/CurrentProgramme/R9LeakageArithmetic.lean`
  (and the root-level `K0K1Status.lean`).
- Exact missing declaration/import: `import RequestProject.FixedCertificateAlgebra`
  — the module `RequestProject.FixedCertificateAlgebra` is absent from this
  workspace (`RequestProject/` contains only `CurrentProgramme/` and `NANC/`;
  a root-level `FixedCertificateAlgebra.lean` exists but lies outside the
  `RequestProject.+` library glob of `lakefile.toml`).
- Lake reports: `error: no such file or directory ... RequestProject/FixedCertificateAlgebra.lean`.

Proof that all modules relevant to this run build: targeted `lake build` PASSES
for `EndpointShiftedDeterminant`, `EndpointCharacterTransfer`,
`EndpointHighKBandKernel`, `EndpointShiftedMAM`, `EndpointCharacterPairing`,
`EndpointShiftedMAMOperatorSocket`, `EndpointAllKCompilerV2`,
`CurrentStatusShiftedMAMOperator`, `AxiomAuditShiftedMAMOperator`,
`CurrentStatusGate1BFiniteLift`, `AxiomAuditGate1BFiniteLift`
(8061 jobs, 0 errors).  None of these imports the missing legacy module.
