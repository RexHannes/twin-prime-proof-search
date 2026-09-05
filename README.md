# Twin Prime Proof Search

**Status: OPEN. No proof of the Twin Prime Conjecture is claimed.**

This repository is a public research and formal-verification programme around the Ford–Maynard / fixed-shift Twin-Prime route. The public surface is organised by **evidence and current relevance**, not by the historical order in which intermediate gates were invented.

## Start here

- **[Proof map](PROOF_MAP.md)** — the full current dependency DAG.
- **[Current status](CURRENT_STATUS.md)** — the shortest audited + live-candidate status page.
- **[Claims ledger](CLAIMS_LEDGER.md)** — claim-by-claim evidence and status.
- **[Banked work](banked/)** — material trusted at its stated evidence level.
- **[Current frontier](frontier/)** — what is actually worth attacking now.
- **[Graveyard](graveyard/)** — false, retired and superseded routes.
- **[Corrections and retractions](CORRECTIONS_AND_RETRACTIONS.md)** — public status firewall.
- **[Archive](archive/)** — historical manuscripts, safe-bank reports and source archaeology.

## Current picture

### Audited baseline — 5 September 2026 R11 release

```text
CARD5 / source geometry / Vaughan V=2 / affine determinant   BANKED [Lean]
abstract finite Hilbert-HMRD                                BANKED [Lean]
rough-modulus variance                                      BANKED [analytic + audit]
former Sector A                                             CLOSED at stated conditional scope
physical Hilbert-HMRD caller                                RETIRED / NONCLOSING
old FSHC three-sector architecture                          SUPERSEDED
R_hi                                                        OPEN in audited R11
R11                                                         OPEN
Global Gate1B                                               OPEN
HSTAR                                                       OPEN
Twin Prime                                                  OPEN
```

Read the audited R11 paper at [`banked/manuscripts/gate1b-r11-2026-09-05/`](banked/manuscripts/gate1b-r11-2026-09-05/).

### Live post-R11 research frontier

The latest candidate recompiler reduces the physical signed square to three pieces:

```text
shared-prime rows          candidate power-small
near m=n strip             candidate log-small
coprime far-separated      OPEN
```

with current target

```text
Q_cp,far << X^2 L^{-2 S0}.
```

Candidate reductions do **not** supersede the audited R11 ledger until independently reviewed.

## Gate 1A

Gate1A / BP-VLF4 is currently **DORMANT / NONCONTROLLING / NOT CLOSED**. It disappeared from the live dependency path because the Ford endgame was recompiled, not because Gate1A was proved.

## Repository layout

```text
banked/       trusted formal / audited analytic / manuscript material
frontier/     current wall / candidate reductions / downstream / dormant nodes
graveyard/    false / retired / superseded routes
archive/      historical reports, old manuscripts and research archaeology

RequestProject/
Gate1A/
Gate1B/
Universal/
UniversalV8/
Gate04Root/   stable formal/source trees retained for imports and reproducibility
```

The stable source directories remain at their existing paths deliberately; cosmetic relocation must not break Lean imports or historical reproducibility.

## Scope firewall

Do not infer any of the following from local or banked progress:

```text
local closure => R11
R11 => Global Gate1B without source census/reassembly
Global Gate1B => HSTAR without the required reconciliation
any of the above => Twin Prime
```

The Twin Prime Conjecture remains open in this repository.
