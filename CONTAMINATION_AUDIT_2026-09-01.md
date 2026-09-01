# Project contamination audit — 1 September 2026

## Repository audited

`RexHannes/twin-prime-proof-search`

## Active scope

Fixed-shift / Ford–Maynard / Twin-Prime programme only.

## Pre-existing cross-project material found

The tree inherited several late-August #287-specific research notes/prompts and mixed current-status/dependency-graph rows. These predated the 1-Sep cleanup.

## Cleanup performed

Removed from the current tree (preserved in Git history):

- `ERDOS287_CURRENT_RESEARCH_LEDGER_2026-08-29.md`
- `NEXT_ARISTOTLE_ERDOS287_BALANCED7_REPAIR_2026-08-29.md`
- `NEXT_PRO_ERDOS287_BALANCED7_XYZ_CLOSE_2026-08-29.md`
- `RESEARCH_FRONTIERS/ERDOS287_PROOF_INDEX.md`
- `RESEARCH_FRONTIERS/ERDOS287_PRIMITIVEFRACTION_CASEB_2026-08-30.md`

Replaced the living mixed layers with project-local versions:

- `RequestProject/CurrentProgramme/CurrentStatus.lean`
- `RequestProject/CurrentProgramme/DependencyGraph.lean`
- `RESEARCH_FRONTIERS/CURRENT_FRONTIERS.md`
- `CURRENT_GATE_ARCHITECTURE_AND_STATUS.md`
- `CURRENT_PROGRAMME_MASTER_CONTINUATION_REPORT.md`
- `ARISTOTLE_SUMMARY.md`
- `README.md`

The verified cleanup build compiled the living status ledger and project-local dependency graph and passed the automated cross-project active-label scan before merge.

## Generic-lemma firewall

Source-neutral finite/algebraic lemmas may remain reusable. Their presence does not import a separate problem's source realization, status, analytic theorem or conclusion.

## Public-status firewall

```text
GATE1B: OPEN
FULL_FM_TYPEII: OPEN
TWIN_PRIME_CONJECTURE: OPEN
```

No Erdős-#287 theorem is an active dependency of this conclusion graph.
