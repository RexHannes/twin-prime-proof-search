# BANKED

This directory contains material trusted at its **stated evidence level**. `BANKED` does not mean every item is Lean-formalised.

## Evidence classes

- [`formal/`](formal/) — kernel-checked exact/finitary mathematics and formal status reports.
- [`audited-analytic/`](audited-analytic/) — analytic results independently audited but not necessarily Lean-formalised.
- [`manuscripts/`](manuscripts/) — audited public manuscript releases.
- [`certificates/`](certificates/) — finite/replay certificates where present.

The evidence label controls. A paper-audited result must not be silently promoted to a Lean theorem, and a conditional compiler must not be treated as an inhabited analytic input.
