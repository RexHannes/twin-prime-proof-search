# Gate 1A / Gate 1B Dependency Graph — 31 August 2026

This file is a current high-level dependency overlay. Older dependency graphs remain historical records of earlier frontiers.

## Status legend

- **[L]** kernel-proved finite/algebraic theorem
- **[A]** audited analytic/source-compiler result outside Lean
- **[C]** conditional interface/compiler
- **[S]** source/global bridge open
- **[O]** open

## Gate 1A

```mermaid
graph TD
  AFIN["Gate 1A finite/kernel provider bank [L]"]
  ASRC["source interfaces + Gate0→1A bridge [S/O]"]
  AAN["external analytic inputs/interfaces [C/O]"]
  AGL["Global Gate 1A [O]"]

  AFIN --> AGL
  ASRC --> AGL
  AAN --> AGL
```

Controlling public status:

`GATE1A: OPEN`.

The finite/kernel bank is substantial, but this graph does not promote source/interface hypotheses into results.

## Gate 1B — fresh canonical balanced-`R_9`

```mermaid
graph TD
  H0["Canonical h=0 HIGH-HIGH / C2 [A CLOSED]"]
  HNE["HNE / C3 [A CLOSED]"]
  LD["Lower-D / C4 [A CLOSED]"]
  C5["Canonical balanced-R9 Gate1B / C5 [A CLOSED]"]
  AD["R9 canonical→global adapter / C6 [S OPEN]"]
  G1B["Global Gate 1B [O]"]

  H0 --> C5
  HNE --> C5
  LD --> C5
  C5 --> AD
  AD --> G1B
```

The final HNE repair is the source-level two-copy AP Fourier projection:

`HNE-APINDEX-2D-APFOURIER-PROJECTION45: PASS`.

There is no remaining internal analytic residual in the frozen canonical balanced-`R_9` branch.

The global bridge is:

```text
Delta_R9^adapter
  = b_9^can - P_R9 b^FM
```

with target `||Delta_R9^adapter||_G <= 1` plus exact zero-mode comparison.

## Global downstream firewall

```mermaid
graph TD
  G1A["Global Gate 1A [O]"]
  G1B["Global Gate 1B [O]"]
  SRC["Global source/provider census [O/S]"]
  GEN["TWIN_GENERATED_TYPEII_CLOSED [O]"]
  FULL["TWIN_FULL_TYPEII_CLOSED [O]"]
  G2["Gate 2 / Ford–Maynard compiler [C]"]
  TP["Twin Prime Conjecture [O]"]

  G1A --> GEN
  G1B --> GEN
  SRC --> GEN
  GEN --> FULL
  FULL --> G2
  G2 --> TP
```

No arrow in this graph is supplied merely by using the same phrase “Type II”. Each export requires a literal source/range/coefficient dictionary.

## Comparison architecture

```mermaid
graph LR
  FM["global positive comparison b^FM"]
  PR["P_R9 projection"]
  AD["Delta_R9 adapter"]
  CAN["packet-local signed b_9^can"]
  AN["closed canonical Gate1B analytic compiler"]

  FM --> PR --> AD --> CAN --> AN
```

The packet-local `b_9^can` must not be promoted to the global Ford–Maynard `b`: its global prime-mass contract fails. The adapter is the explicit bridge between the two roles.

## Historical formulation

The historical switched `E_hist` remains a source/specification pin for the legacy statement, but is bypassed by the explicit canonical packet theorem. It must not be silently identified with `b_9^can` or the canonical switched aggregate.
