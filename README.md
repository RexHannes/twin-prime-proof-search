# Twin Prime Proof Search — Public Research Archive

**Current public manuscript:** Draft 16 (27 August 2026)

This repository is an exploratory research/proof-search archive. It does **not** claim a proof of the Twin Prime Conjecture.

## Current manuscript

- [Stable in-progress PDF](in-progress-twin-prime-proof.pdf)
- [Versioned Draft 16 PDF](twin_prime_programme_draft16.pdf)
- [Draft 16 LaTeX source](twin_prime_programme_draft16.tex)
- [Draft 16 bibliography](references_draft16.bib)
- [Draft 16 change/status ledger](README_DRAFT16.md)
- [Aristotle Gate-1B V16 reproof/reverify](ARISTOTLE_GATE1B_V16_RANKONE_BEZOUT_REPROOF_REVERIFY.md)
- [Double-GCD/Bézout source audit](SOURCE_AUDIT_DOUBLEGCD_20260827.md)
- [Rank-one source audit](SOURCE_AUDIT_RANKONE_20260827.md)
- [Draft 16 Overleaf bundle](twin_prime_programme_draft16_overleaf.zip)

## Controlling status

`GATE1B: OPEN`

First exact analytic residual:

`RANKONE-BEZOUT-AFFINE-ELLIOTT5D45`

Latest banked Gate-1B items include:

- `BETA-DP-TO-MU-LARGEPRIME45: PASS`
- `RANKONE-SHIFT-BIJECTION45: PASS`
- `LOW-PRETENTIOUS-PROFILE45: PASS`
- `ALLSHIFT-CHOWLA-TO-RANKONE45: FALSE AS A DIRECT SPLICE`
- `WRIGHT-PARTFIX-MOYK5-45: POWER NONCLOSING`

For the primitive residual, the best currently banked scale is
`Q V (log X)^(C0)` while the required scale is `Q V (log X)^(-A)`.
There is no remaining fixed-power deficit at that reduced node, but the required arbitrary-log rank-one decorrelation theorem remains unproved.

## Publication firewall

The following remain **open / not proved**:

- Gate 1B;
- the full Type-II chain required by the programme;
- twin-prime infinitude.

No Hardy–Littlewood asymptotic is claimed. Research-level internal reductions are kept distinct from published theorems and from machine-checked finite identities.

## Reproducibility

Draft 16 is published from the checked-in LaTeX/bibliography source. The publication workflow verifies the exact source checksums before compiling and updating the stable PDF path.

## Aristotle

This project has used [Aristotle](https://aristotle.harmonic.fun) for formal reproof/reverification work. The Aristotle prompts and ledgers are audit aids; unresolved analytic bounds are deliberately kept uninhabited rather than introduced as axioms.
