# Draft 16 — 27 Aug 2026 controlling Gate-1B update

Draft 16 supersedes Draft 15 for the overall programme status.

## Controlling mathematical change

Draft 15 stopped at the pure-five-defect coherent projector / fully-crossed
entropy-gap child.  The later 27 Aug audits reduce that child further.

Banked in Draft 16:

- `FULLCROSS-LARGEPRIME-DIVISOR-MULT2-45: PASS`;
- `FULLCROSS-DEFECT-GCD-ROUTER45: PASS`;
- `FULLCROSS-DOUBLEGCD-BEZOUT45: PASS`;
- `DP-FACTOR-INJECTIVE-BEZOUTLINE45: PASS`;
- `DOUBLEGCD-LARGE-GS-TAIL45: PASS`;
- `FULLCROSS-RIGIDITY-ONLY-CLOSURE45: FAILED ROUTE`;
- `MRK5-SOURCE-RECOVERED: PASS`;
- `MOYK5-SOURCE-KERNEL-MANUFACTURE45: PASS`;
- `MOYK5-QK5-REPRESENTATION-ANTILOOP45: PASS`;
- `BETA-DP-TO-MU-LARGEPRIME45: PASS`, namely
  `beta_{D,P}(n) = -mu(n) L_{D,P}(n)` on the clean squarefree cell;
- `RANKONE-SHIFT-BIJECTION45: PASS`;
- `ALLSHIFT-CHOWLA-TO-RANKONE45: FALSE AS A DIRECT SPLICE`;
- `WRIGHT-PARTFIX-MOYK5-45: POWER NONCLOSING`;
- `LOW-PRETENTIOUS-PROFILE45: internal analytic PASS`.

The first exact analytic residual is now

`RANKONE-BEZOUT-AFFINE-ELLIOTT5D45`.

It is the primitive `g=s=1` child of
`PURE5-DP-DOUBLEGCD-BEZOUT-LINE45`, written with the literal Möbius carrier
and the physical rank-one shift family.  The current best banked scale is

`Q V (log X)^(C0)`

against the required

`Q V (log X)^(-A)`.

There is therefore no remaining fixed-power deficit in this primitive
post-Cauchy residual, but the arbitrary-log joint decorrelation theorem is
still open.

## Literature audit added

Draft 16 adds explicit scope checks for:

- Matomäki–Radziwiłł–Tao averaged Chowla (`arXiv:1503.05121`);
- Tao–Teräväinen logarithmic correlation structure (`arXiv:1708.02610`);
- Klurman–Mangerel–Teräväinen short AP variance (`arXiv:1909.12280`);
- Jizhou Guo, quantitative logarithmic Chowla with growing shifts
  (`arXiv:2608.23500`);
- Thomas Wright, partially fixed modulus trilinear Kloosterman fractions
  (`arXiv:2604.25177`);
- Blomer–Pascadi all-moduli bilinear Kloosterman bounds
  (`arXiv:2607.24311`).

None is promoted to a direct provider for the rank-one five-defect theorem.

## Publication firewall

- Gate 1B: OPEN.
- `RANKONE-BEZOUT-AFFINE-ELLIOTT5D45`: OPEN.
- Pure-five-defect comparison/main-term pin: SOURCE OPEN.
- Lower-defect faces: not inferred from the five-defect case.
- `r>1` square-character family: OPEN.
- CSTAR–CNW transition strip: OPEN.
- QK56 full parent / exhaustiveness: OPEN.
- Full Type II: OPEN.
- Ford–Maynard downstream source adapter: OPEN / conditional.
- Twin-prime infinitude: NOT PROVED.

## Build audit

- LaTeX/Biber: PASS
- PDF pages: 69
- undefined citations/references: 0
- overfull boxes: 0
- all-page render: PASS
- visual audit of title and Late Update VIII: PASS
- Draft 15 -> Draft 16 render comparison: completed

Draft 16 does not update the stable public GitHub PDF unless a separate push is
explicitly requested.
