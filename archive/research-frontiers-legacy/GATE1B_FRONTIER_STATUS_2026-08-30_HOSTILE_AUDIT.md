# Gate 1B — Frontier Snapshot — 30 August 2026

**Status:** `GATE1B OPEN`

This is an append-only research snapshot. It records the hostile-audited state after retracting the attempted same-`u` closure.

## Safe closed range

```math
D\ge Y^{3/4}L^{-B_*}
```

remains closed. The lower-`D` range remains open.

## Stable bank

The following survive audit:

- centered `q,v` source splice repaired;
- exact same-`u` physical AP coordinates;
- `2x2` modulo-`ell` residue system for `(Z_-,Z_+)` has unit determinant;
- fixed-`ell` physical `Z` pair is unique in the short boxes;
- quotient `(r,k)` normal form;
- AP-sampling multiplicity second moment
  ```math
  \sum_{\mathbf z}m(\mathbf z)^2\ll Y^8D^{-2}L^C;
  ```
- cross-`u` algebra
  ```math
  (q,u_i)=1,
  \qquad
  \ell_1\equiv\ell_2\pmod{(u_1,u_2)}.
  ```

## First exact source residual

For `j=1`, the pure-defect leaf has the required `alpha_j,gamma_j` eighth moments. For `j=2,3,4,5`, the model coordinate high moment is not source-banked.

Required source theorem:

```math
\sum_{n\asymp Y}\tau(n)^7|\lambda_i(n)|^8\ll YL^C.
```

Current node:

```text
C4SHIFT-BEZOUT-SOURCE-ALPHAGAMMA-L8-45
```

Status:

```text
j=1: PASS
j=2,3,4,5: SOURCE PIN
GLOBAL: PARTIAL PASS / SOURCE PIN
```

## Retracted same-u compiler promotion

The previous attempted diagonal closure is withdrawn.

Reason 1: the old safe estimate

```math
\mathcal N_D^{safe}\ll Y^{9/8}D^{-1/2}L^C
```

is an `L^1_theta ell_v^2` norm; it does not imply a Plancherel `L^2_theta ell_v^2` energy bound by squaring.

Reason 2: the `alpha/gamma` source had already been compressed into the old `Gamma` `L^2` norm before the attempted AP-sampling block replacement. Therefore the AP-sampling factor cannot simply be multiplied onto that old estimate.

Withdraw:

```text
E_D^safe << Y^(9/4)D^(-1) as an inferred Plancherel theorem
E_diag(D) << Y^(3/2)D^(-2)L^C from block replacement
SAMEU-PHYSICAL-AP-GRAM45: CLOSED
```

## First analytic/compiler residual

After the source high-moment pin, the direct target is

```text
C4SHIFT-BEZOUT-
LOWERD-SAMEU-
SOURCEDIAGONAL-NORMALIZATION45
```

It requires a direct normalized positive Plancherel-energy estimate from the literal physical source, with all Fourier/AP/Mellin/local normalisations retained and AP sampling inserted before any global source compression.

## Dependent same-u children

```text
SAMEU-H0-SOURCEWEIGHTED-PRODUCTENERGY45: SOURCE PIN
SAMEU-HNE-SHIFTEDCORRELATION45: SOURCE PIN
SAMEU-PHYSICAL-AP-GRAM45: OPEN
```

The H0 repair must control the literal synchronized physical fibre, not only the bare multiplicative representation count of `s X_- Z_-`. The HNE step additionally needs a bounded packet-shift incidence theorem.

## Cross-u

Analytic work has not yet been promoted because the route is depth-first through same-`u`. Banked algebra only:

```math
(q,u_i)=1,
\qquad
c=(u_1,u_2)\gg T,
\qquad
\ell_1\equiv\ell_2\pmod c,
\qquad
\ell_1-\ell_2=cj.
```

`J0`, `JNE`, and the source-weighted mixed Gram are not yet reached analytically.

## Parallel local residual

```text
TOPBAND-BROAD-MAJOR-TREE-MATCH45
```

remains independently open.

## Next attack

1. Recover the literal `lambda_i` model coordinates and prove or repair the weighted eighth moment.
2. Rebuild the literal positive same-`u` Plancherel diagonal from zero; do not reuse the old `L1` safe compiler.
3. Insert the proved AP-sampling multiplicity before global Cauchy/source compression.
4. If the diagonal closes, prove the H0 physical-fibre moment and HNE packet-shift incidence.
5. Only then return to cross-`u` analytic work.

## Publication firewall

```text
GATE1B: OPEN
```
