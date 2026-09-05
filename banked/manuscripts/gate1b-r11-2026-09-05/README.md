# Gate 1B / R11 audited progress manuscript (5 September 2026)

This directory contains the status-controlled journal manuscript for the current Twin Gate 1B / `R11` research frontier. It is a rigorous progress paper, not a claim of `R11`, Global Gate 1B, `HSTAR`, or twin-prime closure.

## Authoritative frontier

| Node or architecture | Status |
|---|---|
| Former Sector A | **CLOSED** at arbitrary fixed logarithmic precision, conditional on the frozen source/compiler bank |
| Former three-sector FSHC formulation | **SUPERSEDED** by one exact high-pass residual |
| Physical delta + single-Poisson Hilbert-HMRD caller | **RETIRED / NONCLOSING** |
| Abstract finite Hilbert-HMRD theorem | **VALID; LEAN-CHECKED** |
| Current physical residual | `R_hi` |
| `R11` | **OPEN** |
| Global Gate 1B | **OPEN** |
| `HSTAR` | **OPEN** |
| Twin-prime conjecture | **OPEN** |

## Main audited advance

For squarefree rough moduli `q ~ R`, with `omega(q) <= j`, least prime factor at least `P`, and one common `1`-bounded sequence supported on `(D,2D]`, the paper proves

```text
sum_q sum_a^* |E_q(a;y)|^2  <<_j  D R + D^2/P.
```

The proof descends imprimitive characters with the coprimality correction intact and applies the primitive multiplicative large sieve. Its physical transference closes the former balanced-low Sector A and every fixed-polylogarithmic frequency band in the enlarged range `K >= R/sqrt(P_*)`, subject to the inherited source/compiler interfaces.

The independent audit requires three corrections, all incorporated in the manuscript:

1. principal coprimality removal costs `O_j(2^j(D/P+1))`, not the literal coefficient `j(D/P+1)`;
2. odd-Mobius dyadic recursion costs one additional `log D`, giving the conservative ledger `L^(114+3b/2)`;
3. the legal cellwise frequency cutoff uses the minimum cyclic conductor over the cell.

The exact first-moment reassembly is

```text
R11(X) = R_hi(X) + O_S(X L^(-S)),
```

where `R_hi` retains the literal Mobius coordinate, five-prime modulus, labelled six-prime target, and all unremoved high frequencies. The required bound for `R_hi` is not proved.

## Evidence hierarchy

1. latest Aristotle/Lean status and kernel bank;
2. newest independent Opus hostile audit;
3. newest rough-conductor analytic research report;
4. frozen upstream source/local-sector bank, used only where stated.

Where these layers differ, the manuscript follows the newest independently audited status and records the discrepancy explicitly.

## Files

- `twin_gate1b_r11_audited_20260905.tex`: complete journal-style manuscript source.
- `twin_gate1b_r11_audited_20260905.bib`: bibliography.
- `CLAIMS_LEDGER.md`: theorem/evidence/open-claim index.
- `BUILD_AND_QA.md`: compilation and visual-QA record.

## Build

A TeX distribution with `latexmk`, `biber`, `newtx`, `biblatex`, `cleveref`, and the AMS packages is required.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error twin_gate1b_r11_audited_20260905.tex
```

The checked build produces 32 A4 pages with no unresolved citations or cross-references and no overfull boxes.