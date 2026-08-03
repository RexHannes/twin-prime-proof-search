# Lean proof-search notebook for prime-pair and parity questions

> **Status: exploratory formalization — not a proof of the Twin Prime Conjecture, Hardy–Littlewood, or a parity-breaking theorem.**

This repository preserves an attempted Lean-assisted proof search.  It is published as a research record: some finite algebraic, combinatorial, and bookkeeping statements are formalized, while the analytic estimates and final number-theoretic implications needed for the headline conjectures remain open.

## What this is

The project explores several related directions, including:

- a Lean “bank” of finite arithmetic, lattice, and Kloosterman-style identities;
- status/dependency ledgers for proposed prime-pair and parity-breaking routes;
- finite models for reciprocal subset-sum collisions and their energy spectrum; and
- a formal counterexample family showing that one naive bounded-support strategy for smooth reciprocal identities fails.

The archive records edits by [Aristotle (Harmonic)](https://aristotle.harmonic.fun).  See `ARISTOTLE_SUMMARY.md` for the run-by-run provenance supplied with the archive.

## What is and is not established

| Topic | Honest status |
| --- | --- |
| Selected finite / algebraic statements | Formalized in Lean; inspect the corresponding theorem and its dependencies before relying on it. |
| Proposed analytic estimates | Open inputs, conditional interfaces, provisional reductions, or literature context — not Lean proofs of those estimates. |
| Twin Prime Conjecture / twin-prime lower bound | **Not proved.** |
| Hardy–Littlewood conjectures | **Not proved.** |
| General parity-breaking theorem | **Not proved.** |
| Full high-`P3` / final sieve assembly | **Not proved.** |

The repository’s own authoritative ledgers make these nonclaims explicit:

- `HIGH_P3_AUDIT.md`, especially the “Explicit nonclaims” section;
- `LEDGER.md`, whose global nonclaims include no twin primes, no Hardy–Littlewood, and no parity breaking;
- `NANC/BankStatus.md`, which lists the twin-prime lower bound and Hardy–Littlewood as open.

## Proof-hole policy

There are currently six Lean `sorry` placeholders:

- two in `RequestProject/Support4.lean`;
- two in `RequestProject/EnergyDominanceY3.lean`; and
- two in `RequestProject/DominantShortEnergy.lean`.

They mark unproved classification/conjectural statements.  A successful Lean build therefore does **not** turn this repository into a complete proof of any headline conjecture.  Treat the status ledger and each theorem’s assumptions as part of the result.

## Notable bounded claims recorded in the project

The supplied project documentation describes formalized finite results such as:

- finite-depth Möbius-convolution algebra;
- selected finite-field/Kloosterman, linear-algebra, and exponent-arithmetic components;
- an exact reciprocal subset-sum collision/energy decomposition; and
- an infinite family of primitive reciprocal identities with unbounded support among `{2,3}`-smooth composite denominators.

These are components and diagnostics for proof search.  They do not supply the missing analytic estimates, source transcriptions, or final deductions required by the Twin Prime Conjecture or Hardy–Littlewood.

## Building

The project specifies Lean `v4.28.0` and Mathlib `v4.28.0` in `lean-toolchain` and `lakefile.toml`.

```bash
lake build
```

Historical reports bundled in `ARISTOTLE_SUMMARY.md` and `HIGH_P3_AUDIT.md` report successful builds for earlier snapshots.  This publication should be independently rebuilt and audited before any mathematical reliance.

## Repository map

- `RequestProject/` — main Lean sources and formal status ledger.
- `NANC/` — finite parity/sieve-related models and a concise bank status.
- `LEDGER.md` — detailed claim-by-claim status and dependencies.
- `HIGH_P3_AUDIT.md` — audit record, frontier, and explicit nonclaims.
- `ARISTOTLE_SUMMARY.md` — chronological supplied run summaries; later entries supersede earlier ones where they conflict.

## How to read or contribute

Please do not describe this repository as a solution, proof, or breakthrough on twin primes, parity breaking, or Hardy–Littlewood.  Useful contributions would include:

1. reproducing the Lean build with the pinned toolchain;
2. auditing individual theorem statements and their axiom closure;
3. replacing `sorry` placeholders with genuine proofs, where possible;
4. formalizing exact, citable hypotheses for the open analytic inputs; and
5. keeping the ledgers current whenever a status changes.

The goal of this public record is falsifiability and clear separation between verified components, conditional architecture, evidence, and open work.
