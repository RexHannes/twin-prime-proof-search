# Erdős #461A Max-Jump D3S Checkpoint

## Scope

This checkpoint banks finite arithmetic and graph combinatorics and isolates one
analytic input, `OPEN_ANALYTIC_INPUT_threeFormUpperSieve`. It does **not** prove
a uniform super–Erdős–Graham theorem or Erdős #461A.

## Banked core

- Finite excess identity and asymmetric true-excess spacing.
- Equal-label absolute spacing from the established signed spacing premise.
- Side-factor identities, gcd-two identity, divisibility-by-four dichotomy, and
  max side at least four.
- Three-form equation, parity (with odd rough complementary factors), divisibility
  obstruction at 3, linear-solution parametrisation, and local root tables.
- Strict-rank directed acyclicity and the finite orphan path-cover inequality.

## Conditional branch

`conditionalDoublySmallTokens` and `conditionalOrphanSea` visibly accept an
explicit `OPEN_ANALYTIC_INPUT_threeFormUpperSieve`. The structure has no global
inhabitant; its accessor only projects a supplied proof.

The intended analytic statement is the dimension-three upper-sieve bound with
the repaired envelope

`H = 2 + ceil(t / (2*a*b*u))`.

Unconditional D3S is not Lean-certified until that input is discharged.

## Important interpretation

The orphan quantity counts token-centre occurrences/positions. It does not count
distinct labels and is not a super-EG conclusion.

## Out of scope

Hall matching/capacity, BRFC, CHSA, BORF, singleton capacity two,
maximal-layer discharge, conversion to distinct labels, uniform super-EG, and
Erdős #461A.

## Audit limitation

This repository update is a **partial bank**, not the requested completed
conditional D3S tree.  The large-u estimate, singular-factor averages, repaired
dyadic summation, exact token definitions, boundary count, undirected-forest
argument, and quantitative path-length bound have not been formalized.  The
`assemble` argument of `conditionalDoublySmallTokens` exposes these missing
steps as an explicit premise; it must not be described as following from the
three-form sieve input alone.  Thus the current project does not yet satisfy the
“exactly one open analytic input and no other open theorem” target.
