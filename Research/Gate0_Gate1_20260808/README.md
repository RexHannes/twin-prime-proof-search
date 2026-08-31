# Gate 0–1 Research Checkpoint — 2026-08-08

> **Status: exploratory research checkpoint, not a proof of Full Type II, FCPT, the Twin Prime Conjecture, Hardy–Littlewood, or parity breaking.**

This directory records the current Gate 0 / Gate 1 frontier developed in the GPT-Sol / Fable / Opus / Aristotle proof-search workflow. It is deliberately conservative: finite algebra, exact identities, source fields, analytic estimates, failed routes, and conditional literature interfaces are separated.

## Current global status

- **Gate 0:** not authoritatively closed. The generic reconstructed root packet is well specified, but the exhaustive source packet census / weighted edge-family definition remains incomplete.
- **Gate 1:** not closed. A substantial set of degenerate and resonant sectors is closed or algebraically reduced, but the generic globally coupled source estimate remains open.
- **Gate 2 / Gate 3:** no global bypass is claimed while Gate 1 is open.
- **Gate 4:** many lower-dimensional strata are closed; the generic nonresonant sector remains open.

## Parameterization

Use

\[
M=X^{1/3},\qquad R=X^a,\qquad L=X^b,
\]

\[
H=X^{a+2b-2/3},\qquad D=X^{2/3-a},\qquad K=X^{1/3-a}.
\]

Exact relations:

\[
DH=L^2,\qquad RK=M,\qquad MK=D.
\]

The clean polytope under current discussion is

\[
a\ge 5/18,\qquad b\ge 1/3,\qquad a+b\le 5/8.
\]

At

\[
V_2=(5/18,25/72),
\]

we have

\[
M=X^{24/72},\ R=X^{20/72},\ L=X^{25/72},\ H=X^{22/72},\ D=X^{28/72},\ K=X^{4/72}.
\]

The source target is

\[
\boxed{\mathcal T=ML^4/H=MDL^2=X^{102/72}.}
\]

The original generic trivial/source scale is

\[
M^2D^2=X^{104/72},
\]

so the **true intrinsic V2 deficit** is

\[
\boxed{M/H=X^{1/36}.}
\]

This must not be confused with the larger artificial losses created by some over-Cauchied reformulations.

## Generic affine/root packet

Rows are

\[
e=(r,m,k),\qquad m'=m+kr.
\]

The reconstructed canonical residue satisfies

\[
mw_0\equiv -2\pmod r,\qquad 0\le w_0<r.
\]

Define

\[
r\alpha=mw_0+2,\qquad \beta=\alpha+kw_0.
\]

Then

\[
\boxed{m'\alpha-m\beta=2k.}
\]

CRT roots are

\[
t_p(e)\equiv-\alpha\bar m\pmod p,
\qquad
t_q(e)\equiv-\beta\overline{m'}\pmod q.
\]

The exact ROOT-COLLAPSE identity is banked at the mathematical level in the current research record. Cleanness of `m,m'` is not used in that algebraic identity; source routing for non-clean packets is nevertheless a separate Gate-0 question.

## Current source coefficient class

The source prime coefficients are rank one:

\[
x_{p,q}=b_pd_q,\qquad |b_p|,|d_q|\le 1.
\]

After pairing:

\[
b_{p_1}\overline{b_{p_2}}d_{q_1}\overline{d_{q_2}}.
\]

Do not enlarge this to arbitrary `(p,q)` matrices without a proved harmlessness argument.

## Important current corrections

1. **True V2 deficit:** `X^(1/36)`.
2. **Fixed-block Fourier + pairwise cross-p Cauchy loss:** `X^(1/3)` — this is route-induced, not intrinsic.
3. **PPD / MRD / CRF:** at most stronger sufficient routes; they are not the exact source frontier.
4. **MIX2:** the multiplicative-convolution identity is useful algebra, but MIX2 alone does not imply the global Gate-1 target.
5. **Pascadi-style short-support dictionary:** remains conditional on source-specific coefficient/support structure; do not claim a direct theorem match from phase resemblance alone.

## Files in this checkpoint

- `GATE0_SOURCE_CENSUS.md` — exact Gate-0 routing ledger and missing source fields.
- `GATE1_V2_FRONTIER.md` — current Gate-1 mathematics, closed sectors, repaired lemmas, failed routes, and exact analytic frontier.
- `NEXT_PROOF_PROGRAM.md` — shortest honest proof program from this checkpoint.

## Explicit nonclaims

Nothing in this directory proves or implies:

- Full Type II;
- Ford–Maynard positivity / FCPT;
- parity breaking;
- the Twin Prime Conjecture;
- Hardy–Littlewood;
- a complete high-`P3` assembly.

Any later file that conflicts with this checkpoint must state the new proof and explicitly supersede the relevant ledger entry.