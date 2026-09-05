# ARISTOTLE GATE-1B V16 — RANK-ONE BÉZOUT REPROOF / REVERIFY

DO MATHEMATICS AND FORMAL REVERIFICATION.

This is an append-only, hostile reproof/reverify run for the Twin-Prime
Programme Gate 1B Draft 16.  It is NOT permission to assume the remaining
analytic theorem, Gate 1B, Full Type II, Ford–Maynard closure, or twin-prime
infinitude.

## 0. CONTROLLING STATUS

Treat the following as the intended research ledger to be checked, not as
axioms:

- PURE5-DP-DOUBLEGCD-BEZOUT-LINE45: OPEN.
- RANKONE-BEZOUT-AFFINE-ELLIOTT5D45: FIRST EXACT ANALYTIC OPEN.
- best banked primitive scale: `Q*V*(log X)^C0`.
- required scale: `Q*V*(log X)^(-A)`.
- no fixed-power deficit is claimed for this primitive residual.
- GATE1B: OPEN.
- FULL TYPE II: OPEN.
- TWIN PRIME INFINITUDE: NOT PROVED.

Never introduce an axiom whose proposition is one of these open conclusions.

## 1. FROZEN BANK — REVERIFY, DO NOT SILENTLY STRENGTHEN

Reprove or machine-check wherever possible:

1. `DP-LINE-ENTROPY-TRICHOTOMY45`.
2. `EQUAL-LARGE-FACTOR-OFFDIAG-ROUTER45`.
3. `FULLCROSS-LARGEPRIME-DIVISOR-MULT2-45`.
4. `FULLCROSS-DEFECT-GCD-ROUTER45`.
5. `FULLCROSS-DOUBLEGCD-BEZOUT45`.
6. `DP-FACTOR-INJECTIVE-BEZOUTLINE45`.
7. `DOUBLEGCD-LARGE-GS-TAIL45`.
8. `FULLCROSS-RIGIDITY-ONLY-CLOSURE45` as a DEATH CERTIFICATE:
   rigidity/multiplicity/injectivity alone leave the primitive natural `Q*V`
   scale and therefore do not imply arbitrary logarithmic cancellation.
9. `BETA-DP-TO-MU-LARGEPRIME45`.
10. `RANKONE-SHIFT-BIJECTION45`.
11. the exponent arithmetic in `WRIGHT-PARTFIX-MOYK5-45`.

If any item cannot be represented faithfully in the current Lean library,
print the exact missing imported analytic theorem or source definition.  Do
not replace it by `axiom`.

## 2. DOUBLE-GCD BÉZOUT GEOMETRY

Work in the clean entropy-gap cell.

Start with the fully-crossed off-diagonal equations and the two GCD
factorisations

    d1 = g*a,  d2 = g*b,  gcd(a,b)=1,
    v1 = s*w1, v2 = s*w2, gcd(w1,w2)=1.

Derive source-exactly that the remaining difference parameter is divisible by
`s`, and after writing `j=s*k` obtain

    g*ell*A - u*s*w1 = 2,
    A2 - A1 = u*s*k,
    w2 - w1 = g*ell*k.

For fixed `(g,s)` prove the line parametrisation

    A_t = A0 + u*s*t,
    w_t = w0 + g*ell*t,
    T_{g,s} ~ H/(g*s).

Machine-check the algebraic implications and the coprimality assumptions
actually used.

## 3. LARGE-PRIME MULTIPLICITY

Reprove the clean cell statement:

If `N << Q/g` and `p ~ P` is an admissible large prime divisor, then there are
at most two such `P`-scale prime divisors, since three would force
`N >= P^3 > Q` in the physical entropy-gap range.

Also verify the uniqueness subrange

    g >> Q/P^2  ->  at most one P-scale prime divisor.

Do not replace dyadic inequalities by asymptotic prose; print the exponent
margins.

## 4. FACTOR INJECTIVITY ON A BÉZOUT LINE

For fixed clean `(u,ell,g,s)` prove:

- the same large prime `p` cannot occur at two distinct line parameters `t`;
- the same Möbius cofactor `a` cannot occur at two distinct line parameters.

Print exactly where

    gcd(p,u*s)=1,
    gcd(a,u*s)=1,
    T_{g,s} < p,
    T_{g,s} < a

or the correct physical inequalities enter.

## 5. LARGE-gs TAIL

From the natural scale

    U*R*T_{g,s}^2 ~ Q*V/(g^2*s^2),

and the fixed-polylog source/edge multiplicity, verify that for

    L = (log X)^(A+C0+3)

the contribution from `g*s > L` is

    <<_A Q*V*(log X)^(-A).

Keep the primitive `g=s=1` child explicit.

## 6. SEMIPRIME COEFFICIENT -> LITERAL MÖBIUS

On the clean squarefree cell define

    L_DP(n) =
      sum_{p|n, p~P, n/p~D} log p.

Prove exactly

    beta_DP(n)
      = sum_{d*p=n, d~D, p~P} mu(d) log p
      = -mu(n) L_DP(n).

State the squarefree hypothesis and the identity
`mu(n/p) = -mu(n)`.

Do not drop `L_DP`; it is the actual large-prime selector.

## 7. PRIMITIVE RANK-ONE RESIDUAL

Choose

    ell*A0 - u*w0 = 2,
    gcd(u,ell)=1,

and set

    A_t = A0 + u*t,
    w_t = w0 + ell*t.

The exact research target is

    R_R1 =
      sum_{u~U, ell~R, gcd(u,ell)=1}
      sum_t sum_{k != 0, |t+k| << H}
        mu(A_t) mu(A_{t+k})
        L_DP(A_t) L_DP(A_{t+k})
        b5(w_t) conjugate(b5(w_{t+k}))
        W_{u,ell,t,k}.

Required:

    |R_R1| <<_A Q*V*(log X)^(-A).

Create a declaration/interface named, or equivalent to,

    RankOneBezoutAffineElliott5DBound

but leave it UNINHABITED unless a real analytic proof is produced.

Forbidden:

    axiom RankOneBezoutAffineElliott5DBound : ...
    theorem ... := by exact open_assumption
    theorem ... := by sorry

## 8. RANK-ONE SHIFT BIJECTION

Set

    r = u*k,
    s = ell*k.

From `gcd(u,ell)=1`, prove

    k = gcd(r,s),
    u = r/gcd(r,s),
    ell = s/gcd(r,s).

Hence verify injectivity of `(u,ell,k) -> (r,s)` on the clean positive sector.

Check the family-size ledger:

    # actual shifts ~ U*R*H = X,
    independent rectangle ~ Q*V = X*H,
    density = 1/H,
    H >= X^(5/18).

This is a finite/exponent certificate.  It does NOT prove a Chowla transfer.

## 9. CHOWLA / CORRELATION FIREWALL

Do not formalise any of the following as implications without an actual
theorem matching the source:

    averaged Chowla -> rank-one residual,
    logarithmic Chowla -> ordinary rank-one residual,
    short-AP variance -> vector-valued rank-one residual.

The relevant public statements are only scope references:

- MRT averaged Chowla: arXiv:1503.05121.
- Tao–Teräväinen log-correlation structure: arXiv:1708.02610.
- KMT short AP multiplicative functions: arXiv:1909.12280.
- Guo growing-shift logarithmic Chowla: arXiv:2608.23500.

Bank only:

    ALLSHIFT-CHOWLA-TO-RANKONE45:
      FALSE AS A DIRECT SPLICE

meaning the published theorem hypotheses/output do not literally supply the
physical rank-one weighted bound.

## 10. WRIGHT / KLOOSTERMAN DEATH CERTIFICATE

Reverify the arithmetic audit of Wright 2026, arXiv:2604.25177.

Use the deliberately generous split

    R_f = Y^rho,
    n   = Y^(8-rho),
    M   = Y^theta,
    A   = Y^(theta-1),

with physical prefactors/norms as in Draft 16.

Check that over the admissible region the best total exponent is at least

    Y^(27/2+o(1)) = X^(3/2+o(1)),

against physical target

    Y^9 = X,

leaving deficit

    Y^(9/2) = X^(1/2).

If the exact theorem statement changes the arithmetic, print the correction
instead of preserving this ledger mechanically.

Blomer–Pascadi arXiv:2607.24311 is a genuine external theorem, but do not
promote it to the rank-one moving-family result.

## 11. LOW PRETENTIOUS PROFILE

Draft 16 records an internal analytic pass for small-conductor/low-frequency
profiles using standard PNT/Siegel–Walfisz and smooth partial summation.

Do NOT mark this as a Lean kernel theorem unless the required analytic library
is actually imported.

Instead:

- formalise the algebraic factorisation of the defect and beta transforms;
- state the exact external analytic theorem needed for each bound;
- prove the deterministic implication from those external bounds to
  `LOW-PRETENTIOUS-PROFILE45`.

The remaining uninhabited analytic interface is a high-profile inverse
statement, informally:

    large rank-one correlation
      -> common low profile
         OR quantitatively controlled high-profile packet.

Since the low branch is routed, the open work is the high branch.  Do not
invent an `InverseLargeSieve` axiom.

## 12. ANTI-CIRCULARITY

Explicitly verify:

1. no Möbius sign is used twice;
2. five centred defects are not replaced by a positive L2 energy before the
   claimed step;
3. the large-prime selector is not discarded;
4. rank-one shifts are not enlarged to an independent rectangle for free;
5. no logarithmic average is silently converted into an ordinary average;
6. no polylog shift theorem is applied to power-sized shifts;
7. no fixed-modulus Kloosterman theorem is relabelled as a moving-family
   inverse theorem;
8. no representation transform that returns QK5 is called progress;
9. comparison/main-term matching remains OPEN;
10. lower-defect faces are not inferred from the `|J|=5` case;
11. Gate 1B is not marked closed;
12. Full Type II is not marked closed;
13. twin-prime infinitude is not asserted.

## 13. REQUIRED OUTPUT

Return:

A. Lean/reproof file(s) for the finite/algebraic certificates actually proved.
B. A theorem-status ledger with exactly:
   - KERNEL PROVED,
   - EXTERNAL ANALYTIC INPUT,
   - SOURCE OPEN,
   - OPEN / UNINHABITED,
   - DEATH CERTIFICATE.
C. The first line that remains genuinely analytic.
D. Any correction to Draft 16 if the machine proof finds one.

The final status must remain one of:

    GATE1B OPEN — FIRST EXACT RESIDUAL:
    RANKONE-BEZOUT-AFFINE-ELLIOTT5D45

or, only after a real proof and all downstream source obligations:

    GATE1B CLOSED.

Do not output a twin-prime theorem from this run.
