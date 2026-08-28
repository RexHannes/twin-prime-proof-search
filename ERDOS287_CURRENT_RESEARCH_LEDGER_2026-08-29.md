# Erdős #287 — Current Research Ledger (2026-08-29)

This is an **append-only research-status note**. It does not replace or weaken any historical Lean bank, and it does not assert a Lean proof of Erdős #287 or of `BALANCED7`.

The repository's existing master `RequestProject/CurrentProgramme/CurrentStatus.lean` predates the latest Balanced7 comparison/full-q audit. The more recent Gate-1B append-only layers (`CurrentStatusCharacterBundle.lean`, `CurrentStatusHighKShift.lean`, `CurrentStatusShiftedMAMOperator.lean`, and their audits) are already present on `main`. This file records the current #287 research frontier until a subsequent Aristotle run creates a kernel-checked status layer/conditional compiler.

## Controlling verdict

```text
ERDOS287: OPEN.
FCL: OPEN.
BALANCED7: OPEN — NARROW REPAIR / AUDIT PENDING.
```

The latest Pro closure candidate was **not** accepted as a full Balanced7 closure after hostile audit. However, the audit preserves substantial gains and reduces the remaining work to a small set of explicit obligations.

## Surviving / bankable gains

### `BALANCED7-EULER-UNIFORMITY45`

**Research PASS.** The full-q principal Euler identity survives audit. The factorisation

```math
F_P(w)=H_P(w)/\zeta(1+w)
```

has off-`P` local factor

```math
1-\frac{p^{-w}}{p(p-1)(1-p^{-1-w})}=1+O(p^{-7/4})
```

on `Re(w) >= -1/4`, with `H_P(w)=O(1)` uniformly over the physical seven-prime family and

```math
H_P(0)=2B(P).
```

This is a **full-q** identity and may only be invoked after exact reassembly of all q-regions.

### Physical `mu*log` normalisation

**PASS / repair banked.** The source-minimal identity is

```math
\Lambda(2P+s)=\sum_{qr=2P+s}\mu(q)\log r.
```

The historical `C_ext=0` ledger is incomplete and must be retained only as **RETRACTED / SUPERSEDED**. The safe current hard-cell ledger is

```text
C_ext = 1.
```

With the previously banked variance budget `C_var=5`, the local hard-cell log margin survives:

```text
C_var - 2*C_ext = 3 > 0.
```

### Full-q structural partition

**PASS.** With `U=X^(1/3)` and `qr=2P+s`, the exact sectors are

```text
SmallQ: q <= U;
SmallR: q > U and r <= U;
Hard:   q > U and r > U.
```

The sectors are exhaustive and disjoint at the sharp level; hard q is then handled by a smooth dyadic partition of unity.

## Small-q current status

The historical target

```text
AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45
```

is **SUPERSEDED AS CONTROLLING / WRONG PROVIDER**, not false. Generic Gate-0 Type-I is a source mismatch because q divides the affine form `2P+s`, not the index `P`.

The replacement 3+4 multiplicative-large-sieve route has **capacity/exponent arithmetic PASS**, but the hostile audit could not verify the literal generated-coefficient normalisation. The current first exact residual is therefore:

```text
AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45:
    SOURCE / COEFFICIENT-NORM OPEN.
```

Required discharge:

1. pin the literal SP-2 prime-box weights;
2. derive the 3-prime product coefficient L2 norm including labelled-product multiplicity and repeated primes;
3. derive the 4-prime product coefficient L2 norm likewise;
4. print the imprimitive-to-primitive conductor/multiplicity cost;
5. re-run the 3+4 large-sieve bound with every Mellin/log cost explicit.

The large-sieve exponent arithmetic itself did not fail.

## Small-r current status

The direct source estimate is a **research closure candidate**, but the previous full-q owner table was not exact enough.

The correct object must be written as

```math
D_{sr}=S_{sr}-M_{sr}^{prin},
```

with `M_sr^prin` counted exactly once in the full Euler principal identity. Bounding `S_sr` and `M_sr^prin` separately is acceptable, but the final reassembly must subtract the principal packet explicitly before invoking the full-q Euler identity.

Current node:

```text
AFFINE287-SP2-SMALLR-OWNER-SUBTRACTION45:
    LOCAL REASSEMBLY REPAIR.
```

No new deep analytic theorem is currently identified here.

## Hard dyadic current status

The hard mechanism is **not dead**. The hostile audit found a uniformity correction.

The pointwise conditions include

```text
Q > X^(2/7),
Q < X^(5/7),
```

but the short-t sieve uses `z=T^(1/20)` and the saving is `1/log z`, not literally `1/log X` uniformly as `theta -> 5/7`.

For the physical hard range

```math
1/3 < theta < 2/3,
```

we have the fixed margin

```math
5/7-2/3=1/21,
```

so `log z >= (1/420) log X` and the desired logarithmic sieve saving survives with an absolute constant.

The safe formulation is therefore a **delta-uniform physical-range theorem**, e.g.

```text
HARD-THETA-PHYSICAL-DELTA45:
    PASS CANDIDATE with delta=1/21.
```

Do not state the old open interval `(2/7,5/7)` as a uniform theorem with constants independent of distance to the right endpoint.

Shiu's affine-divisor estimate remains a research PASS candidate on the physical range, subject to the literal theorem statement/source pin.

## No-double-spending / full-q reassembly

**OPEN pending one local repair.** The small-r principal packet must not be both discarded inside the direct small-r estimate and simultaneously counted inside `2B(P)` without explicit subtraction.

Required exact owner convention:

```text
SmallQ principal      -> full Euler owner
SmallQ defect         -> 3+4 large-sieve owner
SmallR principal      -> full Euler owner (or explicitly removed before Euler reassembly)
SmallR defect         -> direct small-r owner
Hard principal        -> full Euler owner
Hard defect           -> hard raw-minus-principal owner
Even/nonunit sectors  -> zero/routed
```

Only after this table is implemented algebraically may `ALL-Q-NO-DOUBLE-SPENDING45` be promoted.

## Current Balanced7 chain

```text
X = AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45
    |
    | only if PASS
    v
Y = AFFINE287-SP2-SMALLR-OWNER-SUBTRACTION45
    |
    | only if PASS
    v
Z = HARD-THETA-PHYSICAL-DELTA45
    |
    | only if PASS
    v
W = ALL-Q-EXACT-REASSEMBLY45
    |
    | only if PASS
    v
SP2-BALANCED7-FULL-Q45 / BALANCED7
    may be promoted at research/paper level only after a fresh hostile audit.
```

Thus the **first exact residual** is currently:

```text
AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45.
```

## Effectivity firewall

Separate from the asymptotic Balanced7 repair:

```text
287-EFFECTIVE-POLYLOG-MODULUS-REPLACEMENT45: OPEN.
```

Classical Siegel-Walfisz in the polylogarithmic modulus region is generally ineffective. Therefore even an eventual asymptotic Balanced7 closure does **not** automatically provide:

- a computable large-X threshold;
- an effective FCL threshold;
- explicit `M0`;
- a seamless finite-range-to-asymptotic bridge;
- a computable `WindowPairSupply` threshold.

## Downstream fixed-k / fragmentation status

The earlier claim that the same analytic geometry should work for each fixed `k>=7` remains only a **downstream research candidate** until Balanced7 is repaired and re-audited. It must not be used to activate the uniform-k census.

If and only if Balanced7 later closes, the proposed next research node is:

```text
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45.
```

That node must control the actual k-range, coefficient `(-1)^r C(k-1,r)`, fragmentation multiplicity, repeated/squareful strata, model-containing cells, `J != empty` routing, and a unique source-owner map.

## Research vs Lean status

Nothing in this note inhabits an analytic interface. No row here should be interpreted as `LEAN_PROVED` unless an existing kernel theorem is cited explicitly.

The next Aristotle run should create an append-only #287 status layer and conditional reassembly compiler, preserving all historical statuses and keeping `ERDOS287: OPEN`.
