# Next Proof Program — Gate 0 / Gate 1

This file gives the shortest honest continuation from the 2026-08-08 checkpoint.

## Priority 1 — Aristotle finite bank

Formalize / independently reprove the finite core before another expensive analytic run:

1. V2 exponent ledger and the distinction
   - intrinsic source deficit `1/36`;
   - pairwise-Fourier/Cauchy route loss `1/3`.
2. AFF and root congruence package.
3. DCRT residue identities.
4. corrected row-frequency injectivity via modulus divisibility + size + gcd.
5. input-frequency injectivity with `gcd(2,c)` tracked.
6. cyclic Parseval / restricted Parseval / weighted restriction.
7. fixed-(p,m') Fourier contraction.
8. p-diagonal finite consequence.
9. p-resonance interval-counting consequence.
10. large-prime divisor uniqueness / branching lemmas.
11. root-collision energy as a coincidence-count theorem only.
12. preserve existing Route-B Mobius-root repair; do not infer analytic closure.

No analytic theorem should be inhabited merely to encode a desired estimate.

---

# Priority 2 — Gate 0 source archaeology

Use the full repository/archive to construct `ConcreteCleanP3EdgeFamily` from source, not from exponent inference.

For each packet class extract:

```text
row parameterization
prime coefficient tensor
row weight
multiplicity
prefactor
gcd / dyadic restrictions
centering convention
operator after exact algebra
```

Required packet classes:

```text
direct
switched
balanced
grouped 3+6
j=1
j=2
endpoint
one-small-rho
non-unit/gcd
non-clean m'
boundary m'
all residual high-P3 packets
```

Every row must end in exactly one verdict:

```text
ROUTES_TO_ROOT
CLOSED_EXCEPTION
GENUINELY_NEW_OPERATOR
```

### Gate-0 closure criterion

Gate 0 closes only if

\[
\mathfrak R_{\rm new}=\varnothing
\]

and multiplicity / main-projection / weight provenance are globally consistent.

### Load-bearing output

The most important Gate-0 field for Gate 1 is the actual row-weight class:

```text
COMMON_SMOOTH
FINITE_TEMPLATE
STRUCTURED_EDGE_DEPENDENT
ARBITRARY_BOUNDED_EDGE_DEPENDENT
```

Do not choose the Gate-1 harmonic tool before this field is known.

---

# Priority 3A — if weights are common smooth / finitely templated

Attempt source-specific harmonic compression, not generic arbitrary-weight compression.

Goal: prove a decomposition into a bounded / `X^{o(1)}` number of scalar Kloosterman-admissible blocks with complete coefficient norm ledger.

For every proposed block prove:

1. exact source equality or controlled error;
2. interval/support size;
3. coefficient `l2` norms;
4. modulus dependence;
5. fixed multiplier/unit condition;
6. total decomposition multiplicity;
7. global reassembly cost.

Only after these are proved may Pascadi / Bettin-Chandee / related scalar bilinear Kloosterman theorems be invoked.

### Kill rule

If tensorization/support decomposition incurs a positive power loss exceeding the available theorem margin, abandon that dictionary immediately.

At V2 a previously explored hypothetical `(L^2,M)` dictionary had only a small positive power-loss budget. At endpoint vertices there may be essentially only `X^{o(1)}` room. Therefore no hidden dimension factor is acceptable.

---

# Priority 3B — if weights are genuinely arbitrary edge-dependent

Do **not** pursue a uniform short-Fourier-support theorem: arbitrary bounded sparse edge weights need not have short Fourier support.

Instead preserve the original source graph and signs.

Primary target:

\[
\sup_{|b|,|d|\le1}
\sum_e\omega_e
\left|\sum_{p,q}b_pd_qA_{e,p,q}\right|^2
\ll
ML^4/H\,X^{o(1)}.
\]

Recommended direction:

1. subtract only already-closed sectors (p-diagonal, p-resonance, determinant degeneracies, exact swap);
2. retain the global p-sum — no pairwise p-Cauchy;
3. retain the full-c character / Gauss signs if using the character decomposition;
4. exploit edge injectivity and directional cancellation in a signed modulus-averaged reassembly;
5. use a literature theorem only after proving its exact source dictionary.

---

# Priority 4 — full-c character reassembly

The archive contains local ingredients:

\[
\sum_\chi |C_{m,\chi}|^2\ll\varphi(c)M X^{o(1)}
\]

and a directional bound of the schematic form

\[
|D_{q_1,q_2,m,\chi}|\ll L^2\sqrt M/H\,X^{o(1)}.
\]

Historic failure: taking absolute values / blockwise Cauchy destroys the gain.

Therefore any new character route must preserve at least one of:

```text
Gauss-sum sign
character orthogonality across the actual source decomposition
modulus average
rank-one prime coefficient signs
row-weight structure
```

`MIX2 = sum |C|^2 |D|^2` may be used as a collision census but is **not** by itself the global closure target.

---

# Priority 5 — hostile audit protocol

Only after a new Gate-1 proof candidate exists, send it to Fable / independent Opus for hostile audit.

Mandatory audit questions:

1. Was the source coefficient class enlarged?
2. Was a row weight treated as arbitrary or smooth without source proof?
3. Was a cancellation average used twice?
4. Was a dimension / modulus / packet multiplicity hidden in `X^{o(1)}`?
5. Was an incomplete interval silently completed?
6. Was a scalar literature theorem applied to a correlated or vector-valued source?
7. Does the proof close V2 at the true source target, or only an over-strong reformulation?
8. Does the mechanism extend across the polytope, including the endpoint?

---

# Current decision tree

```text
Finish finite Lean bank
        |
        v
Authoritative Gate-0 census
        |
        +--> new operator found --> carry it explicitly into Gate 1
        |
        +--> no new operator
                |
                v
          determine weight class
                |
         +------+------+
         |             |
 common/template   arbitrary edge-dependent
         |             |
 harmonic          source-preserving signed
 dictionary        graph/modulus dispersion
         |             |
         +------v------+
                |
          candidate Gate-1 proof
                |
          hostile Fable audit
                |
          if survives: extend V2
          mechanism across polytope
```

## Nonclaims

This program is a research plan, not evidence that the remaining theorem is true or that the Twin Prime Conjecture follows.