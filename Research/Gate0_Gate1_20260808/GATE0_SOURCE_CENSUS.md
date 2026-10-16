# Gate 0 — Authoritative Source Census Ledger

> **Verdict: OPEN SOURCE CENSUS.** The generic root template is reconstructed and algebraically coherent; exhaustive source routing is not yet certified.

## Goal

Construct an authoritative source object

```text
ConcreteCleanP3EdgeFamily
```

that specifies, for every surviving high-`P3` packet:

1. exact admissible row parameters `(r,m,k)`;
2. `m' = m + k r` support and dyadic ranges;
3. clean/non-clean factorization data;
4. exact source coefficient tensor;
5. decomposition multiplicity;
6. exact prefactor / normalization;
7. row weight and whether it is common, finitely templated, or genuinely edge-dependent;
8. canonical `w0, alpha, beta`;
9. gcd and box-disjointness conditions;
10. whether the packet routes to the generic root operator, is a closed exception, or creates a genuinely new analytic operator.

The closure target is a disjoint partition

\[
\boxed{\mathfrak R_{\rm all}=\mathfrak R_{\rm root}\sqcup\mathfrak R_{\rm closed}}
\]

with

\[
\mathfrak R_{\rm new}=\varnothing.
\]

If a nonempty `R_new` is found, Gate 0 is not closed and that operator must be carried into Gate 1 explicitly.

---

## Reconstructed generic root template

### Row data

\[
e=(r,m,k),\qquad m'=m+kr.
\]

Canonical orbit residue:

\[
mw_0\equiv-2\pmod r,\qquad 0\le w_0<r.
\]

Affine variables:

\[
r\alpha=mw_0+2,
\qquad
\beta=\alpha+kw_0,
\]

hence

\[
r\beta=m'w_0+2,
\]

and

\[
\boxed{m'\alpha-m\beta=2k.}
\]

### Root data

\[
t_p(e)\equiv-\alpha\bar m\pmod p,
\]

\[
t_q(e)\equiv-\beta\overline{m'}\pmod q.
\]

The finite ROOT-COLLAPSE / physical-incidence identities depend on this affine structure and gcd hypotheses; they do not intrinsically require clean `P3` factorization.

### Source coefficient class

Preserve

\[
b_pd_q,
\]

and after squaring

\[
b_{p_1}\overline{b_{p_2}}d_{q_1}\overline{d_{q_2}}.
\]

No arbitrary matrix enlargement is banked.

---

# Packet ledger

## 1. Direct-dispersion / generic clean packet

**Known:** displayed graph/root phase, affine row variables, rank-one prime coefficients.

**Finite routing:** ROOT.

**Status:**

```text
ROUTED_FROM_RECONSTRUCTED_SOURCE
```

**Still required for authoritative Gate 0:** exact multiplicity and weight normalization from the original decomposition.

---

## 2. Switched packets

**Known:** switching exists at identity level in the research archive.

**First missing source field:** exact switched-packet coefficient tensor.

Load-bearing question:

\[
\text{does the switched packet preserve }b_pd_q\text{ up to }X^{o(1)}\text{ separated factors?}
\]

**Status:**

```text
FINITE_SOURCE_FIELD
NEW_OPERATOR_POSSIBLE UNTIL TENSOR IS EXTRACTED
```

---

## 3. Balanced packets

**Known:** balanced affine identities are compatible with the generic root algebra.

**First missing source field:** exact weight type:

```text
COMMON_SMOOTH
FINITE_TEMPLATE
EDGE_DEPENDENT
```

This is analytically load-bearing: a common/finitely templated weight may support further harmonic compression; a genuinely arbitrary edge-dependent weight may not.

**Status:**

```text
FINITE_SOURCE_FIELD — WEIGHT CLASS
```

---

## 4. Grouped `(3+6)` packets

**First missing source field:** exact packet multiplicity / grouping integer and resulting prefactor.

Need to prove that grouping does not create a coefficient matrix beyond the original rank-one source class.

**Status:**

```text
OPEN_INPUT_EXACT_FIELD
```

---

## 5. `j=1` packets

**First missing source field:** exact prefactor and weight inherited from the decomposition.

**Status:**

```text
FINITE_SOURCE_FIELD
```

---

## 6. `j=2` packets

**First missing source field:** exact prefactor and weight inherited from the decomposition.

**Status:**

```text
FINITE_SOURCE_FIELD
```

---

## 7. Endpoint packets

**First missing source field:** boundary smooth/dyadic weight convention and multiplicity at partition edges.

Expected possibilities:

- closed boundary error;
- routed root packet with bounded multiplicity;
- a separate endpoint operator.

Do not assume which before source extraction.

**Status:**

```text
FINITE_SOURCE_FIELD
```

---

## 8. One-small-`rho` packets

**Known:** local exceptional-row identities exist in the research bank.

**First missing source field:** exact small-factor threshold and source coefficient after this split.

**Status:**

```text
FINITE_SOURCE_FIELD
```

---

## 9. Non-unit / gcd sectors

Existing hostile audits report a power-saving density loss for shared small factors and treat these as closed exceptions under bounded weights.

**Status:**

```text
CLOSED_EXCEPTION — subject to final source multiplicity tally
```

Do not use this line to infer anything about generic all-coprime rows.

---

## 10. `m'` outside nominal dyadic window

Finite affine/root identities still make sense, but the original dyadic partition determines whether these rows are absent, boundary errors, or routed through another packet.

**First missing source field:** boundary convention.

**Status:**

```text
FINITE_SOURCE_FIELD
```

---

## 11. Non-clean `m'`

ROOT-COLLAPSE, affine identities, and the basic incidence picture do not use clean-`P3` factorization.

However, source coefficient / multiplicity / packet provenance must still be checked.

**Status:**

```text
FINITE ROOT ALGEBRA ROUTED
SOURCE ROUTING OPEN
```

---

## 12. Exhaustive weighted clean-edge family

This is the decisive Gate-0 object.

Need an authoritative proof that every surviving hostile high-`P3` packet is represented exactly once (up to an explicitly bounded multiplicity) by the declared family, with the declared coefficient and weight.

**Status:**

```text
OPEN — ConcreteCleanP3EdgeFamily NOT YET AUTHORITATIVE
```

---

# Required extraction table

For each packet, fill the following columns from the actual source/repository rather than exponent inference:

| Packet | Row parameterization | Prime coefficient | Row weight | Multiplicity | Prefactor | gcd/support | Operator | Verdict |
|---|---|---|---|---:|---|---|---|---|
| direct | `(r,m,k)` | pending authoritative transcription | pending | pending | pending | generic | root | provisional route |
| switched | pending | **missing** | pending | pending | pending | pending | unknown/root? | source field |
| balanced | compatible affine rows | likely source rank-one, verify | **missing weight class** | pending | pending | pending | root if legal | source field |
| 3+6 | pending | pending | pending | **missing** | **missing** | pending | unknown/root? | source field |
| j=1 | pending | pending | pending | pending | **missing** | pending | unknown/root? | source field |
| j=2 | pending | pending | pending | pending | **missing** | pending | unknown/root? | source field |
| endpoint | pending | pending | **boundary convention** | pending | pending | pending | unknown | source field |
| small-rho | pending | pending | pending | pending | threshold missing | pending | unknown | source field |
| gcd | exceptional | bounded | bounded | bounded | — | shared factor | closed | provisional closed |
| nonclean m' | affine rows | verify source | inherited? | verify | verify | nonclean | root algebra | source open |

---

# Gate-0 closure criterion

Gate 0 may be marked `CLOSED` only after all of the following are proved from source:

1. every surviving packet appears in the census;
2. every packet has an exact coefficient and multiplicity;
3. all row weights have an exact provenance and bound;
4. each packet is routed to ROOT or CLOSED_EXCEPTION;
5. no `NEW_OPERATOR_POSSIBLE` entry remains;
6. global reassembly does not double-count or subtract the same main projection twice.

Until then:

```text
GATE 0: OPEN SOURCE CENSUS
```

This is compatible with substantial finite progress already being banked.