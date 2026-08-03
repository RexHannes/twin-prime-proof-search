# Cofactor Genealogy Analysis

**Date:** 2026-06-08 (Session 9)

---

## 1. C₄ Self-Closure is FALSE

### Background

Session 8 identified the cofactor set C₄ = {5, 7, 13, 19, 41, 43} arising from
v₂/v₃-peeling of the 7 "bad" support-4 {2,3}-smooth cores. The question was
whether C₄ is **self-closing**: does peeling {2,3,C₄}-smooth vectors produce
only C₄-smooth cofactors?

### Computational disproof

An exhaustive scan of support-5 {2,3}-smooth cores up to MAX_VALUE = 10⁶ found:
- **1213 primitive support-5 {2,3}-smooth cores**
- **400 peels** violating C₄-closure
- **26 outside-C₄ primes**: {11, 17, 23, 29, 31, 37, 53, 59, 61, 67, 71, 73,
  83, 107, 113, 127, 193, 227, 331, 547, 661, 683, 757, 1093, 2731, 43691}

### Formal counterexample (Lean-verified)

The identity **32 + 3 + 1 = 27 + 9** is a support-5 {2,3}-smooth kernel equation.

v₃-peeling (merging coprime-to-3 terms {32, 1}):
- S₃ = 32 + 1 = 33 = 3 · 11
- v₃(33) = 1, divide by 3
- Merged value = 11
- Remaining terms {3, 9, 27}/3 = {1, 3, 9}
- **Residual: 11 + 1 - 3 - 9 = 0**, i.e., **1 + 11 = 12**

The cofactor **11 ∉ C₄**, proving C₄ is not self-closing.

This is also verified as a reciprocal identity:
  1/27 + 1/288 + 1/864 = 1/32 + 1/96 = 1/24

All five denominators {27, 32, 96, 288, 864} are {2,3}-smooth.

---

## 2. Arithmetic Origin of Bad Cofactors

### v₃-peel cofactors from 2-term merges

When merging two coprime-to-3 terms 2^a and 2^b (with signs), the sum is
2^min(a,b) · (2^|a-b| ± 1). The bad cofactor is the 6-free part of 2^n ± 1.

| Expression | n | Value | 6-free part | Note |
|-----------|---|-------|-------------|------|
| 2^1 + 1 | 1 | 3 | 1 | smooth |
| 2^2 + 1 | 2 | 5 | **5** | in C₄ |
| 2^3 + 1 | 3 | 9 | 1 | smooth |
| 2^4 + 1 | 4 | 17 | **17** | outside C₄ |
| 2^5 + 1 | 5 | 33 | **11** | **outside C₄** |
| 2^7 + 1 | 7 | 129 | **43** | in C₄ |
| 2^9 + 1 | 9 | 513 | **19** | in C₄ |
| 2^11 + 1 | 11 | 2049 | **683** | outside C₄ |
| 2^13 + 1 | 13 | 8193 | **2731** | outside C₄ |
| 2^17 + 1 | 17 | 131073 | **43691** | outside C₄ |
| 2^3 - 1 | 3 | 7 | **7** | in C₄ |
| 2^4 - 1 | 4 | 15 | **5** | in C₄ |
| 2^5 - 1 | 5 | 31 | **31** | outside C₄ |
| 2^7 - 1 | 7 | 127 | **127** | outside C₄ |

### Key insight: v₃-peel divisibility criterion

For the v₃-peel to be "useful" (actually reduce 3-adic valuation of remaining
terms), we need 3 | S₃. For 2-term merges:

- **3 | (2^n + 1)** iff **n is odd** (proved in Lean)
- **3 | (2^n - 1)** iff **n is even** (proved in Lean)

### v₂-peel cofactors from 2-term merges

Similarly, merging two odd-weight terms 3^a and 3^b gives 3^min · (3^|a-b| ± 1).
The cofactor is the 6-free part of 3^n ± 1.

---

## 3. Cofactor Genealogy Framework

### Why a fixed finite set cannot work

The bad cofactors from 2-term merges grow without bound because:
- The 6-free parts of 2^n + 1 and 2^n - 1 include arbitrarily large primes
  (Fermat/Mersenne-like phenomena)
- For each new support level, new exponent differences become available,
  producing new cofactors

### The genealogy structure

Instead of a closed cofactor set, we have a **genealogy**:

- **Level 0**: Pure {2,3}-smooth (the starting point)
- **Generation 1**: Single peel of support-4 cores → C₄ = {5, 7, 13, 19, 41, 43}
  (from 3^n ± 1 with n ≤ 4)
- **Generation 2**: Single peel of support-5 cores → adds {11, 17, 31, ...}
  (from 2^n ± 1 with new n values, and from 4-term peel sums)
- **Generation k**: Each level can introduce new primes

The genealogy is indexed by:
1. The prime p (the bad cofactor)
2. The exponent expression producing p (e.g., p | 2^5 + 1)
3. The peel type (v₂ or v₃)
4. The number of merged terms (2 or 4)

---

## 4. Residual-Family Equivalence

### Definition

Two {2,3}-smooth identities produce **equivalent residuals** if their peel
residuals, after normalizing by common {2,3}-smooth scaling, have the same
coprime core.

### F₁₁ family is not unique

The cofactor-11 residual is NOT a unique coprime core. The seven solutions
to 11 + a = b + c with {2,3}-smooth a, b, c are:

| (a, b, c) | Identity |
|-----------|----------|
| (1, 3, 9) | 11 + 1 = 3 + 9 = 12 |
| (1, 4, 8) | 11 + 1 = 4 + 8 = 12 |
| (1, 6, 6) | 11 + 1 = 6 + 6 = 12 |
| (2, 4, 9) | 11 + 2 = 4 + 9 = 13 |
| (3, 6, 8) | 11 + 3 = 6 + 8 = 14 |
| (4, 6, 9) | 11 + 4 = 6 + 9 = 15 |
| (6, 8, 9) | 11 + 6 = 8 + 9 = 17 |

Each corresponds to a different residual family shape.

---

## 5. Lean Formalization Status

### Proved (zero sorry, standard axioms only)

| Theorem | Description |
|---------|------------|
| `support5_identity_11` | 32 + 3 + 1 - 27 - 9 = 0 |
| `support5_*_smooth` | All 5 entries are {2,3}-smooth |
| `v3_peel_residual` | Residual: 11 + 1 - 3 - 9 = 0 |
| `eleven_not_smooth23` | 11 is not {2,3}-smooth |
| `eleven_not_in_C4` | 11 ∉ C₄ |
| `C4_not_self_closing` | Combined C₄ non-closure theorem |
| `reciprocal_identity_11` | Reciprocal form: 1/27 + 1/288 + 1/864 = 1/32 + 1/96 |
| `v3_cofactors_small` | 6-free parts of 2^n + 1 for n = 1..5 |
| `useful_v3_peel_criterion` | 3 | (2^n + 1) ↔ n is odd |
| `useful_v3_peel_criterion_minus` | 3 | (2^n - 1) ↔ n is even |
| `outsideC4_all_prime` | All 13 small outside-C₄ primes are prime |
| `outsideC4_disjoint` | Disjoint from C₄ |
| `outsideC4_not_smooth` | None are {2,3}-smooth |
| `F11_family_*` | All 7 cofactor-11 residual identities |
| `support5_cofactor5` | Support-5 identity giving cofactor 5 |
| `support5_cofactor7` | Support-5 identity giving cofactor 7 |

### Definitions introduced

| Definition | Description |
|-----------|------------|
| `removeFactorsAux` | Remove all factors of p (fuel-bounded) |
| `sixFreePart` | Remove all factors of 2 and 3 |
| `v3PeelCofactor2` | v₃-peel cofactor from 2-term merge |
| `v2PeelCofactor2` | v₂-peel cofactor from 2-term merge |
| `SignedEntry` | Signed kernel entry (sign + weight) |
| `ResidualFamilyData` | Residual family specification |
| `C4` | The support-4 cofactor set {5,7,13,19,41,43} |
| `outsideC4Small` | Outside-C₄ primes ≤ 100 |

---

## 6. What Is NOT Attempted

Per the user's instructions:
- **No y=3 tail decay** attempt
- **No C₄ self-closure proof** (it is false)
- **No bounded cofactor set** claim at any level
