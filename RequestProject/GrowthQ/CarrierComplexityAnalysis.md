# Carrier Complexity Analysis

**Session 10 — 2026-06-08**

## 1. Motivation and Context

### What failed
- **C₄ self-closure**: The support-4 cofactor set C₄ = {5,7,13,19,41,43} is NOT
  self-closing under support-5 peeling. An exhaustive scan found 26 new primes
  outside C₄ among the support-5 peel residuals.
- **Small residual catalogue**: 395 distinct residual signatures among 400 bad
  peels — far too many for manual enumeration.

### What works
- **Carrier complexity 1**: All 400 bad support-5 peels have exactly ONE
  residual term with a prime factor outside ALLOWED = {2,3,5,7,13,19,41,43}.
  All other terms are ALLOWED-smooth.

## 2. Definitions

### ALLOWED = {2,3,5,7,13,19,41,43}

This is the union of {2,3} (the smooth base for y=3) and
C₄ = {5,7,13,19,41,43} (the cofactors from support-4 bad cores).

### IsAllowedSmooth(n)
Every prime factor of n lies in ALLOWED.

### HasOutsideCarrier(n)
¬ IsAllowedSmooth(n): there exists a prime p ∣ n with p ∉ ALLOWED.

### Carrier complexity
The number of terms in a residual equation whose weight has an outside carrier.

## 3. Empirical Data Summary

| Metric | Value |
|--------|-------|
| Primitive support-5 {2,3}-smooth cores | 1213 |
| Bad peels (outside C₄) | 400 |
| Distinct residual signatures | 395 |
| Non-single-carrier rows | **0** |
| Carrier complexity distribution | 400 × complexity 1 |

### Residual support distribution
| Support | Count |
|---------|-------|
| 3 (carrier + 2 smooth) | 29 |
| 4 (carrier + 3 smooth) | 371 |

### Carrier multiplier counts
| Multiplier count | Frequency |
|-----------------|-----------|
| 1 | 246 |
| 5 | 55 |
| 2 | 21 |
| 4 | 12 |
| 3 | 10 |

### Most common outside parts
11, 61, 17, 121 (=11²), 341 (=11·31), 73, 547, 683, 3641 (=11·331), 1093

## 4. Formalized Content

### Lean file: `CarrierComplexity.lean`

**Zero sorry. Standard axioms only.**

#### Definitions formalized
- `AllowedPrimes : Finset ℕ` — the 8-element allowed set
- `IsAllowedSmooth : ℕ → Prop` — all prime factors in ALLOWED
- `HasOutsideCarrier : ℕ → Prop` — ¬ IsAllowedSmooth
- `Carrier1Certificate` — structure for carrier-1 residual equations
- `Carrier1Certificate.IsValid` — validity predicate

#### Proved theorems (selection)
- `AllowedPrimes_all_prime`: every element of ALLOWED is prime
- `isAllowedSmooth_of_smooth23`: {2,3}-smooth ⊂ ALLOWED-smooth
- `isAllowedSmooth_of_dvd`: divisor-closed
- `isAllowedSmooth_mul`: product-closed
- `hasOutsideCarrier_iff`: equivalent to ∃ prime factor ∉ ALLOWED
- `carrier1_certificate_gives_complexity_one`: valid cert → complexity 1
- `carrier_determined_by_smooth`: carrier value = − Σ smooth values
- `commonOutsideParts_are_outside`: all 10 common outside parts verified

#### Verified certificates (8 representative)
| Outside part | Certificate | Equation |
|-------------|-------------|----------|
| 11 | `cert_11_a` | 11 + 1 − 3 − 9 = 0 |
| 61 (via 122) | `cert_61_a` | 122 + 1 − 27 − 96 = 0 |
| 17 (via 85) | `cert_17_a` | 85 − 4 − 81 = 0 |
| 121 (= 11²) | `cert_121_a` | 121 + 7 − 128 = 0 |
| 341 (= 11·31) | `cert_341_a` | 341 − 1 − 16 − 324 = 0 |
| 73 | `cert_73_a` | 73 + 8 − 81 = 0 |
| 547 | `cert_547_a` | 547 + 13 − 560 = 0 |
| 683 | `cert_683_a` | 683 + 1 − 684 = 0 |

## 5. Strategic Assessment

### Why carrier complexity 1 matters

If every peel step introduces at most one exotic prime factor, then:

1. **The exotic factor is a "tag"** that tracks the peel's non-smooth contribution.
   It can be factored out or isolated.

2. **The ALLOWED-smooth frame** constrains the residual: the smooth terms determine
   the carrier value (up to sign), so there are only finitely many possible carrier
   values for each smooth frame.

3. **Descent potential**: If peeling reduces support while maintaining carrier
   complexity 1, then iterating gives a chain:
   ```
   support k → support (k-1) → ... → support 3
   ```
   where each residual has at most one exotic factor. This is a descent argument
   that could eventually bound primitive identity support.

### Why this replaces C₄-closure

C₄-closure asked: "do cofactors stay in a fixed finite set?"
Answer: No (26+ primes found).

Carrier complexity asks: "how many exotic terms appear per residual?"
Answer: exactly 1 (universally observed).

The key insight is that **we don't need the exotic primes to come from a fixed set**.
We only need there to be **at most one** exotic term per peel step. This is a much
weaker condition that may be provable.

### What would be needed for a proof

A proof that carrier complexity ≤ 1 for support-5 (or general support-k) {2,3}-smooth
peels would require showing:

1. The merged peel value M = Σ±2^aᵢ (coprime-to-3 terms) can contribute at most one
   prime factor outside ALLOWED when divided by 3^m.

2. Since M is a sum/difference of powers of 2, its factorization is controlled by
   the Aurifeuillean/Cunningham structure of 2^a ± 2^b = 2^min(a,b)(2^|a-b| ± 1).
   The factor 2^|a-b| ± 1 may have multiple prime factors, but only one can be
   outside ALLOWED (the others being absorbed by the {2,3,C₄} structure).

3. For more than 2 coprime-to-3 terms, the merged sum M = Σ±2^aᵢ is a more complex
   expression, and its factorization is harder to control. The empirical evidence
   suggests that even in this case, at most one "new" prime appears.

### Open questions

1. Does carrier complexity 1 hold for support-6+?
2. Is there a number-theoretic explanation (e.g., from the Cunningham tables or
   algebraic factorization of 2^n ± 1)?
3. Can the bounded-carrier property be used directly for energy counting, without
   full descent?
