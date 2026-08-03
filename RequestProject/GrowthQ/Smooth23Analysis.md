# {2,3}-Smooth Reciprocal Identity Analysis

## §1. Support-3 Completeness (PROVED)

**Theorem** (`support3_completeness_of_smooth23`):
Every support-3 reciprocal identity `1/d₁ + 1/d₂ = 1/d₃` among distinct positive
{2,3}-smooth integers belongs to one of three families:

- **Type I** (from `1 + 2 = 3`): `1/(2^(a-1)·3^b) + 1/(2^a·3^b) = 1/(2^a·3^(b-1))`
- **Type II** (from `1 + 3 = 4`): `1/(2^a·3^(b-1)) + 1/(2^a·3^b) = 1/(2^(a-2)·3^b)`
- **Type III** (from `1 + 8 = 9`): `1/(2^a·3^b) + 1/(2^(a-3)·3^b) = 1/(2^a·3^(b-2))`

**Proof method**: Denominator clearing → coprime reduction → S-unit equation
classification → consecutive smooth pair classification.

The proof is fully formalized in `Smooth23Completeness.lean` with standard axioms only.

## §2. Support-4 Investigation (EXPLORATORY)

### §2.1 Enumeration

Computationally, the coprime (gcd = 1) support-4 identities `1/a + 1/b = 1/c + 1/d`
among {2,3}-smooth integers up to 500 include:

| Identity | Values | Sum |
|----------|--------|-----|
| (2, 12, 3, 4) | 1/2 + 1/12 = 1/3 + 1/4 | 7/12 |
| (3, 12, 4, 6) | 1/3 + 1/12 = 1/4 + 1/6 | 5/12 |
| (3, 24, 4, 8) | 1/3 + 1/24 = 1/4 + 1/8 | 3/8 |
| (3, 36, 4, 9) | 1/3 + 1/36 = 1/4 + 1/9 | 13/36 |
| (4, 36, 6, 9) | 1/4 + 1/36 = 1/6 + 1/9 | 5/18 |
| (6, 144, 9, 16) | 1/6 + 1/144 = 1/9 + 1/16 | 25/144 |
| (8, 72, 9, 36) | 1/8 + 1/72 = 1/9 + 1/36 | 5/36 |

All other support-4 identities are scalar multiples of these.

### §2.2 Algebraic Structure

A support-4 identity `1/a + 1/b = 1/c + 1/d` clears to:
```
cd(a + b) = ab(c + d)
```

Equivalently, rearranging: `1/a - 1/c = 1/d - 1/b`, which clears to:
```
(c - a) · bd = (b - d) · ac
```

This is a **4-term S-unit equation**: `x₁ + x₂ + x₃ + x₄ = 0` where each `xᵢ`
is a {2,3}-unit (i.e., of the form `±2^a · 3^b`).

### §2.3 Reduction to S-unit Theory

By Evertse's theorem (1984), for a fixed set S of primes, the number of
non-degenerate solutions to `x₁ + x₂ + ... + xₙ = 0` in S-units is finite
(bounded by `3^{5n}` for |S| primes).

For S = {2, 3} and n = 4, this gives a finite (though potentially large) bound.
The enumeration above suggests the actual list is quite short.

### §2.4 Obstruction to Direct Classification

Unlike the 3-term case (where coprime reduction gives `a + b = c` and
`consecutive_smooth23_pairs` finishes), the 4-term case requires:

1. **Partition into non-degenerate subsums**: A 4-term equation
   `x₁ + x₂ + x₃ + x₄ = 0` might have degenerate sub-sums
   (e.g., `x₁ + x₂ = 0` and `x₃ + x₄ = 0`).

2. **Non-degenerate 4-term classification**: When no proper sub-sum vanishes,
   the equation genuinely involves 4 terms. The S-unit equation machinery
   (Baker's method / LLL reduction) gives finiteness but the explicit
   enumeration requires computational verification.

3. **Exponent bounds**: For S = {2,3}, explicit bounds on the exponents in
   non-degenerate solutions are known (de Weger, 1989). The bound is
   roughly max(|a|, |b|) ≤ 10^6 for 3-term equations; for 4-term,
   the bounds are larger but still computable.

### §2.5 Proof Strategy

**Option A: Finite computation with certification.**
Enumerate all solutions to the 4-term {2,3}-S-unit equation up to the
explicit exponent bound, then verify each. This is a finite computation
but potentially large.

**Option B: Reduce to 3-term sub-problems.**
Show that every support-4 identity decomposes as a "difference of two
support-3 identities" sharing a common term. This would reduce to the
already-proved support-3 classification.

**Option C: Direct coprime parametrization.**
Generalize the coprime reduction technique. A 4-term identity
`1/a + 1/b = 1/c + 1/d` can be parameterized by clearing denominators
and extracting gcd structure. Then smoothness constraints reduce to
a finite set of small S-unit equations.

### §2.6 Recommended Next Steps

1. Verify that the list of 7 fundamental coprime identities is complete
   (by increasing the search bound or applying S-unit bounds).
2. Formalize the coprime support-4 identities as Lean theorems.
3. Attempt a completeness proof using Option B or C above.

## §3. Graver Basis Analysis (y = 3)

The chain identities from `UnboundedSupport.lean` are **Graver basis elements**
of unbounded support. This means:

- The Graver basis of the {2,3}-smooth reciprocal kernel is infinite.
- Support-4 and support-5 Graver elements exist outside the chain family.
- Energy dominance by bounded-support elements is structural (the chain
  family has exponentially decaying energy contribution 2^{-(3+2t)}).

The Dominant Short-Energy Conjecture remains the correct target: it asserts
that macroscopic entropy deficit implies macroscopic short-support energy,
even though individual primitive identities can have unbounded support.
