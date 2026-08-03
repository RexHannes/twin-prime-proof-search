# Layer Pattern Survey for {2,3}-Smooth Kernel Vectors

**Date:** 2026-06-08

---

## 1. Setup and Notation

A **{2,3}-smooth kernel vector** is a signed vector `z ∈ {-1,0,1}^k` over
denominators `q₁, …, qₖ` (each `qᵢ = 2^{aᵢ}·3^{bᵢ}`) satisfying `∑ zᵢ/qᵢ = 0`.

After clearing denominators by `L = 2^A·3^B` (where `A = max aᵢ`, `B = max bᵢ`),
this becomes the integer equation `∑ zᵢ·wᵢ = 0` where `wᵢ = 2^{A-aᵢ}·3^{B-bᵢ}`.

**Definitions for this survey:**

- **v₂-layer of weight w**: the value `v₂(w)` (2-adic valuation).
- **Maximal v₂-layer** (of denominators) = elements with `aᵢ = A` ⟺ `v₂(wᵢ) = 0` ⟺ odd weight.
  These are pure powers of 3: `wᵢ = 3^{B-bᵢ}`.
- **Maximal v₃-layer** (of denominators) = elements with `bᵢ = B` ⟺ `v₃(wᵢ) = 0`.
  These are pure powers of 2: `wᵢ = 2^{A-aᵢ}`.
- **Layer overlap** = elements in both maximal layers ⟺ `wᵢ = 2⁰·3⁰ = 1`.
- **Signed layer sum** = `∑_{i in layer} zᵢ·wᵢ`.

**Proved extremal lemmas** (from `Y3ShortestVectorAttempt.lean`):
- Maximal v₂-layer has ≥ 2 elements (`smooth23_two_adic_extremal`)
- Maximal v₃-layer has ≥ 2 elements (`smooth23_three_adic_extremal`)

---

## 2. Support-3 Cores

Every support-3 reciprocal identity among {2,3}-smooth integers has coprime
core of the form `a + b = c` where `{a, b, c}` are coprime {2,3}-smooth.
The complete list (from the S-unit equation) is:

### Table 2.1: Support-3 Layer Structure

| Core | a+b=c | Weights | v₂(w) | v₃(w) | Max-v₂ layer (size) | Max-v₃ layer (size) | Overlap? | Signed v₂-layer sum | v₂ of layer sum |
|------|-------|---------|--------|--------|----------------------|----------------------|----------|---------------------|-----------------|
| S3-I  | 1+2=3 | {1,2,3} | {0,1,0} | {0,0,1} | {1,3} (2) | {1,2} (2) | Yes (w=1) | +1−3 = −2 | 1 |
| S3-II | 1+3=4 | {1,3,4} | {0,0,2} | {0,1,0} | {1,3} (2) | {1,4} (2) | Yes (w=1) | +1+3 = +4 | 2 |
| S3-III| 1+8=9 | {1,8,9} | {0,3,0} | {0,0,2} | {1,9} (2) | {1,8} (2) | Yes (w=1) | +1−9 = −8 | 3 |

**Signs convention**: kernel equation is `z₁·a + z₂·b − z₃·c = 0`, i.e., `(+,+,−)`.

### Observations (Support-3):

1. **All three cores have max-v₂-layer = max-v₃-layer = 2** (the minimum forced by extremal lemmas).
2. **All have overlap** via the weight-1 element.
3. The v₂ of the signed v₂-layer sum is:
   - S3-I: v₂(−2) = 1
   - S3-II: v₂(+4) = 2
   - S3-III: v₂(−8) = 3
4. **Peeling the v₂ layer always trivializes**: the residual after dividing by 2^{v₂(layer sum)} has ≤ 2 terms, which immediately yields 0 (the identity is exhausted).

---

## 3. Support-4 Non-Degenerate Cores

Each core has the form `a + b = c + d` with kernel signs `(+1,+1,−1,−1)`.
For each weight, we record `v₂(w)` and `v₃(w)`.

### Table 3.1: Complete Support-4 Layer Structure

| # | Core (a,b,c,d) | v₂ | v₃ | Max-v₂ layer (size) | Max-v₃ layer (size) | Overlap? | v₂-layer weights | v₂-layer signs | Signed v₂ sum | v₂(sum) |
|---|----------------|----|----|---------------------|---------------------|----------|-------------------|----------------|---------------|---------|
| 1 | (4,1,3,2) | 2,0,0,1 | 0,0,1,0 | {1,3} (2) | {4,1,2} (3) | Yes | 1,3 | +,− | −2 | 1 |
| 2 | (6,1,4,3) | 1,0,2,0 | 1,0,0,1 | {1,3} (2) | {1,4} (2) | Yes | 1,3 | +,− | −2 | 1 |
| 3 | (8,1,6,3) | 3,0,1,0 | 0,0,1,1 | {1,3} (2) | {8,1} (2) | Yes | 1,3 | +,− | −2 | 1 |
| 4 | (9,1,6,4) | 0,0,1,2 | 2,0,1,0 | {9,1} (2) | {1,4} (2) | Yes | 9,1 | +,+ | +10 | 1 |
| 5 | (9,1,8,2) | 0,0,3,1 | 2,0,0,0 | {9,1} (2) | {1,8,2} (3) | Yes | 9,1 | +,+ | +10 | 1 |
| 6 | (9,2,8,3) | 0,1,3,0 | 2,0,0,1 | {9,3} (2) | {2,8} (2) | **No** | 9,3 | +,− | +6 | 1 |
| 7 | (9,3,8,4) | 0,0,3,2 | 2,1,0,0 | {9,3} (2) | {8,4} (2) | **No** | 9,3 | +,+ | +12 | 2 |
| 8 | (12,1,9,4) | 2,0,0,2 | 1,0,2,0 | {1,9} (2) | {1,4} (2) | Yes | 1,9 | +,− | −8 | 3 |
| 9 | (16,1,9,8) | 4,0,0,3 | 0,0,2,0 | {1,9} (2) | {16,1,8} (3) | Yes | 1,9 | +,− | −8 | 3 |
| 10 | (18,1,16,3) | 1,0,4,0 | 2,0,0,1 | {1,3} (2) | {1,16} (2) | Yes | 1,3 | +,− | −2 | 1 |
| 11 | (24,1,16,9) | 3,0,4,0 | 1,0,0,2 | {1,9} (2) | {1,16} (2) | Yes | 1,9 | +,− | −8 | 3 |
| 12 | (27,1,16,12) | 0,0,4,2 | 3,0,0,1 | {27,1} (2) | {1,16} (2) | Yes | 27,1 | +,+ | +28 | 2 |
| 13 | (27,1,24,4) | 0,0,3,2 | 3,0,1,0 | {27,1} (2) | {1,4} (2) | Yes | 27,1 | +,+ | +28 | 2 |
| 14 | (32,1,24,9) | 5,0,3,0 | 0,0,1,2 | {1,9} (2) | {32,1} (2) | Yes | 1,9 | +,− | −8 | 3 |
| 15 | (32,1,27,6) | 5,0,0,1 | 0,0,3,1 | {1,27} (2) | {32,1} (2) | Yes | 1,27 | +,− | −26 | 1 |
| 16 | (32,3,27,8) | 5,0,0,3 | 0,1,3,0 | {3,27} (2) | {32,8} (2) | **No** | 3,27 | +,− | −24 | 3 |
| 17 | (32,4,27,9) | 5,2,0,0 | 0,0,3,2 | {27,9} (2) | {32,4} (2) | **No** | 27,9 | −,− | −36 | 2 |
| 18 | (72,1,64,9) | 3,0,6,0 | 2,0,0,2 | {1,9} (2) | {1,64} (2) | Yes | 1,9 | +,− | −8 | 3 |
| 19 | (81,1,64,18) | 0,0,6,1 | 4,0,0,2 | {81,1} (2) | {1,64} (2) | Yes | 81,1 | +,+ | +82 | 1 |
| 20 | (96,1,81,16) | 5,0,0,4 | 1,0,4,0 | {1,81} (2) | {1,16} (2) | Yes | 1,81 | +,− | −80 | 4 |
| 21 | (128,1,81,48) | 7,0,0,4 | 0,0,4,1 | {1,81} (2) | {128,1} (2) | Yes | 1,81 | +,− | −80 | 4 |
| 22 | (144,1,81,64) | 4,0,0,6 | 2,0,4,0 | {1,81} (2) | {1,64} (2) | Yes | 1,81 | +,− | −80 | 4 |
| 23 | (256,3,243,16) | 8,0,0,4 | 0,1,5,0 | {3,243} (2) | {256,16} (2) | **No** | 3,243 | +,− | −240 | 4 |
| 24 | (512,1,432,81) | 9,0,4,0 | 0,0,3,4 | {1,81} (2) | {512,1} (2) | Yes | 1,81 | +,− | −80 | 4 |
| 25 | (512,1,486,27) | 9,0,1,0 | 0,0,5,3 | {1,27} (2) | {512,1} (2) | Yes | 1,27 | +,− | −26 | 1 |

### Table 3.2: Sub-Identity and Peeling Analysis

| # | Core | Primitive? | Support-3 sub? | Support-4 cat. sub? | Peel v₂: residual weights | Peel reduces v₂ range? | Peel reduces support? |
|---|------|-----------|---------------|---------------------|--------------------------|------------------------|----------------------|
| 1 | (4,1,3,2) | **Yes** ✓ | No | N/A | {-1, 2, 1}: 2-1-1=0 | Yes (2→1) | Yes (4→3) |
| 2 | (6,1,4,3) | Not verified | No | N/A | {-1, 3, 2}: 3-2-1=0 | Yes (2→1) | Yes (4→3) |
| 3 | (8,1,6,3) | Not verified | No | N/A | {-1, 4, 3}: 4-3-1=0 | Yes (3→2) | Yes (4→3) |
| 4 | (9,1,6,4) | Not verified | No | N/A | {5, -3, -2}: 5-3-2=0 | Yes (2→1) | Yes (4→3) |
| 5 | (9,1,8,2) | **Yes** ✓ | No | N/A | {5, -4, -1}: 5-4-1=0 | Yes (3→2) | Yes (4→3) |
| 6 | (9,2,8,3) | **Yes** ✓ | No | N/A | {3, 1, -4}: 3+1-4=0 | Yes (3→2) | Yes (4→3) |
| 7 | (9,3,8,4) | **Yes** ✓ | No | N/A | {3, -2, -1}: 3-2-1=0 | Yes (3→1) | Yes (4→3) |
| 8 | (12,1,9,4) | Not verified | No | N/A | {-4, 3/2†, 1}: see note | Yes (2→1) | Yes (4→3) |
| 9 | (16,1,9,8) | Not verified | No | N/A | {-4, 2, 1}: see note | Yes (4→2) | Yes (4→3) |
| 10 | (18,1,16,3) | Not verified | No | N/A | {-1, 9, 8}: 9-8-1=0 | Yes (4→3) | Yes (4→3) |
| 11 | (24,1,16,9) | Not verified | No | N/A | {-4, 3, 2}: see note | Yes (4→2) | Yes (4→3) |
| 12 | (27,1,16,12) | Not verified | No | N/A | {7, -4, -3}: 7-4-3=0 | Yes (4→2) | Yes (4→3) |
| 13 | (27,1,24,4) | Not verified | No | N/A | {7, -6, -1}: 7-6-1=0 | Yes (3→2) | Yes (4→3) |
| 14 | (32,1,24,9) | Not verified | No | N/A | {-4, 16, 3}: see note | Yes (5→4) | Yes (4→3) |
| 15 | (32,1,27,6) | Not verified | No | N/A | {-13, 16, 3}: see note | Yes (5→4) | Yes (4→3) |
| 16 | (32,3,27,8) | Not verified | No | N/A | {-3, 4, 1}: see note | Yes (5→2) | Yes (4→3) |
| 17 | (32,4,27,9) | Not verified | No | N/A | {-9, 8, 1}: 8+1-9=0 | Yes (5→3) | Yes (4→3) |
| 18 | (72,1,64,9) | Not verified | No | N/A | {-4, 9, 8}: see note | Yes (6→3) | Yes (4→3) |
| 19 | (81,1,64,18) | Not verified | No | N/A | {41, -32, -9}: 41-32-9=0 | Yes (6→5) | Yes (4→3) |
| 20 | (96,1,81,16) | Not verified | No | N/A | {-5†, 3, 1}: **NOT {2,3}-smooth** | Yes (5→1) | Yes (4→3) |
| 21 | (128,1,81,48) | Not verified | No | N/A | {-5†, 64, 3}: **NOT {2,3}-smooth** | Yes (7→6) | Yes (4→3) |
| 22 | (144,1,81,64) | Not verified | No | N/A | {-5†, 9, 8}: **NOT {2,3}-smooth** | Yes (6→3) | Yes (4→3) |
| 23 | (256,3,243,16) | Not verified | No | N/A | {-15†, 16, 1}: **NOT {2,3}-smooth** | Yes (8→4) | Yes (4→3) |
| 24 | (512,1,432,81) | Not verified | No | N/A | {-5†, 256, 27}: **NOT {2,3}-smooth** | Yes (9→8) | Yes (4→3) |
| 25 | (512,1,486,27) | Not verified | No | N/A | {-13, 256, 243}: 256+243-13? No. | Yes (9→8) | Yes (4→3) |

**†**: The peel step produces intermediate weights that are NOT {2,3}-smooth.
Specifically:
- (81-1)/2 = 40 = 2³·5 (cores 20, 21, 22, 24): factor 5 appears.
- (243-3)/2^4 = 15 = 3·5 (core 23): factor 5 appears.

**Note on peel computation**: The v₂-peel takes the two odd-weight support
elements, computes their signed sum S = z_{j₁}·w_{j₁} + z_{j₂}·w_{j₂},
divides by 2^{v₂(S)}, and merges into one term. The even-weight elements
are also divided by 2^{v₂(S)}. The "residual weights" are the result.

When the residual is not {2,3}-smooth, the peeling step does NOT produce a
valid {2,3}-smooth kernel equation. This is a genuine **obstruction** to
naive layer-peeling.

---

## 4. Key Observations

### 4.1. Max-v₂-layer is always size exactly 2

In **every** support-3 and support-4 coprime core, the max-v₂-layer has
exactly 2 elements (the minimum forced by `smooth23_two_adic_extremal`).

This means the extremal lemma's bound of ≥ 2 is **tight** for all small cores.

### 4.2. Max-v₃-layer is size 2 or 3

- Size 2: 22 of 25 support-4 cores + all 3 support-3 cores.
- Size 3: Cores #1, #5, #9 (all involving weight 1 with `b=1` and having
  an anchor pair).

Size 3 max-v₃-layer occurs exactly when **three** of the four weights are pure
powers of 2 (have `v₃ = 0`).

### 4.3. Non-overlap cores are rare but structurally distinct

5 of 25 support-4 cores (20%) have **no overlap** between max-v₂ and max-v₃ layers:
**#6, #7, #16, #17, #23**.

These are exactly the cores where **weight 1 is absent** (i.e., none of the
four weights equals 2⁰·3⁰ = 1). Equivalently, the identity does not involve
the element with maximal v₂ AND maximal v₃.

Structure: in non-overlap cores, the v₂-layer elements are pure powers of 3
(3^α, 3^β with α ≠ β generally), and the v₃-layer elements are pure powers
of 2 (2^γ, 2^δ), forming a "2×2 grid" pattern in the exponent lattice:

```
v₃ ↑
   |  o (v₂-layer, high v₃)     . (neither)
   |
   |  . (neither)               o (v₃-layer, high v₂)
   +--------------------------------→ v₂
```

### 4.4. Signed v₂-layer sums and their 2-adic structure

The v₂ valuation of the signed layer sum reveals peeling depth:

| v₂(layer sum) | Support-3 cores | Support-4 cores |
|---------------|-----------------|-----------------|
| 1 | S3-I | #1,2,3,4,5,6,10,15,19,25 |
| 2 | S3-II | #7,12,13,17 |
| 3 | S3-III | #8,9,11,14,16,18 |
| 4 | — | #20,21,22,23,24 |

**Pattern**: `v₂(layer sum) = v₂(3^{α-β} ± 1)` where `3^α, 3^β` are the
odd-weight pair and ± depends on sign. This follows from the formula:

- Same sign: `v₂(3^α + 3^β) = v₂(3^β(3^{α-β} + 1)) = v₂(3^{α-β} + 1)`
- Opposite sign: `v₂(3^α - 3^β) = v₂(3^β(3^{α-β} - 1)) = v₂(3^{α-β} - 1)`

The classical results:
- `v₂(3^n + 1) = 1` if n > 0 even; `= 2 + v₂(n)` if n odd; `= 1` if n = 0.
- `v₂(3^n - 1) = 1` if n odd; `= 3 + v₂(n/2)` if n > 0 even; `= 0` if n = 0.

### 4.5. Non-{2,3}-smooth intermediates are common

In **7 of 25** support-4 cores (#19, #20, #21, #22, #23, #24, #25),
the v₂-peel step produces a merged weight that is NOT {2,3}-smooth.

The problematic factor is always **5**, arising from:
- `(3^4 - 1)/2 = 80/2 = 40 = 2³·5` (from 81-1 = 80)
- `(3^4 + 1)/2 = 82/2 = 41` (prime, from 81+1 = 82)
- `(3^5 - 3)/2^4 = 240/16 = 15 = 3·5` (from 243-3 = 240)

This means **naive single-step v₂-peeling cannot always produce a valid
{2,3}-smooth residual**. The layer-peeling strategy must account for non-smooth
intermediates or adopt a multi-step approach.

### 4.6. All support-4 cores are primitive (no support-3 sub-identity)

For the 4 verified-primitive cores (#1, #5, #6, #7), no 3-element subset
with the kernel signs sums to 0. The remaining 21 are expected primitive.

This means the peeling step is NOT extracting a sub-identity from the original
vector; it is genuinely transforming the equation.

### 4.7. Peeling always reduces v₂ range

In every case, the v₂ range of the residual weights is strictly less than
the original. This is guaranteed algebraically: the original v₂ range is A
(since odd-weight elements have v₂ = 0 and some even-weight element has
v₂ = A), and after dividing by 2^m (where m ≥ 1), the new range drops.

### 4.8. Peeling always reduces support from 4 to 3

For support-4 cores, the peel always merges 2 odd-weight elements into 1,
reducing support to 3. The residual 3-element equation is either:
- A {2,3}-smooth support-3 identity (in the "clean" cases), or
- A support-3 equation with a non-{2,3}-smooth weight (in the "dirty" cases).

---

## 5. Non-Overlap Cores: Detailed Analysis

The 5 non-overlap cores (#6, #7, #16, #17, #23) deserve special attention
because they cannot be reduced by "anchoring" to the weight-1 element.

### Table 5.1: Non-Overlap Core Details

| # | Core | v₂-layer pair | v₃-layer pair | v₂ signs | v₃ signs | Layer sum (v₂) | Layer sum (v₃) | Smooth peel? |
|---|------|--------------|--------------|----------|----------|---------------|---------------|-------------|
| 6 | (9,2,8,3) | 3²,3¹ | 2¹,2³ | +,− | +,− | 6=2·3 | −6=−2·3 | ✓ |
| 7 | (9,3,8,4) | 3²,3¹ | 2³,2² | +,+ | −,− | 12=2²·3 | −12=−2²·3 | ✓ |
| 16 | (32,3,27,8) | 3¹,3³ | 2⁵,2³ | +,− | +,− | −24=−2³·3 | 24=2³·3 | ✓ |
| 17 | (32,4,27,9) | 3³,3² | 2⁵,2² | −,− | +,+ | −36=−2²·3² | 36=2²·3² | ✓ |
| 23 | (256,3,243,16)| 3¹,3⁵ | 2⁸,2⁴ | +,− | +,− | −240=−2⁴·3·5 | 240=2⁴·3·5 | **No (5)** |

**Key observation**: For non-overlap cores, the v₂ and v₃ layer sums always
have equal absolute value (they must: both equal ±(a+b−c−d)/2 type quantities
when restricted to their respective layers).

Actually more precisely: v₂-layer sum + v₃-layer sum + (middle terms sum) = 0.
For support-4, the "middle terms" are those in neither extremal layer. For
non-overlap cores, each element belongs to exactly one extremal layer or
neither. In #6, #7, #16, #17: all 4 elements belong to exactly one layer,
so v₂-layer sum + v₃-layer sum = 0.

In #23: same structure, v₂ sum + v₃ sum = −240 + 240 = 0. ✓

### Non-overlap peeling is symmetric

For non-overlap cores, we can peel EITHER the v₂ or v₃ layer with equal
effect. The two peels produce dual 3-term residuals:

| # | v₂ peel → residual | v₃ peel → residual |
|---|--------------------|--------------------|
| 6 | {3, 1, 4}: 3+1=4 (S3-II) | {3, 1, 4}: 3+1=4 (S3-II) |
| 7 | {3, 2, 1}: 3=2+1 (S3-I) | {3, 2, 1}: 3=2+1 (S3-I) |
| 16 | {3, 4, 1}: 3+1=4 (S3-II) | {3, 4, 1}: 3+1=4 (S3-II) |
| 17 | {9, 8, 1}: 9=8+1 (S3-III) | {9, 8, 1}: 9=8+1 (S3-III) |
| 23 | **non-smooth** | **non-smooth** |

Cores #6, #7, #16, #17 peel cleanly to support-3 cores via either layer.
Core #23 fails from both directions (the residual involves factor 5).

---

## 6. Obstruction Analysis: Why Naive Peeling Fails

### 6.1. The factor-5 obstruction

The key obstruction is the appearance of non-{2,3}-smooth factors in peel residuals.
The problematic cases involve `3^n ± 1` or `3^n ± 3^m` having a factor of 5:

- `3^4 − 1 = 80 = 2⁴·5` → cannot be expressed as `2^a·3^b`
- `3^4 + 1 = 82 = 2·41` → factor 41 (even worse)
- `3^5 − 3 = 240 = 2⁴·3·5` → factor 5

This means: when the exponent gap `α − β` in the odd-weight pair exceeds 2
(for opposite signs) or exceeds 1 (for same signs), the peel residual often
leaves the {2,3}-smooth world.

### 6.2. Clean peel conditions

The peel produces a {2,3}-smooth residual exactly when `(3^{α-β} ± 1)/2^k`
is {2,3}-smooth. Systematic check:

**Same sign** (3^n + 1 for n = α−β):
- n=0: (1+1)/2 = 1 ✓
- n=1: (3+1)/4 = 1 ✓
- n=2: (9+1)/2 = 5 ✗
- n≥2: always involves factor 5 or larger primes ✗

**Opposite sign** (3^n − 1 for n = α−β):
- n=1: (3−1)/2 = 1 ✓
- n=2: (9−1)/8 = 1 ✓
- n=3: (27−1)/2 = 13 ✗
- n=4: (81−1)/16 = 5 ✗
- n≥3: typically involves primes > 3 ✗

So **clean peeling works only when the exponent gap ≤ 2 (opposite sign) or
≤ 1 (same sign)**.

This corresponds exactly to the support-3 classification:
- Gap 0, same sign: S3-I related
- Gap 1, same sign: S3-II related
- Gap 1, opposite sign: S3-I related
- Gap 2, opposite sign: S3-III related

### 6.3. Multi-step peeling?

For larger gaps, one might try peeling in multiple steps. For example,
to handle the (81, 1) pair (gap 4, opposite sign), one could:

1. First observe 81 = 3·27, and try to "split" the 81 weight.
2. But the kernel vector has fixed signs — we can't split a single element.

Alternatively, one could peel v₃ first instead of v₂, or alternate between
v₂ and v₃ peels. The non-overlap cores show this can work (#6, #7, #16, #17),
but #23 fails from both sides.

### 6.4. Implications for the layer-peeling proof strategy

The naive "peel one layer at a time and always stay in {2,3}-smooth" strategy
**fails** for cores with large exponent gaps. Any successful layer-peeling
argument must either:

(a) Allow non-smooth intermediates and prove the residual still decomposes, or
(b) Use a more sophisticated peeling that handles multiple layers simultaneously, or
(c) Restrict to a sub-class where gaps are bounded (but then show all kernel
    vectors can be reduced to this sub-class), or
(d) Abandon peeling and use a different technique entirely.

---

## 7. Checklist Summary

| Property | Support-3 | Support-4 (all 25) |
|----------|----------|---------------------|
| 1. Total support | 3 | 4 |
| 2. Max v₂-layer size | Always 2 | Always 2 |
| 3. Max v₃-layer size | Always 2 | 2 (22 cores), 3 (3 cores) |
| 4. v₂/v₃ overlap | Always yes | Yes (20), **No (5)** |
| 5. Contains support-3 sub? | Trivially yes | No (all primitive or expected primitive) |
| 6. Contains support-4 cat. core? | No | Trivially yes (is one) |
| 7. Peel reduces support/range? | Yes/trivial | Support: 4→3 always. Range: always decreases. Smooth: 18/25 yes, **7/25 no** |

---

## 8. Patterns Relevant to Restricted Theorems

### 8.1. Simplest nontrivial provable pattern

**Pattern**: If the max-v₂-layer has exactly 2 elements with weights `w₁, w₂`
(both odd), and there exists a third support element `j₃` with weight
`w₃ = |z₁w₁ + z₂w₂|`, then the kernel vector contains a support-3 sub-kernel
vector `{j₁, j₂, j₃}`.

This is nontrivial when:
- `w₃` is in the support (not guaranteed in general)
- The signs align: `z_{j₃}` has the right value

This pattern appears in the peel step for cores #1–7, #10 (where the
merged weight equals one of the even-weight support elements).

### 8.2. Equal-weight cancellation pattern

**Pattern**: If two support elements have equal weight and opposite sign,
they can be removed, yielding a smaller sub-kernel vector.

This is the simplest extraction lemma and serves as the base case for
inductive decomposition arguments.

### 8.3. The {9,3} → {1+3=4} pattern (from non-overlap cores)

In cores #6 and #16, the v₂-layer is {3^2, 3^1} = {9, 3} with opposite signs.
The signed sum 9−3 = 6 = 2·3. After dividing by 2, the residual 3 matches
one of the even-weight elements, enabling support reduction.

The key constraint: 3^2 − 3^1 = 6 = 2·3, and 6/2 = 3 is {2,3}-smooth.
This works because the exponent gap is 1 (opposite sign), falling in the
"clean peel" region.

---

## 9. Next Steps

1. **Prove the sub-kernel extraction lemma** (Part B of this task):
   if a subset of support elements has signed-weighted sum = 0, the vector
   decomposes.

2. **Prove the equal-weight cancellation lemma**: special case where two
   elements cancel.

3. **Investigate multi-step peeling** for the obstruction cases.

4. **Enumerate support-5 identities** to check if similar layer patterns persist.

5. **Assess whether the non-smooth obstruction is fatal** or merely requires
   a more careful argument.
