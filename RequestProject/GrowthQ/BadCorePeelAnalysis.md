# Bad Core Peel Analysis: The 7 Non-Smooth Support-4 Cores

**Date:** 2026-06-08

---

## 1. The 7 Bad Cores

From the Layer Pattern Survey, 7 of 25 non-degenerate support-4 cores produce
non-{2,3}-smooth intermediates under naive v₂-peeling. These are exactly the
cores where the odd-weight pair's exponent gap exceeds the "clean peel" threshold.

| # | Core (a+b=c+d) | Odd-weight pair | Gap (α−β) | Sign | Peel formula |
|---|----------------|-----------------|-----------|------|-------------|
| 19 | 81+1=64+18 | {81,1} = {3⁴,3⁰} | 4 | same (+,+) | (3⁴+1)/2¹ = 82/2 = **41** |
| 20 | 96+1=81+16 | {1,81} = {3⁰,3⁴} | 4 | opp (+,−) | (3⁴−1)/2⁴ = 80/16 = **5** |
| 21 | 128+1=81+48 | {1,81} = {3⁰,3⁴} | 4 | opp (+,−) | (3⁴−1)/2⁴ = 80/16 = **5** |
| 22 | 144+1=81+64 | {1,81} = {3⁰,3⁴} | 4 | opp (+,−) | (3⁴−1)/2⁴ = 80/16 = **5** |
| 23 | 256+3=243+16 | {3,243} = {3¹,3⁵} | 4 | opp (+,−) | (3⁵−3¹)/2⁴ = 240/16 = **15** = 3·5 |
| 24 | 512+1=432+81 | {1,81} = {3⁰,3⁴} | 4 | opp (+,−) | (3⁴−1)/2⁴ = 80/16 = **5** |
| 25 | 512+1=486+27 | {1,27} = {3⁰,3³} | 3 | opp (+,−) | (3³−1)/2¹ = 26/2 = **13** |

**New primes introduced**: {5, 13, 41}

**Root cause**: The non-smooth cofactor arises from `(3^n ± 1)/2^{v₂(3^n±1)}`:
- n=3, minus: (27−1)/2 = 13 (prime)
- n=4, minus: (81−1)/16 = 5 (prime)
- n=4, plus: (81+1)/2 = 41 (prime)
- n=4, minus, scaled by 3: (243−3)/16 = 15 = 3·5

---

## 2. Core-by-Core Peeled Intermediates

### Core #19: (81, 1, 64, 18) — 81 + 1 = 64 + 18

**v₂-peel:**
- Odd-weight pair: {81, 1}, signs (+, +), sum = 82
- v₂(82) = v₂(2·41) = 1
- Merged: 82/2 = **41** (prime)
- Residual: {41, 64/2, 18/2} = {41, 32, 9}, signs (+, −, −)
- Check: 41 − 32 − 9 = 0 ✓
- Factorization: 41 is **prime** (not {2,3}-smooth)

**v₃-peel (complementary):**
- Coprime-to-3 pair: {1, 64}, signs (+, −), sum = −63
- v₃(−63) = v₃(3²·7) = 2
- Merged: −63/9 = **−7** (prime)
- Residual: {81/9, 7, 18/9} = {9, 7, 2}, signs (+, −, −)
- Check: 9 − 7 − 2 = 0 ✓
- Factorization: 7 is **prime** (not {2,3}-smooth)

**Both peels fail to stay smooth.**

### Core #20: (96, 1, 81, 16) — 96 + 1 = 81 + 16

**v₂-peel:**
- Odd: {1, 81}, signs (+, −), sum = 1 − 81 = −80
- v₂(80) = 4
- Merged: −80/16 = **−5**
- Residual: {96/16, 5, 16/16} = {6, 5, 1}, signs (+, −, −)
- Check: 6 − 5 − 1 = 0 ✓
- Factorization: 5 is prime

**v₃-peel:**
- Coprime-to-3: {1, 16}, signs (+, −), sum = −15
- v₃(15) = 1
- Merged: −15/3 = **−5**
- Residual: {96/3, 5, 81/3} = {32, 5, 27}, signs (+, −, −)
- Check: 32 − 5 − 27 = 0 ✓
- Factorization: 5 is prime

**Both peels produce 5. Same cofactor from both directions.**

### Core #21: (128, 1, 81, 48) — 128 + 1 = 81 + 48

**v₂-peel:**
- Odd: {1, 81}, signs (+, −), sum = −80
- v₂(80) = 4, merged = −5
- Residual: {128/16, 5, 48/16} = {8, 5, 3}, signs (+, −, −)
- Check: 8 − 5 − 3 = 0 ✓

**v₃-peel:**
- Coprime-to-3: {128, 1}, signs (+, +), sum = 129
- v₃(129) = v₃(3·43) = 1
- Merged: 129/3 = **43**
- Residual: {43, 81/3, 48/3} = {43, 27, 16}, signs (+, −, −)
- Check: 43 − 27 − 16 = 0 ✓

**v₂-peel gives 5; v₃-peel gives 43.**

### Core #22: (144, 1, 81, 64) — 144 + 1 = 81 + 64

**v₂-peel:**
- Odd: {1, 81}, signs (+, −), sum = −80
- v₂(80) = 4, merged = −5
- Residual: {144/16, 5, 64/16} = {9, 5, 4}, signs (+, −, −)
- Check: 9 − 5 − 4 = 0 ✓

**v₃-peel:**
- Coprime-to-3: {1, 64}, signs (+, −), sum = −63
- v₃(63) = v₃(3²·7) = 2
- Merged: −63/9 = **−7**
- Residual: {144/9, 7, 81/9} = {16, 7, 9}, signs (+, −, −)
- Check: 16 − 7 − 9 = 0 ✓

**v₂-peel gives 5; v₃-peel gives 7.**

### Core #23: (256, 3, 243, 16) — 256 + 3 = 243 + 16

**v₂-peel:**
- Odd: {3, 243}, signs (+, −), sum = 3 − 243 = −240
- v₂(240) = 4, merged = −240/16 = **−15 = −3·5**
- Residual: {256/16, 15, 16/16} = {16, 15, 1}, signs (+, −, −)
- Check: 16 − 15 − 1 = 0 ✓

**v₃-peel:**
- Coprime-to-3: {256, 16}, signs (+, −), sum = 240
- v₃(240) = v₃(2⁴·3·5) = 1
- Merged: 240/3 = **80 = 2⁴·5**
- Residual: {80, 3/3, 243/3} = {80, 1, 81}, signs (+, +, −)
- Check: 80 + 1 − 81 = 0 ✓

**Both peels produce factor 5. v₂-peel gives 15=3·5; v₃-peel gives 80=2⁴·5.**

### Core #24: (512, 1, 432, 81) — 512 + 1 = 432 + 81

**v₂-peel:**
- Odd: {1, 81}, signs (+, −), sum = −80
- v₂(80) = 4, merged = −5
- Residual: {512/16, 5, 432/16} = {32, 5, 27}, signs (+, −, −)
- Check: 32 − 5 − 27 = 0 ✓

**v₃-peel:**
- Coprime-to-3: {512, 1}, signs (+, +), sum = 513
- v₃(513) = v₃(3³·19) = 3
- Merged: 513/27 = **19**
- Residual: {19, 432/27, 81/27} = {19, 16, 3}, signs (+, −, −)
- Check: 19 − 16 − 3 = 0 ✓

**v₂-peel gives 5; v₃-peel gives 19.**

### Core #25: (512, 1, 486, 27) — 512 + 1 = 486 + 27

**v₂-peel:**
- Odd: {1, 27}, signs (+, −), sum = 1 − 27 = −26
- v₂(26) = 1, merged = −26/2 = **−13**
- Residual: {512/2, 13, 486/2} = {256, 13, 243}, signs (+, −, −)
- Check: 256 − 13 − 243 = 0 ✓

**v₃-peel:**
- Coprime-to-3: {512, 1}, signs (+, +), sum = 513
- v₃(513) = 3, merged = 513/27 = **19**
- Residual: {19, 486/27, 27/27} = {19, 18, 1}, signs (+, −, −)
- Check: 19 − 18 − 1 = 0 ✓

**v₂-peel gives 13; v₃-peel gives 19.**

---

## 3. New Primes Summary

### Table 3.1: Complete cofactor inventory

| Core | v₂-peel cofactor | v₃-peel cofactor | Common prime? |
|------|-----------------|-----------------|---------------|
| #19 | **41** | **7** | No |
| #20 | **5** | **5** | Yes (5) |
| #21 | **5** | **43** | No |
| #22 | **5** | **7** | No |
| #23 | **5** (via 15=3·5) | **5** (via 80=2⁴·5) | Yes (5) |
| #24 | **5** | **19** | No |
| #25 | **13** | **19** | No |

**Complete set of new primes**: C = {5, 7, 13, 19, 41, 43}

**By core exponent gap**:
- Gap 3 (one core, #25): produces 13 (v₂) or 19 (v₃)
- Gap 4 (six cores, #19–#24): produces 5, 41, 7, 43, 19

**Algebraic origin**: The cofactors are the odd parts of 3^n ± 1 and 3^n ± 3^m:
- (3³ − 1)/2 = 13
- (3⁴ − 1)/2⁴ = 5
- (3⁴ + 1)/2 = 41
- (3³ − 1)·3 + ... → 19 = (3³·19 = 513 = 2⁹ + 1)
- 2⁶ − 3⁴ = 64 − 81... → 7 = (3²·7 = 63 = 2⁶ − 1)
- 3·43 = 129 = 2⁷ + 1 → 43

More precisely, these cofactors come from **Zsygmondy/lifting-the-exponent**
phenomena in the expressions 2^a ± 3^b:
- 2⁶ − 1 = 63 = 3²·7 → 7
- 2⁶ + 1 = 65 = 5·13 → 5, 13 (from different factorings)
- 2⁷ + 1 = 129 = 3·43 → 43
- 2⁹ + 1 = 513 = 3³·19 → 19
- 3⁴ + 1 = 82 = 2·41 → 41
- 3⁴ − 1 = 80 = 2⁴·5 → 5

---

## 4. Second-Peel Analysis: Does a Second Peel Return to Smooth?

### 4.1 Second v₂-peel on each bad residual

For each core, we take the v₂-peel residual (a 3-element equation involving
one non-smooth element M and two smooth elements r₁, r₂) and apply a second
v₂-peel.

| Core | First v₂-peel residual | Second v₂-peel |
|------|----------------------|----------------|
| #19 | 41 − 32 − 9 = 0 | Odd: {41,9}, sum = 41−9 = 32 = 2⁵. Merged = 1. Even: 32/32 = 1. **1−1=0** ✓ Smooth! |
| #20 | 6 − 5 − 1 = 0 | Odd: {5,1}, sum = −5−1 = −6, v₂=1. Merged = −3. Even: 6/2 = 3. **3−3=0** ✓ Smooth! |
| #21 | 8 − 5 − 3 = 0 | Odd: {5,3}, sum = −5−3 = −8 = −2³. Merged = −1. Even: 8/8 = 1. **1−1=0** ✓ Smooth! |
| #22 | 9 − 5 − 4 = 0 | Odd: {9,5}, sum = 9−5 = 4 = 2². Merged = 1. Even: 4/4 = 1. **1−1=0** ✓ Smooth! |
| #23 | 16 − 15 − 1 = 0 | Odd: {15,1}, sum = −15−1 = −16 = −2⁴. Merged = −1. Even: 16/16 = 1. **1−1=0** ✓ Smooth! |
| #24 | 32 − 5 − 27 = 0 | Odd: {5,27}, sum = −5−27 = −32 = −2⁵. Merged = −1. Even: 32/32 = 1. **1−1=0** ✓ Smooth! |
| #25 | 256 − 13 − 243 = 0 | Odd: {13,243}, sum = −13−243 = −256 = −2⁸. Merged = −1. Even: 256/256 = 1. **1−1=0** ✓ Smooth! |

**Result: ALL 7 bad cores return to {2,3}-smooth after a second v₂-peel.**

### 4.2 Second v₃-peel on each bad residual

| Core | First v₃-peel residual | Second v₃-peel |
|------|----------------------|----------------|
| #19 | 9 − 7 − 2 = 0 | Coprime-to-3: {7,2}, sum = −7−2 = −9 = −3². Merged = −1. Even: 9/9 = 1. **1−1=0** ✓ |
| #20 | 32 − 5 − 27 = 0 | Coprime-to-3: {32,5}, sum = 32−5 = 27 = 3³. Merged = 1. Even: 27/27 = 1. **1−1=0** ✓ |
| #21 | 43 − 27 − 16 = 0 | Coprime-to-3: {43,16}, sum = 43−16 = 27 = 3³. Merged = 1. Even: 27/27 = 1. **1−1=0** ✓ |
| #22 | 16 − 7 − 9 = 0 | Coprime-to-3: {16,7}, sum = 16−7 = 9 = 3². Merged = 1. Even: 9/9 = 1. **1−1=0** ✓ |
| #23 | 80 + 1 − 81 = 0 | Coprime-to-3: {80,1}, sum = 80+1 = 81 = 3⁴. Merged = 1. Even: 81/81 = 1. **1−1=0** ✓ |
| #24 | 19 − 16 − 3 = 0 | Coprime-to-3: {19,16}, sum = 19−16 = 3. Merged = 1. Even: 3/3 = 1. **1−1=0** ✓ |
| #25 | 19 − 18 − 1 = 0 | Coprime-to-3: {19,1}, sum = 19−1 = 18 = 2·3². v₃=2, merged = 2. Even: 18/9 = 2. **2−2=0** ✓ |

**Second v₃-peel also always returns to smooth.**

### 4.3 Why this is algebraically trivial

**Theorem (Three-term peel trivialization)**:

For ANY 3-element equation z₁w₁ + z₂w₂ + z₃w₃ = 0 (with zᵢ ∈ {±1} and
wᵢ > 0), a single v₂-peel on the two odd-weight elements produces a
2-element equation whose terms are automatically {2,3}-smooth if the
un-merged element w₃ is {2,3}-smooth.

*Proof*: The peel merges the odd pair into one term, leaving a 2-element
equation. In a 2-element equation z'₁w'₁ + z'₂w'₂ = 0, we must have
w'₁ = w'₂ and z'₁ = −z'₂. The value w'₂ = w₃/2^k, which is {2,3}-smooth
if w₃ is. So w'₁ = w'₂ is also {2,3}-smooth. □

**Consequence**: The second peel is trivially smooth, but **it is always
trivial** (reduces to a 2-element identity). This gives no useful
information about the original equation beyond confirming consistency.

---

## 5. Non-Trivial Complementary Peel Tests

Since second peels trivialize, we test **cross-peeling**: v₂-peel first,
then v₃-peel on the 3-element residual (or vice versa).

### 5.1 v₂ then v₃

This is equivalent to second-peeling by v₃. The merged element from the
v₂-peel has a specific v₃-valuation. Let's check:

| Core | v₂-residual | v₃ of non-smooth element | v₃-peel of residual |
|------|------------|-------------------------|---------------------|
| #19 | {41,32,9} | v₃(41)=0, v₃(9)=2 | Coprime-to-3: {41,32}. Sum=41−32=9=3². /9 → {1,1}. Trivial. |
| #20 | {6,5,1} | v₃(5)=0, v₃(1)=0 | Coprime-to-3: {5,1}. Sum=−5−1=−6. v₃=1, /3 → {−2,2}. Trivial. |
| #21 | {8,5,3} | v₃(5)=0, v₃(3)=1 | Coprime-to-3: {8,5}. Sum=8−5=3. v₃=1, /3 → {1,−1}. Trivial. |
| #22 | {9,5,4} | v₃(5)=0, v₃(4)=0 | Coprime-to-3: {5,4}. Sum=−5−4=−9=−3². /9 → {−1,1}. Trivial. |
| #23 | {16,15,1} | v₃(15)=1, v₃(1)=0 | Coprime-to-3: {16,1}. Sum=16−1=15. v₃=1, /3 → {5,−5}. Trivial BUT 5 persists! |
| #24 | {32,5,27} | v₃(5)=0, v₃(27)=3 | Coprime-to-3: {32,5}. Sum=32−5=27=3³. /27 → {1,−1}. Trivial. |
| #25 | {256,13,243} | v₃(13)=0, v₃(243)=5 | Coprime-to-3: {256,13}. Sum=256−13=243=3⁵. /243 → {1,−1}. Trivial. |

Cross-peeling produces the same triviality. Core #23 is interesting: the
v₃ cross-peel of the v₂-residual gives {5, 5} — the cofactor 5 PERSISTS
even in the trivial final equation.

### 5.2 Recombination attempts

Can any subset of 2 elements from different cores combine to form a {2,3}-smooth identity?

This doesn't apply within a single core analysis. Within a core, all subsets
have been checked (primitivity).

---

## 6. Multi-Step Peeling Lemma

### 6.1 Statement (provable)

**Lemma (Double v₂-peel for support-4)**:
Let z₁w₁ + z₂w₂ + z₃w₃ + z₄w₄ = 0 be a support-4 kernel equation with
exactly two odd-weight elements (say w₁, w₂ odd). Let S = z₁w₁ + z₂w₂
and let m = v₂(S). Then:

1. The first v₂-peel produces the 3-element equation:
   (S/2^m) + z₃(w₃/2^m) + z₄(w₄/2^m) = 0
   where S/2^m may be non-{2,3}-smooth.

2. The second v₂-peel produces a 2-element equation:
   (z₁w₁ + z₂w₂ + z_odd·w_odd')/(2^{m+m'}) = −z_even·(w_even'/2^{m+m'})
   where both sides are automatically {2,3}-smooth IF w₃, w₄ are {2,3}-smooth.

3. Combining: S/2^m = ±(w₃/2^m) or ±(w₄/2^m) (whichever is the surviving even element).

**This means**: The non-smooth cofactor in the first peel is always equal
(up to sign) to one of the even-weight elements divided by 2^m. Specifically:
- If w₃ is the "surviving" even element in the second peel:
  S/2^m = −z₃ · w₃/2^m
- This gives: z₁w₁ + z₂w₂ = −z₃ · w₃, a KNOWN relation.

Wait — this is NOT new information. It's just saying that in a 3-term
equation a + b + c = 0, we have a + b = −c. The "multi-step peel" is
just unpacking the 4-term equation via two successive reductions.

### 6.2 What IS genuinely informative

The useful information from the peel analysis is:

**For the bounded-cofactor framework**: When peeling a support-n kernel vector
(n ≥ 5), the first v₂-peel reduces to support n−1, but may introduce a
non-smooth element. The non-smooth element is a *specific* number of the
form (3^α ± 3^β)/2^k, which has its odd part determined by α−β.

For the broader proof strategy, we need to know: can this non-smooth element
be handled in subsequent steps? For support-4, the answer is trivially yes
(the residual is support-3, which collapses). For support-5+, the question is
genuinely open.

---

## 7. Bounded-Cofactor Peeling Framework

Since multi-step peeling trivializes for support-4, and since the "obstruction"
is that a single peel doesn't stay smooth, we propose the following framework.

### 7.1 Definition: C-smooth peeling

For a finite set of primes C, call a number **{2,3,C}-smooth** if all its
prime factors are in {2, 3} ∪ C.

A **C-smooth v₂-peel** of a kernel equation is a v₂-peel that produces
a residual where all weights are {2,3,C}-smooth.

### 7.2 The cofactor set for support-4

For all support-4 {2,3}-smooth kernel vectors, the v₂-peel produces weights
that are {2,3,C₂}-smooth where:

**C₂(v₂-peel) = {5, 13, 41}**

These come from the odd parts of (3^n − 1)/2^{v₂(3^n−1)} for n = 3, 4:
- n=3: (27−1)/2 = 13
- n=4: (81−1)/16 = 5
- and (3^4 + 1)/2 = 41

For v₃-peel: **C₃(v₃-peel) = {5, 7, 19, 43}**

### 7.3 Why the cofactor set is bounded for fixed support

For support-4, the odd-weight pair is {3^α, 3^β} with α, β ≤ B (the maximal
v₃-exponent). But for coprime cores, α and β are determined by the core, and
there are finitely many cores (by Evertse's theorem on S-unit equations).

**Key point**: The cofactor set C is finite not because of any deep theorem,
but because the set of coprime cores is finite. For each core, the cofactor
is a computable constant. So C is just the union of finitely many computable
constants.

### 7.4 Obstruction for support-5+

For support-5 kernel vectors, a v₂-peel gives support-4, but the resulting
4-element equation may involve {2,3,C}-smooth weights (not pure {2,3}-smooth).
The support-4 analysis does NOT apply to {2,3,C}-smooth equations.

This is the **genuine obstruction**: the peeling framework accumulates
cofactors, and we cannot bound the support of {2,3,C}-smooth kernel vectors
using only the {2,3}-smooth classification.

### 7.5 What would resolve the obstruction

**Option A**: Prove that for support-4 {2,3,C}-smooth vectors (where C is
finite), the set of coprime cores is also finite, and the peeling cofactors
from this enlarged class are still in C. This would give a self-contained
inductive framework.

**Option B**: Prove that the peeling strategy never needs more than k steps
(for some bounded k) regardless of the intermediate smoothness, by using
a different descent argument (e.g., bounding the LCM or the sum a+b+c+d).

**Option C**: Abandon peeling as the primary tool and use Graver-basis or
integer-programming arguments instead. The finite alphabet {2,3} guarantees
that the Graver basis of the associated lattice is finite, which gives
bounded support directly — but computing the Graver basis explicitly is
the challenge.

---

## 8. Precise Obstruction Report

### 8.1 What works

- **Single v₂-peel** reduces support by 1, reduces v₂-range, and always terminates.
- **Double v₂-peel** always trivializes support-3 residuals (and returns to smooth).
- The cofactor set for support-4 cores is finite and computable: C = {5, 7, 13, 19, 41, 43}.
- Every bad core eventually reaches a smooth trivial identity after 2 peels.

### 8.2 What fails

- **Single v₂-peel does NOT stay {2,3}-smooth** for 7 of 25 support-4 cores.
- The clean-peel condition (exponent gap ≤ 2 for opposite sign, ≤ 1 for same sign)
  is necessary and sufficient for single-step smoothness.
- **No peeling strategy** (v₂, v₃, or cross-peel) avoids non-smooth intermediates
  for these 7 cores. The obstruction is intrinsic to the core's exponent structure.

### 8.3 What remains open

- Whether the bounded-cofactor framework can be made self-closing (Option A above).
- Whether support-5 cores introduce new cofactors beyond C.
- Whether a Graver-basis computation for the {2,3}-smooth lattice would be
  more effective than the peeling approach.

---

## 9. Proposed Lean Lemma: `double_peel_smooth`

The following is the cleanest provable lemma from this analysis:

**Statement**: For three nonzero integers a, b, c with a + b + c = 0, if
exactly one of {a, b, c} is even, say c, then:
1. a + b = −c (obvious from a + b + c = 0)
2. a + b is even (sum of two odds)
3. |a + b| = |c|
4. If c is {2,3}-smooth, then |a + b| / 2^{v₂(a+b)} divides |c| / 2^{v₂(c)}
   and is {2,3}-smooth.

This captures the algebraic fact that the second peel inherits smoothness
from the un-merged element.

See `DoublePeelSmooth.lean` for the formalization.
