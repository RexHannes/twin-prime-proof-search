# Growth-Q Branch: Project Status

**Last updated:** 2026-06-08 (Session 14 — Peel Semantics Alignment)

---

## 0. Critical Semantics Issue (Session 14)

### Raw vs Canonical Peel Mismatch — RESOLVED

Session 13's `peelOnce` used **raw peel** semantics: merge the minimal v_p layer
into one term (divided by p^m), keep non-layer terms unchanged. The Kaggle CSV scans
use **canonical normalized peel** semantics:

1. Find minimal v_p layer.
2. Merge layer terms.
3. **Divide ALL terms by p^m** (not just the merged one).
4. **Divide by gcd** of all resulting terms.

These produce different residuals. The raw peel fails to produce valid equations
on the second step (demonstrated formally for 32+3+1=27+9).

**Resolution** (Session 14): `PeelSemantics.lean` defines:
- `peelOnceRaw` — Session 13's `peelOnce` (renamed)
- `peelOnceFullDiv` — divides all terms by p^m
- `peelOnceCanonical` — full-div + gcd normalization (matches Kaggle)

All three are defined, the worked example is reworked under all three, and the
mismatch is formally demonstrated:
- Raw second v₃-peel of 32+3+1=27+9 → **INVALID** (proved)
- Canonical first v₃-peel gives carrier [11], not [33] (proved)
- Canonical second v₃-peel gives [3,1,4], CC=0 (proved)

**All empirical CC data should be interpreted under canonical peel semantics.**

---

## 0b. Next Decisive Question

**Subcritical carrier genealogy under iterated canonical peeling.**

Session 13's conjecture "CC ≤ 1 forever" is **REFUTED** by the support-6 two-step
data: 1,899 out of 143,688 two-step states reach CC = 2 (~1.32%).

The corrected empirical observations:
- **One-step**: CC ≤ 1 always (likely near-tautological for raw peel; needs
  re-examination under canonical semantics).
- **Two-step**: CC ≤ 2 always observed; CC = 2 in ~1.3% of states; no CC > 2.
- The real phenomenon is **sparse/structured CC growth**, not single-carrier forever.

The next conjecture should be **"subcritical carrier genealogy"**: carrier complexity
grows slowly (sublinearly? logarithmically?) under iterated canonical peeling of
primitive {2,3}-smooth identities. Not "CC ≤ 1 forever."

---

## 1. Classification Status Summary

| Support level | Status | Detail |
|---------------|--------|--------|
| **Support-3** | ✅ **COMPLETE** | All support-3 identities among {2,3}-smooth integers classified into 3 families (Type I, II, III). Lean-verified with zero sorry. |
| **Support-4** | 📊 **Catalogue stable but incomplete** | 28 coprime cores (25 non-degenerate + 3 degenerate) found by exhaustive search up to 10⁶. Stable since max entry 512. All cores Lean-verified. Completeness depends on effective 4-term {2,3} S-unit classification (Evertse guarantees finiteness; explicit bound not computed). |
| **Support-5** | 📊 **Scan complete, carrier-complexity analyzed** | 1213 primitive cores found up to 10⁶. 400 produce outside-C₄ cofactors upon peeling. **All 400 have carrier complexity 1.** 395 distinct residual signatures. |
| **Support-6** | ✅ **ONE-STEP SCAN COMPLETE; TWO-STEP DATA IMPORTED** | Kaggle exact scan up to 10⁶: 35,994 primitive cores. One-step: 19,325 bad peels, all CC=1. **Two-step: 143,688 states scanned; CC=2 in 1,899 cases (~1.3%); no CC>2.** |
| **Support-7+** | ❌ **Not classified** | One-step scout data supportive but not decisive. |
| **Primitive support** | ✅ **Unbounded** (proved) | Infinite family of primitive identities with support 3+2t → ∞ via refinement identity. |

---

## 2. Layer-Peeling Status

### Peel semantics: ⚠️ ALIGNED (Session 14)

| Definition | File | Description |
|------------|------|-------------|
| `peelOnce` (raw) | `IteratedCarrierPeel.lean` | Merge layer, divide merge by p^m, leave non-layer unchanged. **Does NOT match Kaggle.** |
| `peelOnceRaw` | `PeelSemantics.lean` | Alias for `peelOnce`. |
| `peelOnceFullDiv` | `PeelSemantics.lean` | Divide ALL terms by p^m, then merge layer. |
| `peelOnceCanonical` | `PeelSemantics.lean` | Full-div + gcd normalization. **Matches Kaggle.** |

### p-adic extremal lemmas: ✅ PROVED

| Theorem | Status | File |
|---------|--------|------|
| `smooth23_two_adic_extremal` | ✅ | `Y3ShortestVectorAttempt.lean` |
| `smooth23_three_adic_extremal` | ✅ | `Y3ShortestVectorAttempt.lean` |
| `two_adic_extremal_unique` | ✅ | `Y3ShortestVectorAttempt.lean` |
| `three_adic_extremal_unique` | ✅ | `Y3ShortestVectorAttempt.lean` |
| `even_card_oddWtSupp` | ✅ | `Y3ShortestVectorAttempt.lean` |
| `two_le_card_oddWtSupp` | ✅ | `Y3ShortestVectorAttempt.lean` |
| `two_le_card_coprime3WtSupp` | ✅ | `Y3ShortestVectorAttempt.lean` |

### Layer-peel extraction lemmas: ✅ PROVED

| Theorem | Status | File |
|---------|--------|------|
| `sub_kernel_extraction` | ✅ | `LayerPeelExtraction.lean` |
| `complement_sub_kernel` | ✅ | `LayerPeelExtraction.lean` |
| `equal_weight_cancel` | ✅ | `LayerPeelExtraction.lean` |
| `v2_peel_even` | ✅ | `LayerPeelExtraction.lean` |
| `v2_peel_complement` | ✅ | `LayerPeelExtraction.lean` |
| `typeI_layer_extraction` | ✅ | `LayerPeelExtraction.lean` |
| `typeII_layer_extraction` | ✅ | `LayerPeelExtraction.lean` |
| `typeIII_layer_extraction` | ✅ | `LayerPeelExtraction.lean` |

### Double-peel smoothness lemmas: ✅ PROVED (Session 8)

| Theorem | Status | File |
|---------|--------|------|
| `three_term_neg` | ✅ | `DoublePeelSmooth.lean` |
| `three_term_determined` | ✅ | `DoublePeelSmooth.lean` |
| `odd_sum_even` | ✅ | `DoublePeelSmooth.lean` |
| `peel_merged_eq_neg` | ✅ | `DoublePeelSmooth.lean` |
| `support4_double_peel_trivial` | ✅ | `DoublePeelSmooth.lean` |
| `IsSmooth23` definitions & lemmas | ✅ | `DoublePeelSmooth.lean` |
| Bad core verifications (×14) | ✅ | `DoublePeelSmooth.lean` |

### Iterated peeling framework: ✅ BUILT (Session 13)

| Component | Status | File |
|-----------|--------|------|
| `PeelPrime` (two / three) | ✅ | `IteratedCarrierPeel.lean` |
| `PeelState` (residual equation) | ✅ | `IteratedCarrierPeel.lean` |
| `isAllowedSmoothBool` (decidable) | ✅ | `IteratedCarrierPeel.lean` |
| `peelOnce` (raw peel step) | ✅ | `IteratedCarrierPeel.lean` |
| `peelSequence` (iterated raw peeling) | ✅ | `IteratedCarrierPeel.lean` |
| `CarrierGenealogyNode` | ✅ | `IteratedCarrierPeel.lean` |
| `IteratedPeelCertificate` | ✅ | `IteratedCarrierPeel.lean` |
| `IteratedPeelBatch` | ✅ | `IteratedCarrierPeel.lean` |
| Worked example (32+3+1=27+9) | ✅ | `IteratedCarrierPeel.lean` |
| Synthetic CC≥2 examples | ✅ | `IteratedCarrierPeel.lean` |

### Peel semantics alignment: ✅ BUILT (Session 14)

| Component | Status | File |
|-----------|--------|------|
| `peelOnceRaw` (alias) | ✅ | `PeelSemantics.lean` |
| `peelOnceFullDiv` | ✅ | `PeelSemantics.lean` |
| `peelOnceCanonical` | ✅ | `PeelSemantics.lean` |
| `gcdNormalize` | ✅ | `PeelSemantics.lean` |
| `peelSequenceCanonical` | ✅ | `PeelSemantics.lean` |
| Raw vs canonical comparison | ✅ | `PeelSemantics.lean` |
| Raw 2nd peel invalidity proof | ✅ | `PeelSemantics.lean` |
| Support-6 two-step data import | ✅ | `PeelSemantics.lean` |

### Layer-peeling iteration: ⚠️ OBSTRUCTION IDENTIFIED

**C₄ self-closure is FALSE** (Session 9). The bounded-cofactor framework
must be replaced by the **carrier complexity** framework (Sessions 10–13).

**CC ≤ 1 forever is FALSE** (Session 14). Two-step canonical peeling reaches
CC = 2 in ~1.3% of support-6 cases. The next framework should target
**subcritical carrier genealogy** (slowly growing CC bounds).

---

## 3. Carrier Complexity Framework

### Session 10: Support-5 Analysis (Complete)

**Key Finding**: All 400 bad support-5 peels have **carrier complexity exactly 1** relative to
ALLOWED = {2,3,5,7,13,19,41,43}.

**File**: `CarrierComplexity.lean` — Zero sorry, standard axioms only.

### Session 12: Support-6 One-Step Empirical Results

**File**: `Support6CarrierCertificates.lean` — Zero sorry, standard axioms only.

**Key Finding**: All 19,325 bad support-6 one-step peels have **CC = 1**.
**Caveat**: One-step CC ≤ 1 may be near-tautological.

| Split type | Primitive cores | Peels | Bad peels | CC ≥ 2 |
|------------|----------------|-------|-----------|--------|
| 3-vs-3     | 13,538         | 27,076| 7,045     | 0      |
| 2-vs-4     | 17,990         | 35,980| 9,662     | 0      |
| 1-vs-5     | 4,466          | 8,932 | 2,618     | 0      |
| **Total**  | **35,994**     |**71,988**|**19,325**| **0** |

### Session 14: Support-6 Two-Step Results (NEW)

**File**: `PeelSemantics.lean` — Zero sorry, standard axioms only.

**Key Finding**: CC = 2 DOES occur after two canonical peels.

| CC value | Count | Fraction |
|----------|-------|----------|
| 0        | 93,471| 65.05%   |
| 1        | 48,318| 33.63%   |
| 2        | 1,899 | 1.32%    |
| > 2      | 0     | 0.00%    |
| **Total**| **143,688** | |

**Implications**:
- "CC ≤ 1 forever" is FALSE.
- The real phenomenon is sparse/structured CC growth.
- Next conjecture: subcritical carrier genealogy (CC grows slowly).

### Session 11: Generalized Framework

**File**: `CarrierComplexity6.lean` — Zero sorry, standard axioms only.

---

## 4. Cofactor Genealogy (Session 9)

### Key finding: C₄ self-closure is FALSE

Support-5 scan (MAX_VALUE = 10⁶) found 1213 primitive support-5 {2,3}-smooth cores,
400 of which produce cofactors outside C₄.

### Formal counterexample (Lean-verified, zero sorry)

The identity **32 + 3 + 1 = 27 + 9** (support-5, all entries {2,3}-smooth)
produces cofactor **11 ∉ C₄** via v₃-peel.

**File**: `CofactorGenealogy.lean` — 40+ proved theorems, zero sorry.

---

## 5. Bad Core Analysis (Session 8)

Full analysis in `GrowthQ/BadCorePeelAnalysis.md`.

---

## 6. Energy Dominance Status

| Theorem | Status | File |
|---------|--------|------|
| Dominant Short-Energy (general y) | 🔮 **OPEN** | `DominantShortEnergy.lean` |
| Shortest-Vector (general y) | 🔮 **OPEN** | `DominantShortEnergy.lean` |
| Energy dominance (y=3) | 🔮 **OPEN** | `EnergyDominanceY3.lean` |
| Shortest-vector (y=3) | 🔮 **OPEN** | `EnergyDominanceY3.lean` |
| Support-3 energy ≥ 1/8 | ✅ Proved | `EnergyDominanceY3.lean` |
| CP = Z(Q)/2^k | ✅ Proved | `CollisionProbability.lean` |
| #Collisions = 2^k + Σ E_s · 2^{k-s} | ✅ Proved | `EnergySpectrumExact.lean` |

---

## 7. Sorry Count

| File | Sorries | Type |
|------|---------|------|
| `Defs.lean` | 0 | ✅ |
| `Elementary.lean` | 0 | ✅ |
| `EnergySpectrum.lean` | 0 | ✅ |
| `EnergySpectrumExact.lean` | 0 | ✅ |
| `CollisionProbability.lean` | 0 | ✅ |
| `Smooth23.lean` | 0 | ✅ |
| `Smooth23Completeness.lean` | 0 | ✅ |
| `UnboundedSupport.lean` | 0 | ✅ |
| `InverseLemma.lean` | 0 | ✅ |
| `Y3ShortestVectorAttempt.lean` | 0 | ✅ |
| `LayerPeelExtraction.lean` | 0 | ✅ |
| `DoublePeelSmooth.lean` | 0 | ✅ |
| `CofactorGenealogy.lean` | 0 | ✅ |
| `CarrierComplexity.lean` | 0 | ✅ |
| `CarrierComplexity6.lean` | 0 | ✅ |
| `Support6CarrierCertificates.lean` | 0 | ✅ |
| `IteratedCarrierPeel.lean` | 0 | ✅ |
| **`PeelSemantics.lean`** | **0** | ✅ **NEW (Session 14)** |
| `DominantShortEnergy.lean` | 2 | 🔮 Deliberate conjectures |
| `Support4.lean` | 2 | 🔗 Completeness conjecture |
| `EnergyDominanceY3.lean` | 2 | 🔮 y=3 conjectures |

**Total sorries in proved theorems:** 0
**Total sorries in conjectures/reductions:** 6

---

## 8. All Proved Theorems (zero sorry, standard axioms)

### Core infrastructure (`Defs.lean`, `Elementary.lean`)
- `recipSum_empty`, `recipSum_singleton`, `recipSum_union_disjoint`
- `subsetSumImage_card_le`, `subsetSumImage_card_eq_iff`
- `exists_collision_of_not_injective`
- `recipSum_sdiff_eq_of_eq`, `sdiff_nonempty_of_ne_and_eq`
- `collision_to_identity`
- `collisionCount_eq_sum_sq`
- `clearing_denominators`

### Energy spectrum (`EnergySpectrum.lean`, `EnergySpectrumExact.lean`, `CollisionProbability.lean`)
- `collision_iff_kernel`
- `sign3Fiber_card`
- `collisionPairs_card_eq_sum`
- `collisionPairs_card_eq_diagonal_add_energy`
- `collisionProbability_eq`
- `one_le_deficitProxy`

### Support-3 completeness (`Smooth23.lean`, `Smooth23Completeness.lean`)
- `smooth23_typeI_identity`, `smooth23_typeII_identity`, `smooth23_typeIII_identity`
- `no_rectangle_identity`
- `no_pow3_add_one_eq_pow2_of_ge_two`, `no_pow2_add_one_eq_pow3_of_ge_four`
- `consecutive_smooth23_pairs`, `coprime_smooth23_sum_has_one`
- **`support3_completeness_of_smooth23`** (complete classification)

### Support-4 catalogue (`Support4.lean`)
- `support4_core1` through `support4_core25` (all verified)

### Unbounded primitive support (`UnboundedSupport.lean`)
- `refinement_identity`, `chainSum_eq_sixth`, `Bt_card_eq`
- `support_unbounded_with_identity`

### Kernel vector algebra (`InverseLemma.lean`)
- `kernel_add_disjoint`, `kernel_neg`

### p-adic Extremal Layer Lemmas (`Y3ShortestVectorAttempt.lean`)
- `two_adic_extremal_unique`, `even_card_oddWtSupp`, `two_le_card_oddWtSupp`
- `three_adic_extremal_unique`, `two_le_card_coprime3WtSupp`

### Layer-Peel Extraction (`LayerPeelExtraction.lean`)
- `sub_kernel_extraction`, `complement_sub_kernel`, `equal_weight_cancel`
- `v2_peel_even`, `v2_peel_complement`
- `typeI_layer_extraction`, `typeII_layer_extraction`, `typeIII_layer_extraction`

### Double-Peel Smoothness (`DoublePeelSmooth.lean`)
- `three_term_neg`, `three_term_determined`, `odd_sum_even`
- `peel_merged_eq_neg`, `support4_double_peel_trivial`, `double_peel_tautological`
- `IsSmooth23` and closure properties
- Bad core verifications (×14)

### Cofactor Genealogy (`CofactorGenealogy.lean`)
- `C4_not_self_closing`
- `useful_v3_peel_criterion`, `useful_v3_peel_criterion_minus`
- `outsideC4_all_prime`, `outsideC4_not_smooth`
- `F11_family_1` through `F11_family_7`
- `reciprocal_identity_11`

### Carrier Complexity — Support-5 (`CarrierComplexity.lean`)
- `AllowedPrimes`, `IsAllowedSmooth` and 20+ closure/verification lemmas
- `HasOutsideCarrier` and `hasOutsideCarrier_iff`
- 12 explicit outside-carrier proofs
- 6 carrier-complexity-1 examples
- `Carrier1Certificate` framework
- 8 representative valid certificates
- `carrier_determined_by_smooth`, `carrier1_support3_shape`, `carrier1_support4_shape`

### Generalized Carrier Complexity (`CarrierComplexity6.lean`)
- `ResidualEquation`, `CC0Certificate`, `CC2Certificate`, `ClassifiedResidual`
- `PeelOrigin`, `PeelResult`
- Bridge lemmas, synthetic CC2 examples, structural lemmas

### Support-6 Carrier Certificates (`Support6CarrierCertificates.lean`)
- `Support6SplitType`, `Support6ScanData`, aggregate theorems
- `support6_all_cc_at_most_1`
- 6 representative CC1 certificates

### Iterated Carrier Peeling (`IteratedCarrierPeel.lean`)
- `PeelPrime`, `PeelState`, `isAllowedSmoothBool`
- `peelOnce` (raw), `peelSequence`, `CarrierGenealogyNode`
- `IteratedPeelCertificate`, `IteratedPeelBatch`
- Worked example, synthetic CC≥2 examples, smoke tests

### **NEW: Peel Semantics Alignment (`PeelSemantics.lean`)**
- `peelOnceRaw`, `peelOnceFullDiv`, `peelOnceCanonical`
- `gcdNormalize`, `peelSequenceCanonical`, `peelSequenceFullDiv`
- Raw vs canonical comparison for 32+3+1=27+9 (all steps proved)
- `ex_raw_v3_v3_invalid` — raw second peel produces invalid equation (proved)
- `ex_canonical_v3_weights`, `ex_canonical_v3_cc` — canonical gives [1,9,3,11], CC=1
- `ex_canonical_v3_v3_weights`, `ex_canonical_v3_v3_cc` — second canonical gives [3,1,4], CC=0
- `TwoStepPeelDiagnostic` — structure for two-step scan data
- `support6TwoStepDiagnostic` — actual Kaggle data (35,994 cores, 143,688 states)
- `support6_twoStep_cc_leq1_false` — CC≤1 conjecture refuted (CC=2 occurs)
- `support6_twoStep_cc_leq2` — CC≤2 holds for all observed states
- Properties: `peelOnceCanonical_step`, `peelOnceCanonical_history`

---

## 9. Axiom Table

All proved theorems use only standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
Some computational certificates use `Lean.ofReduceBool` and `Lean.trustCompiler` via
`native_decide`. No `admit` or custom `axiom` anywhere.

---

## 10. Session History

| Session | Focus | Key Outcome |
|---------|-------|-------------|
| 1–7 | Core infrastructure, support-3/4/5 classification | Complete classification framework |
| 8 | Double-peel smoothness, bad core analysis | 7 bad cores analyzed, all second-peel smooth |
| 9 | Cofactor genealogy | C₄ self-closure FALSE; carrier complexity framework introduced |
| 10 | Support-5 carrier complexity | All 400 bad peels have CC=1 |
| 11 | Generalized carrier complexity | `CarrierComplexity6.lean` framework |
| 12 | Support-6 one-step scan | 19,325 bad peels, all CC=1 |
| 13 | Iterated peeling framework | `IteratedCarrierPeel.lean`; one-step CC≤1 may be near-tautological |
| **14** | **Peel semantics alignment** | **Raw vs canonical mismatch resolved; CC≤1 conjecture REFUTED by two-step data (CC=2 in ~1.3%); subcritical carrier genealogy proposed** |
