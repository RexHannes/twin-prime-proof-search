# ArbitraryQAttempt Report — Outcome (B)

## Pre-flight result

```text
Target theorem `ReciprocalAtomGapConjecture` was not found.
Here are the closest related declarations I found:
```

### Closest related declarations

A full search of every `.lean` file under `RequestProject/` for the string
`ReciprocalAtomGapConjecture` (case-sensitive and case-insensitive variants,
as well as substrings `AtomGap`, `atomGap`, `atom_gap`, `Atom.*Gap`,
`Gap.*Atom`) returned **zero matches**.

The project contains no declaration with that name or any plausible variant.

The closest conjectural declarations in the project are:

---

#### 1. `dominantShortEnergy_conjecture` (DominantShortEnergy.lean, line 79)

**Exact Lean type:**

```lean
theorem dominantShortEnergy_conjecture
    (y : ℕ) (δ : ℚ) (hδ : 0 < δ) :
    ∃ C : ℕ, ∃ c : ℚ, 0 < c ∧
    ∀ k : ℕ, ∀ q : Fin k → ℕ,
      (∀ i, q i ≠ 0) →
      allSmooth k q y →
      totalWeightedEnergy k q ≥ δ →
      shortWeightedEnergy k q C ≥ c
```

Status: `sorry` (deliberate conjecture, not proved).

---

#### 2. `shortestVector_conjecture` (DominantShortEnergy.lean, line 101)

**Exact Lean type:**

```lean
theorem shortestVector_conjecture
    (y : ℕ) (δ : ℚ) (hδ : 0 < δ) :
    ∃ C : ℕ,
    ∀ k : ℕ, ∀ q : Fin k → ℕ,
      (∀ i, q i ≠ 0) →
      allSmooth k q y →
      totalWeightedEnergy k q ≥ δ →
      ∃ s, s ≤ C ∧ 0 < energyAtSupport k q s
```

Status: `sorry` (deliberate conjecture, not proved).

---

#### 3. `ReciprocalIdentity` (Defs.lean, line 35)

```lean
structure ReciprocalIdentity (Q : Finset ℕ+) where
  A : Finset ℕ+
  B : Finset ℕ+
  hA : A ⊆ Q
  hB : B ⊆ Q
  hAB : Disjoint A B
  hAne : A.Nonempty
  hBne : B.Nonempty
  hsum : recipSum A = recipSum B
```

Status: definition, fully elaborated.

---

#### 4. Other sorry-bearing declarations

| File | Declaration | Status |
|------|------------|--------|
| `EnergyDominanceY3.lean` | `energyDominance_y3` | `sorry` (y=3 restricted conjecture) |
| `EnergyDominanceY3.lean` | `shortestVector_y3` | `sorry` (y=3 shortest-vector variant) |
| `Support4.lean` | `smooth23_four_term_sunit_finite` | `sorry` (finiteness of S-unit solutions) |
| `Support4.lean` | `support4_completeness_of_smooth23` | `sorry` (support-4 completeness) |

---

## Why outcome (A) is not possible

Per the pre-flight requirements (§0):

> If no such declaration exists, do not create a new conjecture with that name
> and do not guess the intended statement. Instead, switch to outcome (B).

Since `ReciprocalAtomGapConjecture` does not exist in the project, creating a
new declaration with that name or attempting to prove a renamed/reformulated
version would violate requirements §0 and §1.

---

## Mandatory grep audit

```bash
grep -rE "sorry|admit|axiom|native_decide|exact\?|apply\?" RequestProject/ --include="*.lean"
```

**Results (all in pre-existing files, none in new files):**

| File | Occurrences |
|------|------------|
| `DominantShortEnergy.lean` | 2× `sorry` (deliberate conjectures) |
| `EnergyDominanceY3.lean` | 2× `sorry` (deliberate conjectures) |
| `Support4.lean` | 2× `sorry` (deliberate conjectures) |

No new files were created or modified (other than this report). No new
`sorry`, `admit`, `axiom`, `native_decide`, `exact?`, or `apply?`
occurrences were introduced.

---

## What concrete theorem would be needed next

If the intent was to prove an "atom gap" result — i.e., that any set `Q` with
positive entropy deficit contains a short reciprocal identity (an "atom") —
the closest existing formulation is `shortestVector_conjecture`. To make
progress toward proving it, the following concrete lemma would be needed:

**Needed lemma (not currently in the project):**

> For fixed `y` and `k`-element `y`-smooth denominator vector `q`, the number
> of primitive signed kernel vectors (Graver basis elements) with support
> exceeding `C` is at most `f(y, C)` for some function `f` that is
> subexponential in `C`. Combined with the `2^{-s}` weighting, this would
> force the energy to concentrate at bounded support.

This requires either:
- An effective Evertse-type bound on the number of S-unit equation solutions
  with bounded prime set, or
- A p-adic layer-peeling argument showing that primitive identity support is
  bounded by a function of `y` alone (contradicted by `UnboundedSupport.lean`
  for the unweighted case, but possibly salvageable for the energy-weighted
  formulation).

---

## Why existing Growth-Q results are insufficient

1. **`UnboundedSupport.lean`** disproves bounded primitive support: the family
   `B_t` gives primitive {2,3}-smooth identities of arbitrarily large support.
   So any "atom gap" conjecture must be stated in energy-weighted terms, not
   raw support terms.

2. **`Support4.lean`** classifies support-3 and catalogues support-4 cores,
   but completeness of the support-4 catalogue is itself conjectural (depends
   on S-unit finiteness).

3. **`EnergyDominanceY3.lean`** restricts to `y = 3` but is still `sorry`.

4. The bridge between the `Fin k → ℕ` indexed model (used in
   `EnergySpectrum*.lean`, `CollisionProbability.lean`) and the `Finset ℕ+`
   model (used in `Defs.lean`, `Elementary.lean`) has not been formalized.
   Any proof of a `Finset ℕ+`-stated conjecture using the indexed results
   would first require this bridge lemma.
