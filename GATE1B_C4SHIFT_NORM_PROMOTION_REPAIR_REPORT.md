# GATE 1B — C4SHIFT NORM-PROMOTION REPAIR REPORT

Append-only repair delta.  No historical module, status file or report was
edited or deleted.

New modules:

* `Gate1B/C4ShiftNormPromotionRepair.lean`;
* `Gate1B/CurrentStatusGate1BC4ShiftNormRepair.lean`;
* `Gate1B/AxiomAuditGate1BC4ShiftNormRepair.lean`.

---

## STILL FORMALLY VALID

Everything previously banked remains valid and untouched, in particular:

* the tuple-level `Γ♯` and its exact three-way partition
  (`C4ShiftAPFourier.GammaSharp`, `gamma_sharp_partition`) — note this already
  satisfies the requirement that `Γ♯` be defined by restricting the *underlying
  tuple sum*, never as `Γ · 1_{r ≠ 0}`;
* the AP-Fourier normal form and the reciprocal phase;
* the double-reciprocity normal form;
* the correct 2+2 four-product grouping;
* the linked-frequency identities;
* the `s`-Gram identity and the collision geometry;
* the exact `Ĥ` pushforward and the `Γ̃` factorisation.

## ANALYTIC PROMOTION RETRACTED

* `C4SHIFT-ONE-FOURPRODUCT-MINOR45` — **old research CLOSURE retracted**.
* `ONE-FOURPRODUCT-MINOR-NORM-PROMOTION45` — **NONCLOSING / INVALID
  IMPLICATION**.
* `DOUBLEMAJOR-AS-SOLE-RESIDUAL` — **RETRACTED**.

The **pointwise** bilinear estimate is explicitly **not** marked false:

* `FOURPRODUCT-POINTWISE-MINOR45` — RESEARCH PASS, **LOG-CORRECTED**: off the
  research major arcs the pointwise bound is `Y⁴ L^{−B+C+1}`, not
  `Y⁴ L^{−B+C}`.  It is research metadata; nothing analytic is formalised.

The Lean theorem `LedgerC4ShiftNormRepair.retraction_is_precise` records this
distinction formally.

## FORMALLY PROVED FIREWALLS

* `sq_abs_sum_le_card_mul_sum_sq`, `l1_le_l2_normalised` — the elementary
  `ℓ¹ ≤ ℓ²` comparison on a normalised finite index set.
* `pointwise_substitution_nonclosing` — explicit finite witness that
  substituting a pointwise bound `S ≥ R` into an `L¹` pairing strictly *worsens*
  the `L¹`-`L¹` estimate.  This is the exact formal shape of the invalid
  promotion.
* `ell_normalisation_no_saving`, `ell_normalisation_sum` —
  `ℓ^{-2} · #{(k₁,k₂) mod ℓ} = 1`, and summing over the physical `ℓ` family
  returns the number of `ℓ` values.  **`1/ℓ²` is never an automatic analytic
  saving.**
* `hKmap_bijective` — `(k₁,k₂) ↦ (k₁−k₂, k₁+k₂)` is a bijection mod `ℓ` **iff**
  `2` is invertible; `hKmap_not_injective_two` is the explicit `ℓ = 2`
  countermodel, so odd/even (2-adic) cells must be split.
* `apindex_hK_normalform` — the linked-frequency identities in `(h,K)`
  coordinates.
* `c4leaf_five` — `c₄,₅ = λ₁λ₂λ₃λ₄` (PURE MODEL LEAF);
  `c4leaf_first_defect` — for `j ≤ 4` the first defect coordinate `δ_{j+1}`
  factors out (source classification only; **no** Fourier smallness inferred).

## CURRENT OPEN CHILDREN

Parent: `C4SHIFT-QFOURIER-PUSHFORWARD45` — ANALYTIC OPEN (requirement unchanged:
`‖Ĥ_j‖_{L¹_θ ℓ²_v} ≤ naturalBound`; not replaced by double-major only, and not
replaced by scalar minor-energy only).

* A. `C4SHIFT-ONE-MINOR-PUSHED-ENERGY45` — ANALYTIC OPEN.
* B. `C4SHIFT-MAJOR-LEAFWISE-ROUTER45` — ANALYTIC / SOURCE OPEN.
  * `C4SHIFT-J5-MAJOR-LOCALMODEL45` — OPEN.
  * `C4SHIFT-DEFECT-SMALLMOD-CHAR45` — OPEN.
  * `C4SHIFT-DOUBLEMAJOR-FOURPRODUCT-APGRAM45` — OPEN, **may be reclassified by
    leafwise routing**, and **not** the sole residual.

These children are **not** claimed to be exhaustive: no exact partition of the
parent is formally established.

## RESEARCH CANDIDATES

* `MINOR-ARC-ENERGY45` — the minor-arc `L²` energy bound
  `∫_minor |F4_j|² ≤ Y⁴ L^{−A}` is **NOT banked as true**.  The socket
  `C4ShiftNormRepair.FourProductMinorEnergyInput` is UNINHABITED, with the
  recorded warning: plausible only for non-centred / model leaves, possibly
  **false** for centred-defect leaves, **leafwise audit required**.

## SUPERSEDED / FALSE / NOT FALSE

| label | status |
|---|---|
| `C4SHIFT-C4-FOURIER-FACTOR45` | FALSE (multiplicative Dirichlet convolution treated as additive convolution; Lean countermodel) |
| `CORRECT-2PLUS2-FOURPRODUCT45` | FORMALLY BANKED |
| `C4SHIFT-NO-DOUBLE-MAJOR45` | FALSE — explicit algebraic resonance |
| `FOURPRODUCT-POINTWISE-MINOR45` | RESEARCH PASS / LOG-CORRECTED — **not false** |
| `C4SHIFT-ONE-FOURPRODUCT-MINOR45` | OLD CLOSURE RETRACTED |
| `ONE-FOURPRODUCT-MINOR-NORM-PROMOTION45` | NONCLOSING / INVALID |
| `DOUBLEMAJOR-AS-SOLE-RESIDUAL` | RETRACTED |
| `C4SHIFT-QFOURIER-PUSHFORWARD45` | CURRENT PARENT ANALYTIC OPEN |

## BUILD

| target | result |
|---|---|
| `Gate1B.C4ShiftNormPromotionRepair` | success (8040 jobs) |
| `Gate1B.CurrentStatusGate1BC4ShiftNormRepair` | success |
| `Gate1B.AxiomAuditGate1BC4ShiftNormRepair` | success (8079 jobs) |

Global `lake build` still fails only on the pre-existing unrelated missing
module `RequestProject.FixedCertificateAlgebra`, deliberately not repaired.

## AXIOM AUDIT

All printed declarations depend only on `propext`, `Classical.choice`,
`Quot.sound` (several on none).  No `sorryAx`, no custom axiom, no proof escape.
Token scan for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`,
`implemented_by`: no occurrences outside prose.

## COMMITS / PUSH

Committed in two append-only steps (exact repair; status/audit/report) and
pushed to `origin`.

---

GATE1B OPEN.

CURRENT PARENT ANALYTIC FRONTIER:
C4SHIFT-QFOURIER-PUSHFORWARD45.

ONE-FOURPRODUCT-MINOR CLOSURE:
RETRACTED.

DOUBLE-MAJOR AS SOLE RESIDUAL:
RETRACTED.
