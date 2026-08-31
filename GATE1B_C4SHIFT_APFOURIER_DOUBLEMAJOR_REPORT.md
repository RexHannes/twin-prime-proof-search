# GATE 1B — C4SHIFT AP-FOURIER / DOUBLE-MAJOR FRONTIER REPORT

Append-only delta on top of the C4Shift consolidation bank.  No historical
module was edited or deleted.

New modules:

* `Gate1B/C4ShiftAPFourierDoubleMajor.lean` — exact algebra and finite Fourier;
* `Gate1B/CurrentStatusGate1BC4ShiftAPFourier.lean` — append-only status layer;
* `Gate1B/AxiomAuditGate1BC4ShiftAPFourier.lean` — axiom audit.

---

## FORMALLY PROVED IN LEAN

**A. Tuple-level `Γ♯` and the exact partition.**
`rCoord` is a function of the *underlying tuple*, not of the post-summed `(w,g)`
fibre, so `Γ♯` is defined by filtering the tuple index set — never as
`Γ · 1_{r ≠ 0}`.  `gamma_sharp_partition` is the exact finite identity

`Γ = Γ_{r=0} + Γ_{r≠0, |g| ≤ thr} + Γ♯`.

`gamma_smallG_vanishes` is a *conditional* consequence of the UNINHABITED
`GammaSharpRangeInput`.

**B. AP-Fourier normal form.**
`ap_fourier_restriction` — restricting an `A`-sum to `A ≡ A₀ (mod ℓ)` equals the
average of `ℓ` shifted transforms.  `lineCoeff_ap_fourier` —

`C(ξ) = e(ξ A₀/ℓ) · (1/ℓ) ∑_{k mod ℓ} e_ℓ(−k A₀) F4((ξ−k)/ℓ)`,

with the physical support statement as an explicit hypothesis.
`ap_phase_reciprocal` — `e_ℓ(−k A₀) = e_ℓ(2 k (us)⁻¹)`.

**C. Double reciprocity normal form** (`C4SHIFT-DOUBLE-RECIPROCITY-NORMALFORM45`).
`exists_bul` (`b_{u,ℓ} = (ℓ y_{u,ℓ} − 2)/u` as an integer),
`sA0_eq_b_add_l_nu` (`s A₀ = b_{u,ℓ} + ℓ ν`) and `double_reciprocity_phase`:
all `A₀`- and `ν`-phases cancel, leaving exactly `e(−2θ/ℓ)`.

**D. Four-product source.**
`fourProduct_2plus2` (via `sum_mul_fibre`) — the **legal** 2+2 grouping
`F4(ω) = ∑_{X,Z} α(X) γ(Z) e(−ω X Z)` for the multiplicative pairing
`c₄(A) = ∑_{XZ=A} α(X) γ(Z)`.

**E. Linked frequencies.**  `linked_frequency_diff`:
`ω₁ − ω₂ = (s u θ − h)/ℓ` with `h = k₁ − k₂`; `linked_frequency_sum`:
`ω₁ + ω₂ = (s u θ − 2 s η − K)/ℓ` with `K = k₁ + k₂`.

**G. `s`-Gram identity (`g`-Plancherel).**  `gram_identity`:
`∑_{x,y} |Γ'(x,y)|² = ∑_{s₁,s₂} |⟨B_{s₁},B_{s₂}⟩|²`, exactly.  No Gram
contraction estimate is claimed.

**H. Collision geometry.**  `collision_coprime_factorisation`: `s₁A₁ = s₂A₂`
with `s₁ = d a`, `s₂ = d b`, `d ≠ 0`, `gcd(a,b) = 1` forces `A₁ = b C`,
`A₂ = a C`.

## REFUTED IN LEAN (countermodels)

* `C4SHIFT-C4-FOURIER-FACTOR45` — **FALSE**.  A multiplicative Dirichlet pairing
  was treated as an additive convolution.  `c4_additive_factorisation_false`
  gives the explicit finite witness `α = γ = 1` on `{1,2}`, `ω = 1/2`, where the
  bilinear form equals `2` and the product of transforms equals `0`.
* `C4SHIFT-NO-DOUBLE-MAJOR45` — **FALSE at the algebraic resonance level**.
  `double_major_resonance`: `η = a/s`, `u θ = (a+b)/s`, `k₁ = b`, `k₂ = −a`
  makes both linked frequencies vanish.  **Nothing is claimed about `m_top`**;
  in particular `m_top(b/s) ≠ 0` is *not* formalised.

## SOURCE-CONDITIONAL / UNINHABITED

* `C4ShiftAPFourier.GammaSharpRangeInput` — physical routing threshold; never
  constructed.
* All earlier sockets remain uninhabited (see the C4Shift consolidation report).

## RESEARCH-LEVEL STATUS ONLY

The double-major four-product AP-Gram sector,
`C4SHIFT-DOUBLEMAJOR-FOURPRODUCT-APGRAM45`, is ANALYTIC OPEN / UNINHABITED.  No
analytic estimate for it exists in this repository.

## TARGETED BUILD RESULTS

| target | result |
|---|---|
| `Gate1B.C4ShiftAPFourierDoubleMajor` | success |
| `Gate1B.CurrentStatusGate1BC4ShiftAPFourier` | success |
| `Gate1B.AxiomAuditGate1BC4ShiftAPFourier` | success (8077 jobs) |

## GLOBAL BUILD RESULT

Unchanged: `lake build` fails only on the pre-existing, unrelated missing module
`RequestProject.FixedCertificateAlgebra`, which was deliberately not repaired.

## AXIOM AUDIT

Every printed declaration depends only on `propext`, `Classical.choice`,
`Quot.sound` — several on none at all.  No `sorryAx`, no custom axiom.  Token
scan for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`,
`implemented_by`: no occurrences outside prose.

---

GATE1B OPEN.

FIRST EXACT RESEARCH RESIDUAL
(conditional on one-minor promotion audit):
C4SHIFT-DOUBLEMAJOR-FOURPRODUCT-APGRAM45.
