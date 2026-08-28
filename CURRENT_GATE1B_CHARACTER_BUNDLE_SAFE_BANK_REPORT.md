# CURRENT GATE1B — CENTERED CHARACTER BUNDLE / TWO-STAGE β SOURCE / ALL-k COMPILER
## Safe bank report

Append-only continuation of `TwinPrimeProject.CurrentProgramme`
(`RequestProject/CurrentProgramme/`).  No previous module was deleted, renamed,
weakened or rewritten.  No axiom was added, no analytic or source interface was
inhabited, and Gate 1B is **not** claimed closed.

---

## A. REGRESSION

* Branch `main`; the pre-existing modules
  `EndpointCentering.lean`, `EndpointTwoByTwoSplit.lean`,
  `EndpointCenteredRewriting.lean`, `EndpointMixedAddMult.lean`,
  `EndpointCollisionL2.lean`, `LichtmanT18Socket.lean`,
  `LichtmanT18Capacity.lean`, `EndpointMixedCompiler.lean`,
  `CurrentStatusMixed.lean`, `AxiomAuditMixed.lean` were located and reused; no
  prior declaration is duplicated.
* One pre-existing, unrelated breakage was found in the delivered sources:
  `RequestProject/TwinPrimeStatus.lean` refers to
  `ShiftedMobiusBank.ProofStatus` / `ShiftedMobiusBank.LedgerEntry`, which do
  not exist anywhere in the repository.  It is **left untouched** (repairing it
  would require inventing content).  `LargePrimeTail.lean` was repaired purely
  additively by prepending `import RequestProject.TwinPrimeDefinitions`.
* Every module of this bank builds individually:
  `lake build RequestProject.CurrentProgramme.<Module>`.

## B. FRONTIER RESET

`ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45` is recorded as
**SUPERSEDED AS CONTROLLING FRONTIER**.  The Lichtman theorem itself is **not**
marked false; only its role as the controlling route is retired
(`LedgerCharBundle` preserves the historical row).

New controlling frontier of this layer:
`ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45` — **OPEN_ANALYTIC**, uninhabited.

## C. CHARACTER ORTHOGONALITY

`EndpointCharacterCentering.lean`.  Mathlib's `DirichletCharacter`, `ZMod`
units, `Fintype.card_units` and `Nat.totient` are reused; no ad hoc character
theory was written.  Banked:

* `nonprincipalChars`, `mem_nonprincipalChars`,
* `principal_apply_unit`, `conj_apply_unit`, `totient_ne_zero_cast`,
* `sum_all_characters_unit_pair`, `sum_nonprincipal_unit_pair`,
* `centeredKernel_eq_nonprincipalCharacterSum` — the exact identity
  `Δ_ℓ(u₁,u₂) = 1_{u₁≡u₂} − 1_{(u₁u₂,ℓ)=1}/φ(ℓ) = φ(ℓ)⁻¹ Σ_{χ≠χ₀} χ(u₁)·conj χ(u₂)`,
  with **all unit hypotheses explicit**,
* `centeredKernel_principal_removed`, `centeredCharacterProjection_zeroPrincipal`,
* `centeredKernel_nonunit_counterexample` — the identity is *not* silently valid
  off the unit sector.

## D. CENTERED SQUARE BUNDLE

* `centeredEnergy_eq_nonprincipalCharacterSquareBundle`:
  `Σ_{u₁,u₂} c(u₁) conj c(u₂) Δ_ℓ(u₁,u₂) = φ(ℓ)⁻¹ Σ_{χ≠χ₀} |Σ_u c(u)χ(u)|²`,
  a pure finite identity, no estimate.
* `centeredEnergy_sum_over_moduli` sums it over `ℓ`.
* `characterParseval_unitSector` is the exact Parseval/orthogonality companion.

## E. 2|2 CHARACTER FACTORISATION

`EndpointTwoStageCharacterForm.lean`: `twoByTwo_character_twist`,
`dirichlet_pullback_mul`, `twoByTwo_dirichlet_twist` —
`Σ_u a₄(u)χ(u)Z(u,ℓ,k) = Σ_{m,r} α(m)γ(r)χ(m)χ(r)Z(mr,ℓ,k)` with
`a₄(u) = Σ_{mr=u} α(m)γ(r)`.  No estimates, no smoothness.

## F. β SOURCE SEARCH

The repository was searched for a literal `β_{D,P}(z) = Σ_{dp=z} μ(d)log p`
with physical dyadic ranges and line transform.  **It is absent.**  It was *not*
invented as an already-proved physical equality.

## G. β SOURCE ADAPTER

`EndpointBetaDPSource.lean`: concrete data `BetaDPLineSourceData`
(`D`, `P`, `beta`, `muWeight`, `primeWeight`, smooth line weight, congruence
kernel, quotient variable, clean-sector predicates — **no free `Prop` field**),
the opened line `betaDP_open_line`, the discrepancy kernel
`factorModKernel` with `K_{u,ℓ}(x) = 1_{xℓ≡2 (u)} − unitIndicator(x,u)/φ(u)`,
`factorModKernelZ_eq_centeredKernel`, `factorModKernel_principal_centered`,
and the **uninhabited** `BetaDPPhysicalSourceAdapter` with
`betaPhysicalAdapter_not_automatic` and `betaData_does_not_give_adapter`.

Status: `ENDPOINT-BETA-PHYSICAL-DICTIONARY45: SOURCE_OPEN / UNINHABITED`.

## H. TWO-STAGE NORMAL FORM

`CharTwistedFactorModTerm` carries exactly
`α(m) γ(r) χ(m) χ(r) muWeight(d) primeWeight(p) W(m,r,d,p,ℓ,k) K_{mr,ℓ}(dp)`;
then `SChar(ℓ,χ,k)` and
`TwoStageSquareBundle(k) = Σ_ℓ φ(ℓ)⁻¹ Σ_{χ≠χ₀} |SChar(ℓ,χ,k)|²`.
`twoStage_normalForm_of_adapter` proves the physical centered endpoint equals
the bundle **plus an explicit comparison/local remainder**, which
`comparisonRemainder_not_absorbed` forbids absorbing into the analytic square.
Status: `CONDITIONAL_SOURCE_COMPILER` (the β adapter is still open);
`twoStage_normalForm_not_automatic` records non-vacuity.

## I. NATURAL-SCALE NORM

`EndpointCharacterBundleNorm.lean`:
`interval_residue_fibre_card_le` (`#{u ∈ box : u ≡ a mod ℓ} ≤ 1 + ⌊len/ℓ⌋`,
exact, no informal `U/ℓ`), `characterParseval_real`,
`characterBundleEnergy_le_multiplicity`, and the rational exponent ledger
`expU = 4`, `expR = 5/2`, `expH = 5/2`, `expQ = 13/2` with
`naturalScale_UH_exponent` (`U²H²` has `Y`-exponent 13),
`naturalScale_split_exponent`, `naturalScale_routes_agree`.
Logs are never treated as real powers.
Status: `ENDPOINT-TWOSTAGE-NATURAL-SCALE-LEDGER45: PROVED_ALGEBRAIC / CAPACITY_ONLY`.

## J. SCALARISATION TAX

`scalarisation_cost`: from a cellwise scalar bound `|SChar(ℓ,χ,k)| ≤ B` the
bundle is at most the weighted cell count times `B²` — finite counting only, no
analytic theorem is claimed to supply `B`.  Exponent ledger:
`scalarizationEnergyTax_value` (`R`-exponent in `X` = `5/18`),
`scalarizationAmplitudeTax_value` (`√R` exponent = `5/36`), `taxes_pos`.
Status: `CAPACITY_ONLY`.  Pascadi Prop. 4.4 is **not** formalised as an axiom.

## K. HILBERT FIREWALL

`sharedCharacterProduct_not_singleLinearLift` with
`sharedCharacterProduct_firewall_nonvacuous`: an explicit finite data
distinction showing the coordinate vectors `m ↦ (χ(m))_χ` and `r ↦ (χ(r))_χ` do
not determine the coordinatewise product through one linear map on either
factor alone.  This is *not* stated as impossibility of every vector-valued
theorem.

## L. ANALYTIC SQUARE SOCKET

`EndpointCharacterSquareSocket.lean`:
`EndpointCharTwistedFactorModSquareInput` — the finite analogue of
`Σ_{ℓ∼R} φ(ℓ)⁻¹ Σ_{χ≠χ₀} |Σ_{m,r,d,p} α γ χ(m)χ(r) μ(d) log p · W · K_{mr,ℓ}(dp)|²
≤ desiredTarget`.  **Uninhabited.**  `EndpointBudgets` separates
`naturalBudget` from `requiredBudget` with a strict improvement requirement
(`natural_pos`, `saving_ratio_lt_one`, `no_trivial_budget`); no fake `log^{-A}`
asymptotics.  `charSquareInput_not_automatic`.

## M. SMALL-k COMPILER

`EndpointAllKCompiler.lean`: `SmallK(K0)`, `smallK_compiler`,
`smallK_compiler_of_inputs`, `smallK_cost_is_K0` — the summed budget is paid
with exactly `#SmallK(K0)`; the polylog cost is represented as a budget
assumption, never called harmless.

## N. HIGH-k SOCKET

`HighKFrequencyGainInput` (uninhabited) for dyadic bands, abstract conclusion
`bandContribution(K) ≤ naturalBandBudget / frequencyGain(K)`, no value of
`delta` claimed; `highKInput_not_automatic`.

## O. ALL-k CONDITIONAL COMPILER

`KPartition`, `high_sum_eq`, `allK_endpoint_compiler`: small-`k` input +
high-`k` gain input + exact partition/exhaustiveness ⇒ `RANKONE-ENDPOINT-ALLK45`.
`allKCompiler_not_unconditional` keeps the interface uninhabited absent both
antecedents.

## P. COMPARISON FIREWALL

`PURE5-COMPARISON-MAINTERM-PIN` stays `SOURCE_OPEN`;
`comparison_not_automatic` shows it is not inferable from centering.
`Pure5PacketInput` / `pure5Packet_projections` express the conditional
dependency without inventing physical source data.

## Q. DEFECT-ORDER LINK

`DefectPropagationInput`, `defectPropagation_not_automatic`,
`defect_chain_requires_five_inputs`: reusing the banked defect census
(`|J| = 5,4,3,2,1`, `no_blanket_monotonicity`), lower-defect closure is **not**
asserted; exactly what one propagation theorem must supply per defect order is
parameterised.

## R. NON-VACUITY

`betaPhysicalAdapter_not_automatic`, `charSquareInput_not_automatic`,
`highKInput_not_automatic`, `comparison_not_automatic`,
`allKCompiler_not_unconditional`, `twoStage_normalForm_not_automatic`,
`defectPropagation_not_automatic` — no compiler manufactures its own analytic
antecedent.

## S. BUILD / TRUST AUDIT

`AxiomAuditCharacterBundle.lean` runs `#print axioms` on 54 principal
declarations; every one depends only on a subset of
`propext, Classical.choice, Quot.sound`.  A repository grep finds no `sorry`,
`admit`, user `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]` in any module of this bank (only the audit docstrings
mention the words).

## T. FINAL LEDGER

`CurrentStatusCharacterBundle.lean` (`LedgerCharBundle`) carries the
machine-readable rows with all historical rows preserved, plus
`no_closed_rows`, `ledger_is_honest`, `gate1B_open`.

## U. FIRST SOURCE OPEN

The physical `β_{D,P} = μ_D ∗ Λ_P` line adapter
(`BetaDPPhysicalSourceAdapter`), still absent.

## V. FIRST ANALYTIC OPEN

`ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45`.

## W. NEXT UNIQUE ACTION

Supply the physical `β_{D,P}` line adapter, or reduce the character-twisted
factor-mod square further before any scalarisation is attempted.

---

```
GATE1B: OPEN.

FIRST SOURCE OPEN:
    physical beta_{D,P}=mu_D*Lambda_P adapter (absent).

FIRST ANALYTIC OPEN:
    ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45.

SMALL-k:
    OPEN.

HIGH-k:
    OPEN.

ALL-k:
    OPEN / CONDITIONAL COMPILER ONLY.

COMPARISON:
    SOURCE_OPEN.

QK56:
    OPEN.
```

No row is promoted to CLOSED; every antecedent listed above is literally
present in the repository as an uninhabited interface.
