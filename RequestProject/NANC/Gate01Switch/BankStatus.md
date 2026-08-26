# Gate01Switch — switched high-P₃ finite bank

Incremental bank on top of the completed direct/root bank
(`RequestProject/NANC/Gate01Root/`).  Everything proved here is finite algebra.
Every genuine asymptotic/cancellation statement is an explicit interface and is
never inhabited.

Build: `lake build` — 8207 jobs, 0 errors.
Lean 4.28.0, mathlib v4.28.0 (commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365).

## Source discipline (SOURCE WINS)

Reused without modification:

* `TwinPrimeProject.lambda3` from `RequestProject/VaughanPacketAlgebra.lean`
  (`λ₃(U,V;q) = ∑_{d ∣ q, U<d, V<q/d} μ(d) Λ(q/d)`, codomain `ℝ`, Mathlib
  `moebius` / `vonMangoldt`).  **No second `lambda3` is defined.**
* `TwinPrimeProject.finiteDiscrepancy`, `shiftedPairing`, `VaughanP1/P2/P3`,
  `exactP1P2P3Decomposition` (same file).
* `TwinPrimeProject.r9BlockConvolutionDecomposition`
  (`RequestProject/R9ConvolutionAlgebra.lean`).

Recorded discrepancies between this specification and the archive:

1. **Residue.**  `finiteDiscrepancy` uses a fixed *natural* residue `a` and the
   test `n % q = a % q`.  No natural `a` satisfies `a ≡ -2 (mod q)` for all `q`
   simultaneously, so the switched discrepancy `discrMinusTwo` is defined by
   divisibility (`q ∣ n + 2`).  The exact per-modulus bridge is
   `finiteDiscrepancy_eq_discrMinusTwo`.
2. **`c₉ = κ_j(α_j * β_{9-j}) + E_j`.**  This identity does **not** occur in the
   archive; only the abstract ordered/distinct symmetrisation split does.  It is
   therefore never assumed: the shape is the predicate `R9CellConvolution` and
   is used only as a hypothesis.  Ledger: `R9_CELL_CONVOLUTION = SourceOpen`.
3. **`P₃ = Λ - P₁ + P₂`.**  This *is* supported by the source: it is
   `exactP1P2P3Decomposition` rearranged, proved as `vaughanSwitchIdentity`
   under the source hypothesis `ShiftedSupportAbove V c`.

## Modules

| file | content |
|---|---|
| `ResidueMinusTwo.lean` | `residueMinusTwoSet`, `discrMinusTwo`, `dvd_add_two_iff_zmod`, `negTwoResidue`, `dvd_add_two_iff_mod_eq`, boundary lemmas (`n=0`, `n=K`, `q=1`, `q>K+2`, nonemptiness) |
| `Lambda3.lean` | `lambda3_term_support`, `lambda3_eq_sum_over_ell`, `lambda3_primePow` (L3-PP), `lambda3_squarefree` (L3-SF), `moebius_div_prime_of_squarefree` |
| `SwitchedOperator.lean` | `switchedOperator` (SW0), `multiplierSet`, `sum_residueMinusTwo_eq_sum_multiplier` (RI), `switchedOperator_eq_multiplier` (SW1) |
| `DivisorPairs.lean` | `divisorPairs`, `sum_lambda3_mul_eq_divisorPairs` (generic opening), `pairSum`, `coeffWeight`, `expectedWeight`, `switchedOperator_eq_SW2` (SW2) |
| `PrimePowerStructure.lean` | `primePart`, `higherPrimePowerPart`, `pairSum_split_prime`, `higherPrimePower_support`, interface `PrimePowerSparseBound` |
| `RepeatedPrime.lean` | `repeated_prime_factorization`, `repeated_cofactor_unique`, `pairSum_split_repeated`, `pairSum_generic_eq_squarefree`, interface `RepeatedPrimeSparseBound` |
| `GenericSwitched.lean` | `switchedStratum`, `genericSwitchedOperator`, `mem_genericPart_divisorPairs`, `switchedOperator_three_way` |
| `ExponentGeometry.lean` | `SwitchedExponents`, `HardSwitchedExponentRegion`, `geometry₁`, `geometry₂`, `hardSwitchedExponentRegion_nonempty` |
| `FixedCellConvolution.lean` | `dconv`, `R9CellConvolution` (hypothesis shape only) |
| `Q5Equation.lean` | `q5_equation`, `q5Fibre`, `divisorsAntidiagonal_shift_eq_q5Fibre`, `genericSwitched_q5_expansion`, `genericSwitched_q5_support`, `genericSwitched_R9_split` |
| `WellFactorable.lean` | `SupportedUpTo`, `HasFactorization`, `factorization_vanishes_at`, `no_factorization_of_coarse_semiprime`, `coarse_of_semiprime` |
| `VaughanSwitchIdentity.lean` | `vaughanSwitchIdentity`, `finiteDiscrepancy_eq_discrMinusTwo` |
| `AnalyticInterfaces.lean` | interfaces + `switched_three_way_bound`, `q5_and_sparse_strata_imply_switched_fixedCell`, `switched_cells_and_coverage_imply_gate1B`, `direct_and_switched_bounds_imply_total` |
| `Ledger.lean` | decidable status table + consistency theorems |
| `AxiomAudit.lean` | `#print axioms` on representative theorems |

## Uninhabited interfaces

`PrimePowerSparseBound`, `RepeatedPrimeSparseBound`,
`Q5ShiftedProductAnalyticStatement`, `ActualSwitchedCoefficientDictionary`,
`ActualSwitchedMainTermDictionary`, `Gate0SwitchedCoverageStatement`,
`Gate1BSwitchedAnalyticStatement`,
`Gate0ExhaustiveOperatorCoverageStatement`.  The (C9) shape
`R9CellConvolution` is a predicate used only as a hypothesis; it is never
established for any source coefficient.

Interface style: following the existing bank (`Gate01Root`), each interface is
a **parametrized `Prop`-valued definition** rather than a `structure … where
bound : Prop`.  This is strictly stronger discipline: a structure with a free
`Prop` field can be inhabited trivially (`⟨True, trivial⟩`), whereas these
definite propositions can only be discharged by a real proof, and none is given.

None is inhabited anywhere.  The direct-bank interfaces
(`DivisorGrowthInterface`, `R4CBound`, `PPD`, `HitPStatement`, `HitStatement`,
`BPointStatement`, `BRowStatement`, `R4CAnalyticStatement`,
`PPDAnalyticStatement`, `Gate0CoverageStatement`, `WeightRealEven`,
`ArchFactorNegligible`, `RootMatrixMatchesSourceG`) are untouched.

## Overclaims explicitly rejected

* NO PROOF OF PRIME-POWER ASYMPTOTIC BOUND.
* NO PROOF OF REPEATED-P ASYMPTOTIC BOUND.
* NO PROOF THAT `lambda3` IS GLOBALLY NOT WELL-FACTORABLE (only a local,
  conditional obstruction at a single coarse modulus).
* NO PROOF OF Q5 ANALYTIC CANCELLATION.
* NO PROOF OF GATE 0 COVERAGE.
* NO PROOF OF GATE 1A.  NO PROOF OF GATE 1B.
* NO PROOF OF FULL TYPE II.  NO PROOF OF FCPT.
* NO PROOF OF TWIN PRIMES.  NO PROOF OF HARDY–LITTLEWOOD.

## Trust audit

`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `@[implemented_by]`: zero
occurrences in the new files.  `#print axioms` on representative theorems
reports only `propext`, `Classical.choice`, `Quot.sound`; the ledger
consistency theorems depend on no axioms at all.
