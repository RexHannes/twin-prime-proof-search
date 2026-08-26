# Gate 0–1 consolidation bank — status notes

Location: `RequestProject/NANC/Gate01Consolidation/`, exported by
`RequestProject/NANC/Gate01Consolidation/Main.lean` and imported from
`RequestProject/NANCBank.lean`.

Everything in this bank is finite / algebraic / combinatorial /
exponent-geometric.  No analytic estimate is proved, and no analytic or source
interface is inhabited anywhere.

## Modules

| Module | Content |
|---|---|
| `Centering.lean` | BANK A. Structural facts about the archive's `finiteDiscrepancy` (reused, not redefined): decomposition into progression mass minus expected, independence of the progression mass from `expected`, additivity, homogeneity, `q = 1`, and summation over all residues. |
| `NonzeroOrthogonality.lean` | BANK C. Additive character `ec q x = exp(2πi x/q)`, `ec_eq_one_iff`, `ec_congr`, complete orthogonality, **NZORTH** (`sum_ec_nonzero`, `sum_ec_nonzero_div`), and **RES_EQ** in integer (`dvd_add_two_inv_iff`) and `ZMod` (`zmod_add_two_inv_iff`) form. |
| `ESeparation.lean` | BANK B. `congrSum`, `fullSum`, `fourierHat`, `nonzeroFreqTerm`; **ESEP1** (`esep1`), **ESEP2** (`esep2`) and `nonzeroFreq_independent_of_expected`. |
| `CRTCentering.lean` | BANK D/E/T. `rho`, `indicator_mul_coprime`, **CRT-CENTER** (`rho_mul_coprime`); abstract source densities with the explicit premise `DensityMultiplicative` and **CRT-SRC** (`rhoSrc_mul_coprime`); the CRT frequency parametrisation `crtFreq`, its bijectivity, the rational frequency addition and the character identity `ec_crt_split`; the mode classification `CRTMode` / `crtMode`. |
| `ShiftInverse.lean` | BANK F/G. `coprime_shift`, **SHIFTINV** (`shift_inverse`, stated with explicit inverses), **SHIFT_PHASE** (`shift_phase`), and `shiftRepresentationMultiplicityBound`. |
| `PrimeCovariance.lean` | BANK H/I. `covKernel`, **KP** / **KP-OFF** / **KP-DIAG**, `centeredForm`, **P2MOM** (`sum_normSq_centeredForm`, `sum_normSq_centeredForm_norm`). |
| `ProductModeObstruction.lean` | BANK J. Product model, vanishing one-coordinate projections, **ANOVA** square mass `(1/d − 1/d²)(1/p − 1/p²)`, and the formal obstruction `zero_projections_not_imply_zero_mixed_mode`. |
| `DeterminantIdentity.lean` | BANK K. **DET** `r₀ v − n s = 2h` (fixed shift `2`, never averaged). |
| `DirectGaussReassembly.lean` | BANK L/M. **CHAR-COMB**, the unit case (`gaussReassembly_unit`, **GAUSS-PHYS** `gauss_phys`, **DIRECT-PHYS** `direct_phys`), the non-unit condition, and the classical stratification: solvability iff `g ∣ B`, the solution set is one class mod `c/g`, and a residue class mod `c/g` meets `{0,…,c−1}` in exactly `g` points. |
| `R9Regrouping.lean` | BANK N/O/P/Q. Slot masses and all binary splits; **REGROUP-PROD** / **REGROUP-CONG** and the exact exponents `4/9`, `5/9`; Convention A (`labelledBlockRegroupingInjective`) and Convention B (`constant_does_not_change_exponent`, on top of the project's existing `r9BlockConvolutionDecomposition`); **BLOCK-PARITY** (`blockImbalance_min`). |
| `ExponentThresholds.lean` | BANK R/S. `expQ = 13/18`, `expSqrtQ = 13/36`; `2/9 < 13/36` with deficit `5/36`; `4/9 − 13/36 = 1/12`, `5/9 − 13/36 = 7/36`; **WEIL-DEF** `13/36 − 5/18 = 1/12`. |
| `AnalyticInterfaces.lean` | The finite objects (`fourFiveDispersion`, `switchedMixedCovariance`) and the three uninhabited analytic interfaces, with `*_conditional` / `*_of_interfaces` implications only. |
| `SourceInterfaces.lean` | `ExpectedDensitySourceInterface` and `HighP3ExhaustiveRoutingInterface` (both uninhabited) plus two conditional consequences. |
| `OverclaimKillTests.lean` | Kills 1–5, each a proved statement (counterexample or explicit missing hypothesis). |
| `StatusLedger.lean` | `ProofStatus`, `Item`, `status`, and the consistency theorems `finiteItems_provedFinite`, `openItems_not_proved`, `gates_not_closed`. |

## Deliberate scope limits

* No formula for the source expectation `E(q)` is assumed: neither
  `totalMass / q` nor `totalMass / φ(q)`.
* `DensityMultiplicative` (DENS-MULT) is a hypothesis and is never instantiated;
  hence the source-density CRT identity is `provedConditional`.
* BANK Q is stated only for **pure nine-block binary partitions**; nothing is
  claimed about regroupings that involve `d`, `p`, `r` or other variables.
* BANK S proves only the exponent comparison; it does **not** assert that the
  true pointwise error is of size `√Q`.
* The ANOVA obstruction refutes only a *formal implication*; it is not a no-go
  theorem for analytic iterated dispersion.
* The determinant identity is banked with no analytic theorem attached; the
  closure route is `reformulationOnly`.
* Nothing here claims `T* ≪ X^{19/18−δ}`, the SW-centered theorem, `4|5`
  q-averaged dispersion, positive-measure switched closure, Gate 1B / 1A / 0
  closure, BC/Wright closure, Maynard 8.2 closure, an N1 uncentered theorem, an
  every-`K` resonance barrier, determinant pivot strict reduction, or a
  product-frequency large-sieve power gain.

## Naming deviation from the request

The suggested module names `01_Centering.lean`, … begin with digits, which Lean
4 module names cannot; the same modules are therefore named
`Centering.lean`, `NonzeroOrthogonality.lean`, `ESeparation.lean` (BANK B, split
out of the centering module), `CRTCentering.lean`, `ShiftInverse.lean`,
`PrimeCovariance.lean`, `ProductModeObstruction.lean`,
`DeterminantIdentity.lean`, `DirectGaussReassembly.lean`, `R9Regrouping.lean`,
`ExponentThresholds.lean`, `AnalyticInterfaces.lean`, `SourceInterfaces.lean`,
`OverclaimKillTests.lean`, `StatusLedger.lean`, `Main.lean`.

Interfaces are definite parametrised propositions rather than structures with a
free `Prop` field, following the convention already used in `Gate01Switch`: a
structure carrying an arbitrary `Prop` would be trivially inhabitable and would
record nothing.
