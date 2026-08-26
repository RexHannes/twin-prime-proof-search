# Twin Prime Gate 1B — source-native HFMV determinant bank: status ledger

Bank location: `RequestProject/NANC/HFMVGate1B/`
Wired into `RequestProject/NANCBank.lean` via `RequestProject.NANC.HFMVGate1B.Main`.

## Build and token audit

* `lake build` — PASSED, 8238 jobs, 0 errors, 0 warnings in the files of this bank.
* Lean 4.28.0, mathlib `v4.28.0` (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
* Token scan over `RequestProject/NANC/HFMVGate1B/*.lean`:
  * `sorry` — 0
  * `admit` — 0
  * `axiom` declarations — 0 (the only occurrences are `#print axioms` audit
    commands in `Main.lean` and the prose word in doc comments)
  * `@[implemented_by]` — 0
* `#print axioms` is run in `Main.lean` on every main finite theorem of the
  bank.  Reported dependencies are only `propext`, `Classical.choice`,
  `Quot.sound` (several theorems depend on no axioms at all).

## PROVED FINITE

| Item | Theorem(s) | File |
|---|---|---|
| Complementary-divisor equivalence `d p ∣ u v + 2 ↔ ∃ l, u v + 2 = d p l` | `dvd_iff_exists_ell`, `dvd_iff_exists_incidence`, `Incidence.dvd` | `HFMVComplementaryDivisor.lean` |
| Source-native incidence predicate and uniqueness of `l` | `Incidence`, `ell_unique`, `ell_unique_of_pos`, `ell_eq_div`, `existsUnique_ell` | `HFMVComplementaryDivisor.lean` |
| Positivity / dyadic range variants for `l` | `ell_pos`, `one_le_ell`, `ell_range`, `ell_le_of_one_le_modulus` | `HFMVComplementaryDivisor.lean` |
| Determinant identity `v₂ d₁p₁l₁ − v₁ d₂p₂l₂ = 2(v₂ − v₁)` (over `ℤ`) | `det_identity`, `det_identity_centered` | `HFMVDeterminant.lean` |
| Determinant converse with `u = (d₁p₁l₁ − 2)/v₁ = (d₂p₂l₂ − 2)/v₂` | `det_converse_abstract`, `det_converse`, `det_converse_pos` | `HFMVDeterminant.lean` |
| Diagonal identity `v₁ = v₂ → d₁p₁l₁ = d₂p₂l₂` and its converse for `u ≠ 0` | `diagonal_prod_eq`, `diagonal_prod_eq'`, `diagonal_v_eq` | `HFMVDiagonal.lean` |
| Exact finite tuple-diagonal decomposition (fibre squares) | `diagonalPairs_eq_prodPairs`, `diagonalPairs_fiber`, `diagonalPairs_card` | `HFMVDiagonal.lean` |
| Rational exponent ledger `4/9`, `5/9`, `13/18`; `UV/Q = X^{5/18}`, `Q²/V² = X^{1/3}` | `expU_add_expV`, `expUV_sub_expQ`, `two_expQ_sub_two_expV`, `rpow_UV_div_Q`, `rpow_Qsq_div_Vsq` | `HFMVExponentLedger.lean` |
| B1 determinant multiplicity one | `b1_multiplicity_one`, `b1_key_injOn` | `B1DeterminantEnergy.lean` |
| B1 abstract finite energy inequality with explicit constant `C = |P ×ˢ Hh|` | `b1Alpha_single`, `b1_energy` | `B1DeterminantEnergy.lean` |

Notes.

1. All determinant algebra is over `ℤ`; no `Nat` subtraction occurs anywhere.
2. `b1_multiplicity_one` needs only the bounds `|h₁|, |h₁'| ≤ H` together with
   `2H < p₁` and `p₁ ≠ p₂` prime; the `h₂`-coordinates are then forced.  The
   multiplicity factor in `b1_energy` is the visible constant
   `C = (b1Box P Hh).card` coming from Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`);
   it is written in the statement, not absorbed by automation.
3. The diagonal bound `diagonalPairs_card_le` is **conditional** on the
   explicitly supplied divisor-counting hypothesis `FiberDivisorBound T D`; it is
   the only upper bound for the diagonal in this bank.
   `diagonalPairs_card_eq_sq_of_constant_v` proves that without such an input the
   diagonal can be as large as `|T|²`, so no analytic negligibility is asserted.

## EXTERNAL ANALYTIC (declared, never inhabited)

| Interface | Definition |
|---|---|
| Möbius dyadic logarithmic saving | `MobiusDyadicLogSaving` |
| Divisor-counting asymptotics (dyadic) | `DivisorBoundDyadic` |
| Source expected-term / HFMV centering match | `SourceExpectedTermMatchesHFMVCentering` |
| Small proper gcd sectors | `SmallProperGCDBound` |
| Supplied diagonal bound | `DiagonalBound` |

All are in `HFMVAnalyticInterfaces.lean`.  Deterministic implications proved
there and nowhere else: `hfmv_bound_of_interfaces`
(`GSDVBound + DiagonalBound + SmallProperGCDBound + centering interface →
HFMVBound`), `diagonalBound_of_divisorBound`, `centering_of_mobius_saving`.
Guards: `gsdv_not_automatic` (an interface can fail, so it is not free),
`gsdv_satisfiable` (interfaces are not vacuously false).

## OPEN ANALYTIC

* `GSDVBound` — the generic off-diagonal GSDV estimate.  Never proved, never
  assumed outside explicit hypotheses.

## OPEN SOURCE

* The original switched expected-term / packet routing is **not supplied**; it
  appears only as `SourceExpectedTermMatchesHFMVCentering`.

## NOT PROVED

* Gate 1B (the proposition `Gate1BClosed` is deliberately **not stated**).
* Full Type II.
* Twin primes.
