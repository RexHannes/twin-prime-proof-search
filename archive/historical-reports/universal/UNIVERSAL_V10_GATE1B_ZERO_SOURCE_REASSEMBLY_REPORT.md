# UNIVERSAL V10 — GATE 1B ZERO / SOURCE / REASSEMBLY COMPILER

Append-only run.  Six new modules, no existing file modified.

---

## A. FILES CREATED

```
RequestProject/NANC/Gate1B/V10CanonicalZeroMode.lean
RequestProject/NANC/Gate1B/V10HistoricalResidual.lean
RequestProject/NANC/Gate1B/V10PacketReassembly.lean
RequestProject/NANC/Gate1B/V10Counterguards.lean
RequestProject/NANC/Gate1B/V10FullTypeIICompiler.lean
RequestProject/NANC/Gate1B/V10Status.lean
UNIVERSAL_V10_GATE1B_ZERO_SOURCE_REASSEMBLY_REPORT.md   (this report)
```

## B. OLD FILES MODIFIED

**NONE.**  (`LEDGER.md` received a new appended block only; no previous block,
module or proof was altered.  `ARISTOTLE_SUMMARY.md` untouched.)

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]` occurs in any new module.

## C. THEOREMS KERNEL-CHECKED (exact names, namespace `TwinPrimeProject.Gate1BV10`)

**Canonical zero mode (reproved from Mathlib orthogonality — nothing postulated).**

```
sum_echar                                   -- ∑_a e_q(ax) = q·1_{x=0}, from AddChar.sum_mulShift
stdCharSystem                               -- inhabits Gate1B.SafeAlgebra.AdditiveCharacterSystem q
card_units_ne_zero
unit_indicator_baseline_std                 -- 1_unit/φ(q) = 1/q + (1/(qφ(q)))∑_{a≠0} c_q(-a)e_q(an)
fourierCoeff_zero
fourier_inversion
sum_ite_isUnit
canonical_discrepancy_has_zero_additive_mean
canonical_discrepancy_eq_nonzero_frequencies
zero_mean_fails_for_arbitrary_expected_term -- test theorem (arbitrary E breaks it)
```

**Historical / canonical residual (stated for the project's own switched objects).**

```
discr_hist_eq_can_add_gap                   -- C_q − E(q) = (C_q − M_q) + (M_q − E(q))
weightedDiscrSum_hist_eq_can_sub_residual   -- S_hist = S_can − R_E
switchedOperator_eq_weightedDiscrSum
switchedOperator_hist_eq_can_sub_residual   -- same, for Gate01Switch.switchedOperator with λ₃
weightedResidual_eq_zero_of_agree
canonicalComparison_residual_vanishes
switchedOperator_hist_eq_can_of_realisation
```

**E-indeterminacy counterguards (finite perturbation identities).**

```
perturbedExpected_self, perturbedExpected_of_ne
weightedResidual_perturbation               -- R_E(E') − R_E(E) = T·λ(q₀)
switchedOperator_perturbation               -- S_hist(E') = S_hist(E) − T·λ₃(U,V;q₀)
historical_residual_not_determined_by_nonzero_packet
residual_changes_concretely                 -- unconditional finite instance
zero_mean_fails_for_arbitrary_comparison
```

**Packet census and reassembly compiler.**

```
hpp_disjoint_repeated, hpp_disjoint_generic, repeated_disjoint_generic
census_union, census_union'                 -- HPP ∪ REP ∪ GEN = divisor-pair source set
freq_disjoint, freq_union                   -- zero / nonzero additive frequency
unit_disjoint, unit_union                   -- unit / nonunit
fullNine_census, fullNine_census_index      -- reuses Gate1B.SafeExtensions.fullNine_anova
norm_sum_le_of_packet_budget
norm_rawSource_le_of_packet_budget
packet_budget_needs_leaf_bounds
empty_packet_family_certifies_nothing
nonzero_source_has_no_empty_decomposition
packet_compiler_not_self_certifying
```

No same-q / shared-g / cross-coprime q-pair face was introduced: those are not
literal finite partitions in the existing bank.

**Conditional compilers and guards.**

```
Gate1BClosureInputs.rawSource_eq_sum_leafValue
Gate1BClosureInputs.leaf_bound
gate1B_closed_of_exact_inputs               -- ⟶ TwinPrimeProject.Gate1BDet2.Gate1BClosed
gate1BClosed_not_automatic
empty_source_forces_zero
FMReassemblyCertificate.sum_source_eq_sum_packet
fullTypeIIBound_of_reassemblyCertificate    -- ⟶ TwinPrimeProject.Gate1BDet2.FullTypeIIBound
compiler_uses_existing_fullTypeII
fullTypeII_not_automatic
certificate_dataType_nonempty               -- finite toy inhabitant of the DATA TYPE only
gate1BClosed_does_not_give_fullTypeII
```

## D. #PRINT AXIOMS OUTPUT

`RequestProject/NANC/Gate1B/V10Status.lean` runs `#print axioms` on all **52**
declarations listed in C.  Every single one reports exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

**No user axiom anywhere.**

## E. SOURCE INTERFACES LEFT UNINHABITED

```
TwinPrimeProject.Gate1BV10.Gate1BClosureInputs
    · highPrimeLeaf   (HIGHPRIME-MSWITCH)
    · sameQLeaf       (SAMEQ)
    · crossModLeaf    (CROSSMOD)
    · H9Leaf          (H9)
    · zeroFork        (E = canonical  ∨  residual bound)
    · S1NormalizationPin, S2DeltaScalarPin
TwinPrimeProject.Gate1BV10.CanonicalComparisonRealisation
TwinPrimeProject.Gate1BV10.FMReassemblyCertificate   (for the real programme;
    only a finite toy instance irrelevant to the analytic problem is built)
TwinPrimeProject.Gate1BDet2.Gate1BClosed
TwinPrimeProject.Gate1BDet2.FullTypeIIBound
TwinPrimeProject.Gate1BDet2.TwinPrimes
```

Nothing in this run inhabits any of them.

## F. FIRST FORMAL BLOCKER

```
def FullFMTypeII_OneSixth : ...        -- ABSENT from the entire repository
```

A repository-wide search finds no `FullFMTypeII_OneSixth`, and likewise no
`FMTypeIIExactAtScale`, `Gate1AOutput`, `Gate1BOutput` or
`Gate1ABReassemblyCertificate` (the string occurs only inside a prose report).
The nearest **existing** target predicate is

```
TwinPrimeProject.Gate1BDet2.FullTypeIIBound (typeIISum X delta : ℝ) : Prop :=
  |typeIISum| ≤ X ^ (1 - delta)
```

The conditional Type-II compiler is therefore stated against that existing
predicate and is explicitly labelled **not** the Ford–Maynard one-sixth
statement.  No easier replacement for `FullFMTypeII_OneSixth` was created, and
no theorem concludes it.

## G. BUILD

```
baseline lake build : PASS   (8539 jobs, 0 errors, before any edit)
final    lake build : PASS   (8545 jobs, 0 errors)
sorry               : NONE
user axioms         : NONE
```

## H. HOSTILE TESTS (all kernel-checked)

1. changing `E` at one `q` changes `R_E` — `weightedResidual_perturbation`,
   `residual_changes_concretely`;
2. zero-mode cancellation fails for an arbitrary comparison term —
   `zero_mean_fails_for_arbitrary_expected_term`,
   `zero_mean_fails_for_arbitrary_comparison`;
3. the packet compiler proves nothing without leaf bounds —
   `packet_budget_needs_leaf_bounds`, `packet_compiler_not_self_certifying`,
   `gate1BClosed_not_automatic`;
4. Type II is not derivable without the certificate — `fullTypeII_not_automatic`,
   `gate1BClosed_does_not_give_fullTypeII`;
5. an empty/vacuous packet family certifies nothing —
   `empty_packet_family_certifies_nothing`,
   `nonzero_source_has_no_empty_decomposition`, `empty_source_forces_zero`;
6. the compiler targets the actual existing predicate —
   `compiler_uses_existing_fullTypeII` (`Iff.rfl` against the banked definition).

Non-circularity: `V10Status.lean` prints the fields of `Gate1BClosureInputs`,
`FMReassemblyCertificate` and `CanonicalComparisonRealisation`; none of them has a
field whose type is the target proposition, and `certificate_dataType_nonempty`
exhibits a toy inhabitant of the certificate data type in a setting where the
Type-II problem is irrelevant.  This says nothing about the real analytic
certificate.

## FINAL VERDICT

```
V10_PARTIAL_KERNEL_CHECK_FIRST_INTERFACE_OPEN
```

Reason: every finite/algebraic and conditional-compiler claim in the brief is
kernel-checked, but the Full-FM Type-II compiler cannot be stated against
`FullFMTypeII_OneSixth`, which does not exist in the project (section F).
GATE1B remains OPEN; FULL TYPE II is not proved; twin primes are not declared.
