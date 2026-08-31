# GATE 1B — ROW-LOCAL DICTIONARY SAFE BANK REPORT

Append-only consolidation (Gate 1B, Gate-1B row-local dictionary layer).

Guiding principle, enforced by types and by kernel-checked firewalls:

```
kernel theorem bank  !=  current research status.
```

---

## FILES ADDED

- `Gate1B/Gate1BLeaf4FormalLocalTree.lean` — unconditional Bézout-row and
  product-difference integer algebra; Dirichlet vs additive convolution
  firewall; noncommutative major-tree interface; formal Leaf-4 split and the
  `c44Loc` / `c45` owner firewall.
- `Gate1B/Gate1BLeaf4RowLocalStatus.lean` — new append-only research-status
  datatype `RowLocalStatus` (metadata only) and all current status constants.
- `Gate1B/Gate1BPhysicalRowLocalDictionaryInterface.lean` — the physical
  row-local dictionary as an interface (`E`, `Z_E`, `kappa_4` are data fields),
  the named source obligations, `PhysicalRowLocalDictionaryValid`, and the two
  purely logical conditional compilers.
- `Gate1B/CurrentStatusGate1BRowLocalDictionary.lean` — new append-only ledger
  layer on top of `LedgerPuncturedProductFourier.full`.
- `Gate1B/AxiomAuditGate1BRowLocalDictionary.lean` — `#print axioms` for all 79
  principal new declarations.
- `GATE1B_ROWLOCAL_DICTIONARY_SAFE_BANK_REPORT.md` — this report.

## FILES MODIFIED

- `Main.lean` — five appended imports plus a comment. Nothing reordered,
  nothing deleted.

No other file in the repository was edited, renamed, relocated or deleted. No
existing theorem was changed, weakened or overwritten.

---

## UNCONDITIONAL KERNEL THEOREMS (new in this delta)

Bézout-row normal form (integer algebra, `a_h = a0 + f*h`, `b_h = b0 + c*h`,
`f*b0 - c*a0 = N`):

- `bezoutRow_det_invariant` : `f*b_h - c*a_h = N`.
- `scaledBezoutRow_det_invariant` : with `A_h = d*a_h`, `B_h = d*b_h`,
  `f*B_h - c*A_h = d*N`.

Product-difference arithmetic (arithmetic kernel of
`HZERO-J4-ALPHA4-PRODUCTDIFF45`):

- `gate1B_leaf4_productDifference` : `u1*v1 = A_h`, `u2*v2 = B_h` imply
  `c*u1*v1 - f*u2*v2 = -(d*N)`.
- `gate1B_leaf4_productDifference_shift` : the literal `N = ell*r` form,
  `c*u1*v1 - f*u2*v2 = -(d*ell*r)`.

Dirichlet / additive convolution firewall:

- namespaces `DirichletConv` (`dmul`, `dmul_apply`, `dmul_assoc`, `dmul_comm`)
  and `AdditiveConv` (`aconv`, `aconv_apply`), kept type- and name-separate;
- `dirichlet_ne_additive_conv` — explicit countermodel: the two operations are
  not the same. **No universal inequality between them is claimed.**

Noncommutative major-tree interface:

- `MajorTreeInterface` with ordered slots `M1, M2, M3, M5`; `alphaComp`
  (`M1 ∘ M2`), `gammaLocComp` (`M3 ∘ M5`), `localComp`, `slots`,
  `slots_length`, `localComp_eq_alpha_comp_gammaLoc`;
- `Leaf4FormalLocalTree` (ordered local slots `M1, M2, M3, M5`);
- `majorTree_comp_not_commutative` — countermodel forbidding replacement of
  ordered composition by a scalar (commutative) product. The false identity
  `Fourier(alpha_4) = Fourier(lambda_1)*Fourier(lambda_2)` is **not**
  formalised anywhere.

Formal Leaf-4 split and owner identity (symbolic Dirichlet coefficients):

- `alpha4 = lambda_1 *_D lambda_2`, `gamma4 = lambda_3 *_D delta_5`,
  `rho5 = delta_5 - lambda_5`, `gamma4Loc = lambda_3 *_D lambda_5`,
  `gamma4Rem = lambda_3 *_D rho_5`;
- `gamma4_split` : `gamma_4 = gamma4Loc + gamma4Rem`;
- `c44Loc = lambda1 *_D lambda2 *_D lambda3 *_D lambda5`,
  `c45 = lambda1 *_D lambda2 *_D lambda3 *_D lambda4`;
- `c44Loc_eq_alpha4_dmul_gamma4Loc`, `c45_eq_alpha4_dmul` (associativity);
- `c44Loc_eq_c45_of_lambda4_eq_lambda5` — **conditional only**, requires the
  supplied source equality `lambda_4 = lambda_5`;
- `c44Loc_ne_c45` — countermodel: without extra source equalities the two
  coefficients differ.

Status-metadata firewalls (all `decide`-checked):

- `rowLocalStatus_never_closed`, `rowLocalStatus_analytic_not_kernelProved`,
  `analyticBanked_not_kernelProved`, `retracted_ne_kernelProved`,
  `productFourier_algebra_banked_mechanism_retracted`,
  `puncturedFrame_banked_jointGain_retracted`, `leaf4_does_not_close_gate1B`,
  `leaves123_open`, `hNe_lowerD_open`,
  `current_first_residual_is_rowLocal_dictionary`,
  `only_algebra_rows_kernelProved`, `residual_labels_distinct`.

Dictionary firewalls:

- `physicalRowLocalDictionaryValid_not_unconditional`,
  `dictionary_data_not_pinned`, `kappa4_not_pinned`,
  `leaf4_closure_requires_dictionary`, `leaf4_closure_not_unconditional`,
  `hZeroHighHigh_does_not_close_gate1B`, `hZeroHighHigh_requires_leaves123`,
  `smallQ_normalisations_are_source_pins`.

Ledger honesty invariants:

- `no_closed_rows`, `ledger_is_honest`, `gate1B_open`,
  `current_first_source_residual`, `old_c4shift_superseded`,
  `previous_layer_preserved`, `historical_research_rows_preserved`,
  `algebra_banked_while_mechanism_retracted`, `new_exact_rows_kernel_proved`,
  `analytic_bank_rows_not_kernel_proved`, `open_branches`,
  `leaf4_does_not_close_gate1B`, `source_pins_open`.

---

## REUSED PREVIOUS BANK

All previously banked Gate 1B declarations are imported and untouched, in
particular:

- punctured finite Fourier frame — `puncturedFourier_gram`,
  `puncturedFourier_posDef`, `puncturedFourier_minNorm_coeff_bound`,
  `puncturedFourier_minNorm_coeff_bound_div`, `puncturedFourier_surjective`,
  `puncturedFourier_fullRowRank`, `puncturedFourier_unitDilate_rank`;
- product-Fourier algebra — `productFourier_orthogonality`,
  `productFourier_gram`, `productFourier_norm_sq`;
- primitive determinant arithmetic — `doubleGcd_dvd_shift`,
  `primitiveDeterminant_factor`,
  `primitiveDeterminant_nonzero_of_shift_nonzero`, the same-X / same-Z
  exclusions, `determinant_phase_factorization`;
- Möbius / divisor identities — `coprime_indicator_mobius`,
  `double_coprime_indicator_mobius`, `prime_dvd_mul_router`;
- zero-mode firewall — `originalZero_preserved`, `cyclicZero_not_identified`,
  `cyclicZero_ne_originalZero`;
- conditional compiler — `conditional_net_compiler` (remains **conditional
  only**; its analytic antecedents are not kernel-proved and are not supplied).

The pre-existing status taxonomy `Status` / `LedgerEntry`
(`RequestProject.CurrentProgramme.StatusTypes`) is reused. The older
two-constructor `ResearchStatus` of the punctured/product-Fourier layer is left
untouched; the new, strictly larger `RowLocalStatus` is appended beside it
because the old one cannot express `analyticBanked`, `sourcePin`, `superseded`
or `retracted`.

---

## SUPERSEDED RESEARCH LABELS

Recorded as `supersededAsControllingFrontier` in the **new** layer only; the
historical rows and files are preserved unchanged:

- `C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45` as *current first residual* —
  historical only, **not false**;
- `HZeroPrimitiveDetNonzeroFull : candidateResearchClosed` — historical
  annotation, not current research truth;
- `HZeroHighHighAnalytic : candidateResearchClosed` — historical annotation;
  the current status of `h = 0` high-high is **conditional** on the physical
  local tree match.

`historical_research_rows_preserved` and `previous_layer_preserved` are the
kernel-checked statements that the old rows still exist, unchanged, in their own
module.

---

## RETRACTED ANALYTIC MECHANISMS

- product-Fourier closes `h = 0` — **retracted**
  (`productFourierClosureMechanismStatus := retracted`,
  ledger row `PRODUCT-FOURIER-CLOSURE-MECHANISM45`);
- joint determinant-character / punctured-frame Gram supplies the missing
  `M^(-1/2)` contraction — **retracted**
  (`jointFrameAnalyticGainStatus := retracted`, row `JOINT-FRAME-MSQRT-GAIN45`);
- arbitrary rank-two defect closure — not used anywhere in this delta;
- old `C4SHIFT` status as *current* first residual — superseded.

The corresponding **algebra remains banked**: no algebraic theorem was modified
because an analytic application failed
(`algebra_banked_while_mechanism_retracted`).

---

## LATEST ANALYTIC BANK (research status data, not Lean analytic theorems)

```
HZERO-J4-ALPHA4-PRODUCTDIFF45                    : PASS.
HZERO-J4-ALPHA4-NONCOMMUTATIVE-MAJORTREE45       : PASS.
HZERO-J4-ALPHA4-BEZOUTROW-NONRESONANT45          : CLOSED.
HZERO-J4-ALPHA4-BEZOUTROW-CENTREDGRAM45          : ANALYTICALLY CLOSED
                                                   AT FORMAL TREE LEVEL.
```

Literal identity banked as *arithmetic* in Lean:

```
c*u1*v1 - f*u2*v2 = -d*ell*r.
```

Interpretation banked as *metadata*: `alpha_4 = lambda_1 *_D lambda_2` must be
represented by ordered major dilation operators; the Fourier-product identity is
**not** formalised.

---

## CURRENT SOURCE PIN

```
ORIGINAL-E(q) / Z_E(q) PHYSICAL-ROWLOCAL-DICTIONARY45.
```

Exposed as `PhysicalRowLocalDictionary` (data: `E`, `ZE`, `kappa4`, and the
principal / non-principal / exceptional / non-unit conventions and projector
ownership) together with `RowLocalObligations` (the named obligations
`E_q_normalization_condition`, `ZE_q_normalization_condition`,
`q1_physical_match`, `q2_physical_match`, `oddPrime_local_match`,
`twoAdic_local_match`, `kappa4NormalizationHypothesis`) and the proposition
`PhysicalRowLocalDictionaryValid`, which is **not proved**.

`q = 1`: formal zero-mode present; centred-defect analytic coefficient
negligible in the current research bank; physical `E(1)/Z_E(1)` normalisation is
a **source pin**.
`q = 2`: formal alternating major packet present; physical `E(2)/Z_E(2)`
normalisation is a **source pin**.
No analytic asymptotics are formalised for either.

---

## CONDITIONAL COMPILERS

- `leaf4_closed_of_physical_dictionary` — from
  `PhysicalRowLocalDictionaryValid D O` together with the explicit
  `centredGram`, `nonresonant`, `productDifference`, `noncommutativeMajorTree`
  and `localTreeOwner` hypotheses, concludes the logical package
  `Leaf4ClosureConclusion D O H`. **No hypothesis is supplied anywhere.**
- `hZeroHighHigh_closed_of_local_dictionary` — from the five explicit leaf
  hypotheses (`leaf1 … leaf5Local`), concludes `HZeroHighHighConclusion L`.
  Dependency structure only; **no hypothesis is supplied**, and
  `hZeroHighHigh_does_not_close_gate1B` shows the package does not imply Gate 1B
  closure.
- `conditional_net_compiler` (previous bank) remains conditional only.

---

## AXIOM AUDIT

`Gate1B/AxiomAuditGate1BRowLocalDictionary.lean` runs `#print axioms` on all 79
principal new declarations. Result:

- every declaration depends on a subset of `{propext, Classical.choice,
  Quot.sound}`; many depend on none;
- **zero** `sorryAx`;
- no new custom `axiom`, no `unsafe`, no `opaque` proof shortcut, no
  `implemented_by`, no `native_decide`, no `sorry`/`admit` (token grep over all
  five new modules is clean);
- the two conditional interface theorems depend only on hypotheses supplied as
  explicit arguments.

---

## BUILD STATUS

```
NEW MODULE BUILD:
  Gate1B.Gate1BLeaf4FormalLocalTree                  PASS
  Gate1B.Gate1BLeaf4RowLocalStatus                   PASS
  Gate1B.Gate1BPhysicalRowLocalDictionaryInterface   PASS
  Gate1B.CurrentStatusGate1BRowLocalDictionary       PASS
  Gate1B.AxiomAuditGate1BRowLocalDictionary          PASS
  (0 errors, 0 warnings)

DEFAULT REPOSITORY BUILD:
  PRE-EXISTING FAILURE.
```

The default `lake build` fails at

```
error: no such file or directory (error code: 2)
  file: RequestProject/FixedCertificateAlgebra.lean
```

This is a historical missing-module / bad-import problem that predates this run;
it was **not** repaired here (append-only policy), no new module imports the
missing modules, and no new module appears in any build error.

---

## CURRENT RESEARCH LEDGER

PERMANENT KERNEL BANK:

```
punctured finite Fourier frame;
product-Fourier exact algebra;
primitive determinant arithmetic;
Möbius/gcd identities;
original-zero/cyclic-zero firewall;
(new) Bézout-row and product-difference integer algebra;
(new) formal Leaf-4 local tree and owner firewall;
(new) Dirichlet/additive convolution firewall.
```

RETRACTED ANALYTIC MECHANISMS:

```
product-Fourier closes h=0;
joint eta/k frame gives M^(-1/2);
arbitrary rank-two defect closure;
old C4SHIFT status as first current residual.
```

LATEST ANALYTIC BANK:

```
HZERO-J4-ALPHA4-PRODUCTDIFF45:                 PASS.
HZERO-J4-ALPHA4-NONCOMMUTATIVE-MAJORTREE45:    PASS.
HZERO-J4-ALPHA4-BEZOUTROW-NONRESONANT45:       CLOSED.
HZERO-J4-ALPHA4-BEZOUTROW-CENTREDGRAM45:       ANALYTICALLY CLOSED AT
                                               FORMAL TREE LEVEL.
```

CURRENT SOURCE PIN:

```
ORIGINAL-E(q)-/Z_E(q)-
PHYSICAL-ROWLOCAL-
DICTIONARY45.
```

LEAF 4:

```
ANALYTICALLY CLOSED
MODULO LOCAL SOURCE IDENTIFICATION.
```

Exact remaining Leaf-4 analytic saving: **NONE** — the obstruction is an exact
source-normalisation / dictionary identity, not a missing power/log saving. This
is **not** Gate 1B closure.

LEAVES 1–3:

```
OPEN / NOT PROMOTED.
```

LEAF 5:

```
PURE LOCAL MODEL;
BARE LEAF 5 IS NOT THE LEAF-4 OWNER.
```

h=0 HIGH-HIGH:

```
ANALYTICALLY CLOSED
MODULO PHYSICAL LOCAL TREE MATCH.
```

HNE:

```
NOT RUN.
```

LOWER-D:

```
OPEN.
```

GATE1B:

```
OPEN.
```

---

## HOSTILE FORMAL AUDIT

1. No old research status deleted — historical modules untouched; preservation
   is kernel-checked (`previous_layer_preserved`,
   `historical_research_rows_preserved`). PASS
2. No kernel theorem changed — `git status` shows only new files plus appended
   `Main.lean` imports. PASS
3. Product-Fourier algebra banked while its closure mechanism is separately
   retracted (`algebra_banked_while_mechanism_retracted`). PASS
4. Dirichlet and additive convolution never identified
   (`dirichlet_ne_additive_conv`). PASS
5. `c44Loc` not identified with bare `c45` (`c44Loc_ne_c45`; the equality exists
   only under the explicit hypothesis `lambda_4 = lambda_5`). PASS
6. `PhysicalRowLocalDictionaryValid` not proved; refutable for the explicit
   non-physical placeholder. PASS
7. `E(q)`, `Z_E(q)`, `kappa_4` are data fields, never assigned values
   (`dictionary_data_not_pinned`, `kappa4_not_pinned`). PASS
8. Leaf-4 status does not imply Gate 1B closure
   (`leaf4_does_not_close_gate1B`, `hZeroHighHigh_does_not_close_gate1B`). PASS
9. Leaves 1–3 remain open (`leaves123_open`, ledger rows `LEAF1/2/3`). PASS
10. HNE remains not run (`hNeStatus := openStatus`, row `HNE : NOT RUN`). PASS
11. Lower-D remains open (`lowerDStatus := openStatus`). PASS
12. Current residual is the physical row-local dictionary, not the superseded
    `C4SHIFT` label (`current_first_residual_is_rowLocal_dictionary`,
    `old_c4shift_superseded`). PASS

---

## STRICT FINAL OUTPUT

```
FILES ADDED:
  Gate1B/Gate1BLeaf4FormalLocalTree.lean
  Gate1B/Gate1BLeaf4RowLocalStatus.lean
  Gate1B/Gate1BPhysicalRowLocalDictionaryInterface.lean
  Gate1B/CurrentStatusGate1BRowLocalDictionary.lean
  Gate1B/AxiomAuditGate1BRowLocalDictionary.lean
  GATE1B_ROWLOCAL_DICTIONARY_SAFE_BANK_REPORT.md

FILES MODIFIED:
  Main.lean (five appended imports + comment only)

NEW UNCONDITIONAL THEOREMS:
  bezoutRow_det_invariant, scaledBezoutRow_det_invariant,
  gate1B_leaf4_productDifference, gate1B_leaf4_productDifference_shift,
  dirichlet_ne_additive_conv, majorTree_comp_not_commutative,
  gamma4_split, c44Loc_eq_alpha4_dmul_gamma4Loc, c45_eq_alpha4_dmul,
  c44Loc_ne_c45, plus the status/dictionary/ledger firewalls listed above.

REUSED KERNEL BANK:
  punctured Fourier frame; product-Fourier algebra; primitive determinant
  arithmetic; Möbius/gcd identities; zero-mode firewall; conditional compiler;
  Status/LedgerEntry taxonomy.

OLD STATUS LAYER:
  PRESERVED

SUPERSEDED LABELS:
  C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45 (as current first residual);
  HZeroPrimitiveDetNonzeroFull : candidateResearchClosed;
  HZeroHighHighAnalytic : candidateResearchClosed.

RETRACTED ANALYTIC MECHANISMS:
  product-Fourier closes h=0; joint frame gives M^(-1/2);
  arbitrary rank-two defect closure; old C4SHIFT as current residual.

DIRICHLET/ADDITIVE FIREWALL:
  PASS

LEAF4 FORMAL LOCAL COEFFICIENT:
  c44Loc = lambda1 *_D lambda2 *_D lambda3 *_D lambda5

BARE LEAF5 COEFFICIENT:
  c45 = lambda1 *_D lambda2 *_D lambda3 *_D lambda4

LEAF4 OWNER DISTINCTION:
  PASS (c44Loc != c45; equality only under supplied lambda_4 = lambda_5)

PHYSICAL ROW-LOCAL DICTIONARY INTERFACE:
  CREATED

E(q):
  SOURCE DATA / NOT GUESSED

Z_E(q):
  SOURCE DATA / NOT GUESSED

kappa_4:
  SOURCE DATA / EXPLICIT HYPOTHESIS (kappa4NormalizationHypothesis)

CONDITIONAL LEAF4 COMPILER:
  leaf4_closed_of_physical_dictionary (all antecedents explicit, none supplied)

CONDITIONAL h=0 COMPILER:
  hZeroHighHigh_closed_of_local_dictionary (all five leaves explicit,
  none supplied)

AXIOM AUDIT:
  subset of {propext, Classical.choice, Quot.sound}; no sorryAx;
  no custom axiom; no unsafe / opaque / implemented_by / native_decide.

NEW MODULE BUILD:
  PASS (all five modules, 0 errors, 0 warnings)

DEFAULT lake build:
  PRE-EXISTING FAILURE (missing RequestProject/FixedCertificateAlgebra.lean;
  untouched, unrelated to this delta)

STRONGEST SAFE FORMAL BANK:
  exact finite Fourier / determinant algebra of the previous layers, now
  extended by the unconditional Bézout-row and product-difference integer
  algebra and the formal Leaf-4 local tree with its owner firewall.

CURRENT FIRST SOURCE RESIDUAL:
  ORIGINAL-E(q)-/Z_E(q)-
  PHYSICAL-ROWLOCAL-
  DICTIONARY45.

LEAF 4:
  ANALYTICALLY CLOSED
  MODULO LOCAL SOURCE IDENTIFICATION.

LEAVES 1-3:
  OPEN / NOT PROMOTED.

h=0 HIGH-HIGH:
  ANALYTICALLY CLOSED
  MODULO PHYSICAL LOCAL TREE MATCH.

HNE:
  NOT RUN.

LOWER-D:
  OPEN.

GATE1B:
  OPEN.

FINAL FORMAL VERDICT:
  SAFE APPEND-ONLY BANK UPDATED
```
