# TWIN GATE1B / R11 — `R_loc-top,3` reduction, continuation report

Append-only continuation of the residue-aware formal frontier. Gate1A was not touched. No
pre-existing Gate1B/R11 statement was weakened, renamed or deleted. All new results are
kernel-proved with `#print axioms` restricted to `propext`, `Classical.choice`, `Quot.sound`;
there is no `sorry`, no `axiom`, no `native_decide`, no `@[implemented_by]`, no `opaque` escape in
the new modules.

## Files added

* `Gate1B/R11/Frontier/RLocTop3Reduction.lean` — the exact reduction of `R_loc-top,3`.
* `Gate1B/R11/Frontier/LocalPrincipalReassembly.lean` — exact reassembly, exact sign and mod-3
  sign pairing of the local principal correction.
* `Gate1B/R11/Frontier/PrimeExtremaConstruction.lean` — the prime-extrema realisation constructed;
  vacuity defect of the historical certificate obligation recorded; non-vacuous replacement.

## Files modified (aggregation / audit only)

* `Gate1B/R11/Frontier/Bank.lean` — three new imports and three markers.
* `Gate1B/R11/Frontier/AxiomAudit.lean` — `#print axioms` for every new principal theorem.

## Build plumbing (separate commit, no mathematical statement changed)

The pre-existing global build failure was **not** a single missing file. 92 modules that are
imported under their library names (`RequestProject.X`, `Gate1A.X`, `Gate1B.X`, `Gate04Root.X`,
`UniversalV8.X`, `Universal.X`) were sitting flattened at the repository root as `X.lean`, so no
library glob picked them up. They were relocated into the directory named by their own import
paths; no file content was rewritten except two `import RequestProject.LocalDensity` lines
retargeted to the file's actual library (`Gate1B.LocalDensity`).

One genuine content gap remains and was **not** fabricated: the module `RequestProject.Status`
(which would define `ShiftedMobiusBank.ProofStatus` / `ShiftedMobiusBank.LedgerEntry`) is absent
from the repository. Its two importers, `TwinPrimeStatus.lean` and (transitively)
`PerfectPowerReduction.lean`, are therefore left at the repository root, exactly as before, i.e.
outside every build target. With that, `lake build` on the default targets now completes with
0 errors.

## The mathematics that was added

Write `E_λ*` for the selected centered functional, `Q₃ = ∏_{j∈J}(I − T_j)` for the residue-aware
top projection, `K` for the pairing kernel, and

```
rowConsumer(x) = selectedConsumer λ Ds Ns (K x)         (x a cell of the prime-coordinate table).
```

1. **Fibrewise identity** (`RlocTop3_eq_pair_rowConsumer`)
   `R_loc-top,3 = ⟨ Q₃W , rowConsumer ⟩` for the counting pairing.

2. **Self-adjointness** (`resAvg_self_adjoint`, `subT_self_adjoint`, `Q3_self_adjoint`)
   The residue-aware averages `T_j` are self-adjoint for the counting pairing (proved by the
   fibre-swap involution `(x,y) ↦ (x[j:=y], x_j)`), hence so is `Q₃` on a repetition-free
   eligible list.

3. **The reduction** (`RlocTop3_eq_pair_Q3_rowConsumer`)
   ```
   R_loc-top,3 = ⟨ W , Q₃(rowConsumer) ⟩ .
   ```
   This is an identity, obtained with no absolute values and no estimate: the projection is moved
   off the source and onto the consumer, and the *raw*, uncentered source `W` reappears.

4. **Exact cancellation** (`Q3_of_residueDetermined`,
   `RlocTop3_eq_zero_of_residueDetermined_rowConsumer`)
   `Q₃` annihilates every function of the residue vector alone. Hence `R_loc-top,3 = 0` exactly
   whenever the selected row consumer is residue-determined — in particular whenever the pairing
   kernel is (`residueDetermined_rowConsumer_of_kernel`). Only the *deviation* of the row
   consumer from a residue profile can contribute.

5. **Deterministic budget** (`abs_Q3_le`, `RLocTop3Bound_of_residue_approximation`,
   `RLocTop3Bound_of_profile`, `RLocTop3Bound_of_oscillation`)
   With `r = |J|`, raw ℓ¹ source mass `Mw` and residue-variation error `eps`,
   ```
   |R_loc-top,3| ≤ Mw · 2^r · eps ,
   ```
   so `RLocTop3Bound` holds as soon as `Mw · 2^r · eps ≤ C x L^{-S₀}`.

6. **Sharpness** (`sharp_RlocTop3_eq_one`,
   `residue_awareness_alone_does_not_kill_RlocTop3`)
   An explicit one-coordinate, two-cell instance with `R_loc-top,3 = 1`. The residue-aware
   algebra alone does not kill the residual: the remaining input is load-bearing.

7. **Local principal correction** (`selected_row_lift_split`, and the `three_*` family)
   The lifted selected row splits exactly as `lifted centered row + local principal row` (no
   absolute values). At `h = 3` the correction is computed exactly:
   `−½ · u_d(n)/φ(d)` on `n ≡ 1 (3)`, `+½ · u_d(n)/φ(d)` on `n ≡ 2 (3)`, `0` on `3 | n`. Hence
   **mod-3 sign pairing**: it cancels exactly between the two unit classes at points with the same
   principal profile, and the whole local principal row of a paired window is exactly `0`.

8. **Certificate field audit** (`primeExtremaRealisation_inhabited`,
   `realFordGrammarObligation_holds_vacuously`, `RealFordGrammarObligationFor`)
   `PrimeExtremaRealisation` (least/greatest prime factor with all seven properties) **is**
   constructible — `Nat.minFac` and the maximum of `Nat.primeFactors` — so that field of the
   historical certificate is now discharged. Conversely, the historical obligation as previously
   stated is *vacuously satisfiable* (`Slot := Empty`), so it certifies nothing; the non-vacuous
   replacement `RealFordGrammarObligationFor hist` is supplied and left open.

## STRICT FINAL OUTPUT

```
PREVIOUS RESIDUE-AWARE BANK:
PRESERVED
(one defect found in a pre-existing *interface*, not in a theorem: the historical
 RealFordGrammarObligation is vacuously satisfiable; recorded append-only, nothing edited)

DEDICATED BUILD:
PASS   (Gate1B.R11.Frontier.Bank, Gate1B.R11.Frontier.AxiomAudit)

GLOBAL REPOSITORY BUILD:
PASS   (after the flattened-module relocation; previously it failed at import resolution.
        RequestProject.Status remains genuinely absent and its two dependent files stay
        outside the build targets, exactly as before)

R_loc-top,3:
OPEN — but every deterministic reduction around it is now kernel-proved, and the wall is a
single explicit hypothesis.

R_loc-top,3 REQUIRED BUDGET:
|R_loc-top,3| ≤ Mw · 2^r · eps , so RLocTop3Bound λ Ds Ns K res l W x L S0 C holds as soon as
    (Mw · 2^r · eps : ℝ) ≤ C · x · L^(−S₀),
  r  = l.length          (number of eligible prime coordinates)
  Mw = ∑_x |W x|         (ℓ¹ mass of the RAW, uncentered source)
  eps= residue-fibre oscillation of the selected row consumer
Equivalently: eps ≤ C x L^{−S₀} / (Mw 2^r).
Support: Ds (moduli) × Ns (n-window) × the finite prime-coordinate table.
Weights: λ on Ds, centeredSel d n = δ_d(n) − u_d(n)/φ(d) on Ns, W on the table.
Residue restriction: the residue map res (mod 3 in the intended instance), eligible list l Nodup,
l ≠ [].
Downstream R11 margin: NOT formalised — RLocTop3Bound currently has no Lean consumer other than
the status ledger row `rlocTop3AnalyticBound = openRow`, so no numerical margin can be claimed.

MOD3 ANALYTIC CALLER:
EXTERNAL_ANALYTIC / OPEN (interface `Mod3CenteredCaller`, still never inhabited).
Its deterministic surroundings are now proved: the lifted-row split and the exact sign and
cancellation of the local principal correction.

REALFORDGRAMMARCERTIFICATE:
INHABITED **only vacuously** (empty slot type) — proved, and flagged as a defect of the
statement, not as progress. Field audit:
  Slot, fordCoefficient, extremaAtom, fordProvenance : data, deterministic once the historical
    coefficients are fixed;
  primeExtrema : KERNEL_PROVED (constructed);
  grammar      : OPEN — the genuine obstruction, since the admissible grammar excludes the
    prime-extrema atoms.
Non-vacuous obligation `RealFordGrammarObligationFor hist`: OPEN.

HISTORICAL WEIGHTED PUSHFORWARD:
CONDITIONAL (unchanged: the linear identities are kernel-proved, the comparison parameter is an
uninhabited evidence interface).

Q3 PROVENANCE RESIDUAL:
OPEN, but strictly reduced: by the self-adjoint reduction the residual is
⟨ Δ , Q₃(rowConsumer) ⟩, so it vanishes identically for a residue-determined consumer and is
otherwise controlled by the same residue-oscillation quantity. Not assumed small because centered.

GENERATED-GRAMMAR PHYSICAL ADAPTER:
INCOMPLETE — the variation-controlled subgrammar (Möbius atom, Mellin twist and perfect-power
pullback excluded) is unchanged; no physical weight was newly certified into it in this run.

MINIMAL OPEN CUT SET:
1. Gate1B.R11.Frontier.ResidueProj.RowConsumerResidueOscillation
   ∀ x y with the same residue vector, |rowConsumer x − rowConsumer y| ≤ eps.
   English: the selected consumer of a kernel row depends on the prime-coordinate cell only
   through its residue vector, up to eps.
   Required strength: eps ≤ C x L^{−S₀} / (Mw 2^r).
   Downstream consumer: RLocTop3Bound (via RLocTop3Bound_of_oscillation), hence R_loc-top,3.
   Evidence: none — never inhabited; and it cannot be dropped
   (residue_awareness_alone_does_not_kill_RlocTop3).
2. Gate1B.R11.Frontier.Mod3CenteredCaller  (EXTERNAL_ANALYTIC, unchanged).
3. Gate1B.R11.Frontier.RealFordGrammarObligationFor  (historical provenance, non-vacuous form).
4. Gate1B.R11.Frontier.ResidueProj.ConditionalConsumerComparison  (historical weighted
   pushforward evidence parameter, unchanged).

R11:
OPEN.

POST-R11 OWNERS: not reached (R11 is open); `R_hi` and `R_newcrit` remain historical coordinates
and were not double-counted or closed.

GATE1B:
OPEN.

HSTAR:
OPEN.

TWIN PRIME:
NO CLAIM.
```

## NEXT_GENERATION_STATE

Begin from the minimal open cut set above. Concretely:

1. Pin the physical pairing kernel `K` of the R11 instance inside Lean (currently it is an
   abstract parameter), then either prove `RowConsumerResidueOscillation` for it with the budget
   `eps ≤ C x L^{−S₀}/(Mw 2^r)`, or exhibit the exact analytic theorem it needs.
2. Everything between that hypothesis and `RLocTop3Bound` is already kernel-proved — no further
   deterministic layer is needed on that path.
3. The `Mod3CenteredCaller` interface should be attacked as the physical source of the same
   oscillation bound, using the now-proved lifted-row split and mod-3 sign pairing.
4. The historical provenance route must use `RealFordGrammarObligationFor`; the old obligation is
   vacuous and must not be used to close anything.
