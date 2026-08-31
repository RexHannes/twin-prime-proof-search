# Gate 1B — Additive-Minor Delta Safe Bank

Append-only delta layer. No historical status layer was modified; no previously
banked module was rebuilt or reproved; Gate 1B was not reproved; the new
analytic crosspair was not attacked.

## New modules

| Module | Content |
| --- | --- |
| `RequestProject/CurrentProgramme/FiniteLiftLocalTwistCompression.lean` | exact local-twist expansion, Möbius coprimality identity, cell bookkeeping, uninhabited divisor-summation input |
| `RequestProject/CurrentProgramme/NearPrimitivePhysicalProjector.lean` | projector weight `Ω_c(S)`, `φ*(c)`, pure order lemma, large/small projector split, induced lifts, uninhabited analytic inputs, weighted physicalisation compiler |
| `RequestProject/CurrentProgramme/BroadMinorAdditiveFourier.lean` | `+`-signed DFT, exact Parseval pairing, `ρ̂=(1−Π)δ̂`, multiplier pairing with the `Π(1−Π)` factor, idempotence orthogonality, non-idempotence countermodel, plateau zero, uninhabited transition input and its conditional compiler |
| `RequestProject/CurrentProgramme/DetLineCompanionAdditiveFourier.lean` | companion skeleton, exact determinant equivalence with integrality exposed, DFT normal form, divisibility completion, completed quotient phase |
| `RequestProject/CurrentProgramme/DetLineAdditiveMinorCrosspairSocket.lean` | source-specific `additiveMinorCrossPair`, uninhabited crosspair socket, Cauchy natural-scale lemma, TT\* representation-loop fact |
| `RequestProject/CurrentProgramme/CurrentStatusGate1BAdditiveMinor.lean` | new append-only status layer with honesty theorems |
| `RequestProject/CurrentProgramme/AxiomAuditGate1BAdditiveMinor.lean` | `#print axioms` over all principal new declarations |

## Status rows (new layer `LedgerAdditiveMinor.full`)

| Label | Status | Note |
| --- | --- | --- |
| DETLINE-FINITELIFT-LOCAL-TWIST-COMPRESSION45 | `provedFinite` | exact expansion kernel-proved; divisor summation uninhabited input |
| DETLINE-NEARPRIM-PRIMITIVE-TO-PHYSICAL45 | `conditionalCompiler` | finite algebra kernel-proved; weighted analytic conclusion conditional |
| BROADMINOR-INTERNAL-MAJOR-ORTHOGONALITY45 | `provedFinite` | plateau kernel-proved; transition conditional on uninhabited input |
| DETLINE-COMPANION-ADDITIVE-FOURIER45 | `provedAlgebraic` | normal form + completion kernel-proved |
| ADDITIVE-MINOR-SEPARATE-ENERGY45 | `capacityOnly` | natural scale, nonclosing; NOT false |
| ADDITIVE-MINOR-TTSTAR45 | `notCurrentlyRequired` | representation loop, noncontrolling; NOT false |
| DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45 | `supersededAsControllingFrontier` | strictly reduced; NOT false |
| DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45 | `analyticOpen` | first exact current research residual; uninhabited |
| DETLINE-HIGHCOND-BETA-RHO-CROSSPAIR45 | `analyticOpen` | finite-lift child is the additive-minor crosspair |
| TOPBAND-BETA-BROADMINOR-DETLINE45 | `open_` | |
| TOPBAND-RECURSIVE-MAJOR-TREE-PAIRING45 | `open_` | |
| TOPBAND-BROAD-MAJOR-TREE-MATCH45 | `sourceOpen` | not run |
| SHIFTED-MAM-TOPBAND45 | `open_` | |
| RANKONE-ENDPOINT-ALLK45 | `conditionalCompiler` | conditional / open |
| PURE5 | `open_` | not activated |
| GATE1B | `open_` | |

The taxonomy has no `nonclosingAtNaturalScale`, `representationLoop`,
`partial` or `researchClosed` constructor; no misleading constructor was
invented, and the nearest honest status was used with a precise note.

## Uninhabited interfaces introduced

```
FiniteLiftLocalTwist.LocalTwistDivisorSummationInput
NearPrimitiveProjector.PrimitiveProjectorIdentityInput
NearPrimitiveProjector.SmallProjectorLargeLiftClosureInput
NearPrimitiveProjector.ProjectorWeightErrorEstimateInput
NearPrimitiveProjector.NearPrimitiveToPhysicalAnalyticInput
BroadMinorFourier.BroadMinorTransitionEstimateInput
AdditiveMinorCrosspair.DetLineNearPrimAdditiveMinorCrosspairInput
```

None of them is inhabited anywhere in the repository.

## Required final block

    PREVIOUS FINITE-LIFT BANK:
        PRESERVED.

    FINITE-LIFT LOCAL TWISTS:
        EXACT EXPANSION KERNEL-PROVED
        (1_{uAs ≡ -2 mod e} = (1/e) Σ_ν e_e(ν(uAs+2));
         1_{gcd(s,e)=1} = Σ_{a | gcd(s,e)} μ(a);
         cell count e·τ(e) with (1/e)·e·τ(e) = τ(e)).
        ANALYTIC DIVISOR SUMMATION: UNINHABITED INPUT.

    PRIMITIVE PROJECTOR ALGEBRA:
        RHS KERNEL LEVEL PROVED
        (projKernel c d = Σ_{r|c, r|d} φ(r) μ(c/r); split, weights, Ω_c(S), φ*(c)).
        THE CHARACTER-SIDE IDENTITY IS AN UNINHABITED INTERFACE.

    LARGE PROJECTORS:
        PHYSICAL DIAGONAL / KERNEL-PROVED
        (r > 2S, r | s1-s2, |s_i| ≤ S ⇒ s1 = s2;
         largeProjector = Ω_c(S) on the diagonal, 0 off it).

    SMALL PROJECTORS:
        LARGE-LIFT CONDITIONAL ROUTE / EXACT INDUCED LIFT e' = e·(c/r) = ℓ/r
        KERNEL-PROVED; CLOSURE IS AN UNINHABITED INPUT.

    WEIGHTED PHYSICALISATION:
        EXACT SPLIT KERNEL-PROVED
        (packet = weighted physical diagonal + small-projector routed terms);
        WEIGHTED ANALYTIC CONCLUSION CONDITIONAL / EXTERNAL.

    rhohat=(1-Pi)deltahat:
        EXACT / KERNEL-PROVED, WITH THE EXACT PARSEVAL PAIRING.

    SMOOTH Pi IDEMPOTENCE:
        NOT ASSUMED.
        ⟨ρ, P_Π F⟩ = (1/q) Σ_m Π(1-Π) δ̂ conj(F̂) is proved exactly;
        vanishing is proved ONLY under Π² = Π;
        an explicit countermodel is banked.

    MAJOR PLATEAU:
        EXACT ZERO / KERNEL-PROVED.

    TRANSITION:
        ANALYTIC INPUT / UNINHABITED (conditional compiler only).

    COMPANION ADDITIVE FOURIER:
        EXACT DFT NORMAL FORM AND DIVISIBILITY COMPLETION KERNEL-PROVED,
        WITH uA | ℓ(dp-uh)-2 EXPLICIT AND THE GENUINE QUOTIENT PHASE.

    ADDITIVE-MINOR EXPRESSION:
        DEFINED EXACTLY, NOT ESTIMATED.

    NATURAL L2 ROUTE:
        NONCLOSING AT RESEARCH LEVEL.

    TT* ROUTE:
        REPRESENTATION LOOP AT RESEARCH LEVEL.

    PREVIOUS FINITE-LIFT FRONTIER:
        SUPERSEDED / STRICTLY REDUCED;
        NOT FALSE.

    CURRENT FIRST EXACT RESIDUAL:
        DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45.

    TOPBAND:
        OPEN.

    PURE5:
        OPEN.

    GATE1B:
        OPEN.

    TARGETED BUILDS:
        PASS for all seven new modules (8065 jobs, 0 errors).

    GLOBAL BUILD:
        PRE-EXISTING FAILURE, UNRELATED AND NOT REPAIRED:
        root-level `K0K1Status.lean` / `RequestProject/CurrentProgramme/R9LeakageArithmetic.lean`
        import `RequestProject.FixedCertificateAlgebra`, which is outside the
        current `RequestProject.+` library glob.

    AXIOM AUDIT:
        53 new declarations audited; only propext, Classical.choice, Quot.sound.
        No sorry / admit / axiom / opaque / unsafe / native_decide /
        @[implemented_by] in the new files.

## FINAL FIREWALL

This layer formalises exact finite/projector/Fourier algebra and the dependency
graph leading to the current additive-minor crosspair.

It DOES NOT prove the analytic arbitrary-log estimate

    DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45,

and therefore DOES NOT close TOPBAND, PURE5 or GATE1B.
