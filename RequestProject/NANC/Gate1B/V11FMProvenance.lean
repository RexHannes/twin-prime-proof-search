import RequestProject.NANC.Gate1B.V11FMPerronGrammarCompiler

/-!
# V11 · Gate 1B — Ford-paper provenance vs. Lean status

**This module contains no declarations.**  It is metadata only, because the
literal Ford–Maynard proof objects are *not* formally represented in this
repository and v11 refuses to pretend otherwise.

## What is formal in the repository

* `TwinPrimeProject.Gate1BV11.FMSieveGenTypeIIAtScale` — a **new v11
  project-local** predicate of equation-(7.23) shape, for arbitrary 1-bounded
  factor functions.  Nothing identifies it with any published statement.
* `TwinPrimeProject.Gate1BV11.FMPerronGeneratedTypeIIAtScale` — the weaker v11
  predicate, quantified only over factor functions carrying a generated
  certificate.
* `fmPerronGeneratedTypeII_of_sieveGen` — the proved implication
  SieveGen ⟹ Generated.

## Research-level claim RC1 (recorded, NOT formalised)

> FM-SIEVEGEN-TYPEII is sufficient for the equation-(7.23) step.

Status: **research claim, unformalised.**  To formalise it one would first need a
formal statement of the (7.23) step itself, which is absent from this
repository.  Recording it here is a note for a later audit, not a theorem.

## Research-level claim RC2 (recorded, NOT formalised, strictly stronger)

> The actual Proposition-7.22 proof may be re-run without arbitraryising its
> generated factors — i.e. every coefficient the proof manufactures is
> `FMPerronGenerated`.

Status: **research claim, unformalised, and deliberately not encoded as a
theorem.**  The only object that could carry it is
`TwinPrimeProject.Gate1BV11.RealFordGrammarCertificate`, which

* needs a formal representation of the coefficients produced by the literal
  proof, and
* needs a `PrimeExtremaRealisation` (the repository has no `P⁻` / `P⁺`),

and is therefore **left without an inhabitant**.  No theorem in v11 concludes
anything from RC2, and no theorem asserts RC2.

## Explicitly NOT claimed anywhere in v11

Siegel–Walfisz; quantitative prime-box PNT; Perron analytic truncation error;
Dirichlet-polynomial mean-value theorem; S2 analytic generated-twist
cancellation; Blomer–Pascadi; Pascadi Theorem 7.1; moving-Θ source-multiplier
cancellation; pair-modulus analytic closure; Gate-1B closure; the Ford–Maynard
theorem; twin primes.

## Absences recorded (searched, not found in the repository)

* `Pminus` / `Pplus` / least- or greatest-prime-factor functions — ABSENT.
* `FullFMTypeII_OneSixth`, `FMTypeIIExactAtScale` — ABSENT (already recorded in
  the V10 bank; v11 does not create substitutes).
* `ShiftedQuotientParentBound`, `QK56FullCovarianceBound` — ABSENT; v11 defines
  them as **new project-local predicates** under those names, clearly marked as
  v11 objects.
-/
