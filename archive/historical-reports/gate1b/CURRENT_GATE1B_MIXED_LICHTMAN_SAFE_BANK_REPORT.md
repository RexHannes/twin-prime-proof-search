# CURRENT GATE 1B — CENTERED 2×2 MIXED SOURCE / LICHTMAN SOCKET · SAFE BANK REPORT

Append-only continuation of `/workspace/request-project`, namespace
`TwinPrimeProject.CurrentProgramme`, tree `RequestProject/CurrentProgramme/`.

**No pre-existing file was modified.**  The diff of this run consists of ten new
Lean modules, this report, and nothing else.  `ARISTOTLE_SUMMARY.md` and every
historical bank (V8.x / V9.x / V10 / V11 / Gate01 / Gate1A / Gate1B / Gate04Root
and the earlier `CurrentProgramme` modules) are untouched.

New modules:

```
RequestProject/CurrentProgramme/EndpointCentering.lean
RequestProject/CurrentProgramme/EndpointTwoByTwoSplit.lean
RequestProject/CurrentProgramme/EndpointCenteredRewriting.lean
RequestProject/CurrentProgramme/EndpointMixedAddMult.lean
RequestProject/CurrentProgramme/EndpointCollisionL2.lean
RequestProject/CurrentProgramme/LichtmanT18Socket.lean
RequestProject/CurrentProgramme/LichtmanT18Capacity.lean
RequestProject/CurrentProgramme/EndpointMixedCompiler.lean
RequestProject/CurrentProgramme/CurrentStatusMixed.lean
RequestProject/CurrentProgramme/AxiomAuditMixed.lean
```

---

## A. FRONTIER RESET

The previous run's record

```
RANKONE-ENDPOINT-U-OFFDIAG45 : first analytic blocker
```

was correct at the time.  The controlling ledger is now, in the new
append-only layer `LedgerMixed` (`CurrentStatusMixed.lean`):

```
RANKONE-ENDPOINT-U-OFFDIAG45
    SUPERSEDED AS CONTROLLING FRONTIER / REDUCED, NOT FALSE.

ENDPOINT-CENTERED-BETA-RANK2-TWOFREQ45
    REDUCED, NOT CLOSED.

ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45
    CURRENT FIRST ANALYTIC/SOURCE FRONTIER.
```

The historical endpoint objects are **not deleted**.  Two Lean facts enforce
this:

* `LedgerMixed.historical_offdiag_row_preserved` — the original
  `RANKONE-ENDPOINT-U-OFFDIAG45` row (status `analyticOpen`, original note) is
  still a member of the untouched `Ledger.gate1B`;
* `LedgerMixed.offdiag_superseded_not_false` — in the new layer the same object
  carries `Status.supersededAsControllingFrontier`, which is proved to be
  neither `falseRoute` nor a kernel-proof status.

Baseline before any edit: `lake build` **PASS, 8612 jobs, 0 errors**.

---

## B. CENTERING  (`ENDPOINT-A-CENTERING45 : LEAN_PROVED_FINITE`)

`EndpointCentering.lean`.

The centered residue kernel is implemented on the exact finite residue system
`ZMod ℓ`:

```
centeredKernel ℓ x y = 1_{x = y} − 1_{xy is a unit} / φ(ℓ)
```

with integer-level pullback `centeredKernelInt`.

Proved:

* `centeredKernel_symm`, `centeredKernel_units` (explicit two-term shape on the
  unit system);
* **zero-row identity** `centeredKernel_row_sum_units`:
  `∑_{y ∈ (ZMod ℓ)ˣ} Δ_ℓ(x, y) = 0` — the congruence indicator contributes `1`
  and the principal term contributes `φ(ℓ)/φ(ℓ) = 1`;
* **generic centering** `sum_mul_conj_eq_sum_centered_mul_conj`: for any
  residue discrepancy `E` of *exact zero mean* on a finite set `S`,
  `∑_a A_a conj(E_a) = ∑_a A°_a conj(E_a)` with `A° = A − avg A`;
* `sum_centeredCoeff` (a centering does have zero mean);
* counterguard `centering_needs_zero_mean`: without the zero-mean hypothesis the
  identity is **false**.

Not done, deliberately: the physical Pure5 discrepancy is absent from the
repository, so **no adapter** from a physical discrepancy to the zero-mean
hypothesis was invented.

```
PURE5-COMPARISON-MAINTERM-PIN : SOURCE_OPEN   (unchanged)
```

---

## C. 2|2 SPLIT  (`ENDPOINT-2x2-MODEL-SPLIT45 : LEAN_PROVED_FINITE`)

`EndpointTwoByTwoSplit.lean`, over an arbitrary commutative monoid `M`.

```
conv2 S T f g m = ∑_{x ∈ S} ∑_{y ∈ T} [xy = m] f(x) g(y)
conv4 S₁S₂S₃S₄ f₁f₂f₃f₄ u = ∑ [x₁x₂·x₃x₄ = u] f₁f₂f₃f₄
```

* `sum_group_one` — the generic exact grouping lemma: grouping by the values of
  a map, with no injectivity, so repeated factorisations are counted with their
  exact multiplicity;
* `conv4_eq_conv2_conv2` — **the exact split** `a₄(u) = ∑_{mr = u} α(m) γ(r)`;
* `conv2_conj`, `sum_conv2_weight`, `sum_conv2_conj_weight` — weighted rewriting
  lemmas used downstream;
* `coverage_is_load_bearing` — a countermodel showing the support-coverage
  hypotheses cannot be dropped.

`EndpointCenteredRewriting.lean` then proves, for an **abstract** kernel
`D ℓ u₁ u₂` and **abstract** line coefficient `Z(u, ℓ, k)`,

```
rCent_two_by_two :
  R_cent = ∑_ℓ ∑_{m,r,m',s} α(m)γ(r) conj(α(m')γ(s))
              D_ℓ(mr, m's) Z(mr,ℓ,k) conj Z(m's,ℓ,k).
```

Source-neutral: no property of `D` or `Z` is used, so it applies to the centered
kernel of §B in particular.

---

## D. MIXED ν COEFFICIENT  (`ENDPOINT-MIXED-ADDMULT-SEQUENCE45 : LEAN_PROVED_FINITE`)

`EndpointMixedAddMult.lean`.

* `nat_sub_is_not_int_sub` — explicit ℕ/ℤ subtraction firewall; `ν` lives over
  `ℤ` throughout.
* `nu m m' r s = m's − mr`.
* `nonzero_congruence_iff_unique_j` — on the nonzero congruence child,
  `mr ≡ m's (mod ℓ)` together with `mr ≠ m's` holds **iff** there is a *unique*
  nonzero integer `j` with `ν = jℓ`.
* `bMix Pm α Z ℓ k r s ν` — the mixed coefficient at a fixed `ν`.
* `mixed_regroup` (fixed `ℓ, r, s`) and `nonzeroCongruence_regroup` (full):

```
nonzero centered congruence contribution
  = ∑_ℓ ∑_{r,s} γ(r) conj γ(s) ∑_{j ≠ 0} bMix(jℓ, r, s; ℓ, k),
```

subject to the exact finite support condition `hJ` (the `j`-ranges of the finite
model), which is carried explicitly rather than assumed away.

---

## E. COLLISION PARAMETRISATION

`EndpointCollisionL2.lean`.

* `gcd_decomposition` — `ρ = (r,s) > 0`, `r = ρr₀`, `s = ρs₀`,
  `IsCoprime r₀ s₀`.
* `collision_param` — if `m₁'s − m₁r = m₂'s − m₂r` then there is `t : ℤ` with
  `m₁ − m₂ = s₀t` and `m₁' − m₂' = r₀t`.
* `collision_param_converse` — every such `t` produces a collision (no
  coprimality needed).

Both are kernel-checked exact integer identities.

---

## F. MIXED L² BOUND  (`ENDPOINT-MIXED-COEFF-L2-45 : PROVED_FINITE`)

* `norm_sq_sum_le_card_mul` — `‖∑ z‖² ≤ #s · ∑ ‖z‖²`.
* `sum_sq_collision_le` — the abstract collision inequality

```
∑_ν ‖B_ν‖² ≤ K · ∑_{p ∈ P} ‖X(p₁)‖² ‖Y(p₂)‖²,
```

  where `K` is a bound for the **actual** fibre cardinalities of the finite
  model, supplied as a hypothesis.  **No `1 + ρ` is written anywhere**, and no
  `X^{o(1)}` is encoded.
* `sum_sq_product_factor` — exact factorisation on a product box.
* `bMix_eq_pair_sum` + `sum_sq_bMix_le` — the mixed coefficient is a genuine
  rank-one pair sum, hence

```
∑_ν ‖bMix(ν)‖² ≤ K · (∑_m ‖α(m)Z(mr)‖²)(∑_{m'} ‖α(m')Z(m's)‖²).
```

* `collision_fibre_card_le_interval` — the *interval* capacity count actually
  justified by a box model `Pm = Icc a b` with `a ≤ b`, `s₀ > 0`:

```
#{m ∈ Icc a b : s₀ ∣ m − m₀} ≤ (b − m₀)/s₀ − (a − m₀)/s₀ + 1.
```

  (The hypothesis `a ≤ b` is necessary; without it the statement is false.)

Status classification actually earned: **PROVED_FINITE**, with the multiplicity
as an explicit hypothesis.  It is *not* promoted beyond that.

---

## G. gcd COST

The project contains no divisor-moment lemma strong enough to turn the gcd
factor into a polylog / subpolynomial cost.  Therefore

```
MixedGcdMomentInput : UNINHABITED arithmetic/source interface
ENDPOINT-MIXED-GCD-MOMENT45 : SOURCE_OPEN
```

`mixedGcdMoment_not_automatic` shows the interface is not vacuous (data with an
impossible level cannot be realised).  Nothing subpolynomial is asserted.

---

## H. LICHTMAN SLOT SCHEMA

`LichtmanT18Socket.lean`.

**The external theorem is not formalised, not assumed, not axiomatised.**  What
exists is a *data schema* `LichtmanT18Dictionary` with theorem-slot names
distinct from the physical variables (`rL, sL, nL, cL, dL`), recording:

physical → `rL/sL/nL/cL/dL` maps; theorem parameter `a`; modulus `q₀`; residue
classes `c₀, d₀`; the coprimality condition; the smooth weight `g(c,d,n,r,s)`;
the coefficient `b_{n,r,s}`; five support/range fields with their inequalities;
and the **phase identity** pinning the recorded physical phase to
`g · b` at the mapped variables.

Every field is concrete data, an equality, or an inequality — there is no bare
`Prop` placeholder.

`LichtmanT18PhysicalPin` is the separate obligation that pins `physPhase` to the
actual mixed summand `α(m) conj α(m') Z(mr) conj Z(m's)`.

Counterguards: `dictionary_phase_not_free`, `dictionary_cClass_rigid`,
`physicalPin_determines_phase`.

```
ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45 : SOURCE_OPEN / UNINHABITED
```

No term of `LichtmanT18Dictionary` or `LichtmanT18PhysicalPin` is constructed
anywhere in the repository.

---

## I. b / tilde-b NORM OBLIGATIONS

`LichtmanT18CoeffNorms` records: the parameter `a`; the coefficient family `b`
and its finite support; the ordinary `ℓ²` norm **with the pin that it really is
that norm**; the divisor-transformed family `tildeB(n'')` with its norm function
and pin; the divisor-support condition `n'' ∣ a^∞`; and the uniform norm bound
the external theorem requires.

The definition of `tildeB` is deliberately a *data field*: the external theorem
has not been transcribed into this repository, so guessing a formula would be a
fabricated transcription.

`transformed_norm_not_determined_by_l2` proves the reason this is a genuine
extra obligation: equal ordinary `ℓ²` norms do **not** determine transformed
norms.

```
LICHTMAN-T18-COEFF-NORM-DICTIONARY45 : SOURCE_OPEN
```

---

## J. 66/107 RATIONAL SIGNAL

`rational_signal_66_107 : (66:ℚ)/107 − 8/13 = 2/1391`, together with
`rational_signal_pos`.

```
ENDPOINT-66107-RATIONAL-SIGNAL45 : PROVED_ALGEBRAIC / CAPACITY_ONLY
```

Explicitly **not** labelled `ENDPOINT-66107-CAPACITY45 : PASS`.  The headline
`66/107` distribution exponent is not by itself a literal Theorem-1.8 endpoint
capacity calculation; and **no conversion to an `X`-exponent is asserted**,
because that algebra is not represented in the repository.
`rational_signal_is_not_a_capacity_certificate` records that a positive rational
gap carries no analytic content by itself.

---

## K. EXPLICIT J LEDGER

`LichtmanT18Params` (`a, q₀, C, D, N, R, S, θ`) and `LichtmanT18JLedger`
(`params`, `jTerm1`, `jTerm2`, `jSq`, and the pin `jSq = jTerm1 + jTerm2`).

The two `J²` terms are **data fields**, not guessed formulas.  What Lean checks
is the arithmetic a later dictionary will need:
`LichtmanT18JLedger.jSq_eq_total` and `LichtmanT18JLedger.jSq_le_of_terms`
(termwise bounding).  This is algebraic metadata only; nothing states that the
external theorem bounds the physical source.

---

## L. CONDITIONAL ENDPOINT COMPILER

Two compilers, both deterministic implications with **no antecedent inhabited**.

1. Capacity (`LichtmanT18Capacity.lean`):
   `endpointMixedLichtmanCapacity_of_inputs` — from `EndpointMixedLichtmanInputs`
   (dictionary + norms + substituted J-ledger + termwise bounds + prefactor
   certificate, with the `bMatch`/`aMatch` consistency pins) it follows that
   `prefactor · J² ≤ target`.

2. Endpoint (`EndpointMixedCompiler.lean`):
   * `nonzeroCongruence_norm_le_of_socket` — kernel-proved aggregation: given a
     socket bound `Bsock ℓ r s` for each `∑_{j≠0} bMix`, the nonzero centered
     congruence contribution is at most
     `∑_ℓ ∑_{r,s} ‖γ(r)‖‖γ(s)‖ Bsock(ℓ,r,s)`;
   * `EndpointMixedSocketInput` — the uninhabited package carrying the finite
     support data plus the **open source** fields (`dict`, `pin`, `norms`), the
     **open analytic** field (`analytic`) and the **open capacity** field;
   * `endpoint_bound_of_socket_input` — the conditional conclusion
     `‖nonzeroCongruenceContribution‖ ≤ target`.

Non-automaticity and non-vacuity are both kernel-checked:
`requiresDictionary`, `requiresAnalytic`, `capacity_not_automatic`, and
`nonzeroCongruenceContribution_nonvacuous` (the contribution equals `2` in an
explicit finite model, so `zero_budget_fails`).

Small-`k` firewall (Phase G): `finite_k_sum_cost` shows a scalar bound applied
independently to each of finitely many `k` costs exactly `#k`, i.e. fixed
polylog for `|k| ≤ log^C X`, and `finite_k_cost_is_attained` shows the factor is
attained.  Therefore

```
LICHTMAN-T18-HILBERT-LIFT45 : NOT CURRENTLY REQUIRED FOR SMALL-k
```

and it is **not** banked from linearity.

---

## M. COMPARISON FIREWALL

`PURE5-COMPARISON-MAINTERM-PIN : SOURCE_OPEN`, unchanged.  The new compiler does
not connect it: `comparison_remains_independent` records that an endpoint norm
bound is logically independent of the main-term identification, and
`comparison_pin_is_the_existing_interface` shows the pin is still the existing
project interface (uninhabited).  Only the generic canonical zero-mode algebra
of §B is available; it is **not** promoted to the physical Pure5 local-density
equality.

---

## N. BUILD / TRUST

* Baseline (before any edit): `lake build` **PASS, 8612 jobs, 0 errors**.
* Final: `lake build` **PASS, 8622 jobs, 0 errors** (+10 new modules).
* Text scan of all ten new modules for `sorry`, `admit`, `axiom`, `opaque`,
  `unsafe`, `native_decide`, `@[implemented_by]`: **no occurrence** except the
  two documentation lines in `AxiomAuditMixed.lean` describing this scan.
* `AxiomAuditMixed.lean` runs `#print axioms` on **53** principal declarations:
  42 report `[propext, Classical.choice, Quot.sound]`, 6 report `[propext]`,
  5 report `[propext, Classical.choice, Quot.sound]` in the short form — i.e.
  every one is within the standard three.  **No `sorryAx`, no
  `Lean.ofReduceBool`.**
* No source or analytic interface is instantiated: `LichtmanT18Dictionary`,
  `LichtmanT18PhysicalPin`, `LichtmanT18CoeffNorms`, `MixedGcdMomentInput`,
  `EndpointMixedLichtmanInputs`, `EndpointMixedSocketInput` have **no**
  constructor application anywhere in the project, in particular none via
  `Classical.choice`.

---

## O. FIRST SOURCE BLOCKER

The repository was searched again for the literal physical endpoint source

```
β_{D,P} = μ_D ⋆ Λ_P.
```

It is **still absent**: the only occurrences are the pre-existing uninhabited
interface `Interfaces.EndpointBetaSourceDictionary` and documentation.  Nothing
was invented.

```
ENDPOINT-BETA-PHYSICAL-DICTIONARY45 : SOURCE_BLOCKED / UNINHABITED
```

All the algebra of §§B–F was therefore developed for an abstract line
coefficient `Z(u, ℓ, k)` and abstract `α, γ`.

---

## P. FIRST ANALYTIC BLOCKER

```
ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45
```

— jointly the source dictionary (§H) and the external analytic socket bound
carried by `EndpointMixedSocketInput.analytic` (§L).  Downstream of it, the
first *arithmetic* blocker is `MixedGcdMomentInput` (§G).

---

## Q. NEXT UNIQUE ACTION

Transcribe the external theorem's literal statement — in particular the two
`J²` terms and the exact `tildeB` construction — into the repository, then
attempt to *inhabit* `LichtmanT18Dictionary` together with
`LichtmanT18PhysicalPin` for the mixed coefficient `bMix`.  Every downstream
step is already a kernel-proved implication, so the substituted parameters would
be checked by Lean without further algebra.

---

## R. FINAL LEDGER

```
Motohashi A/B/C                                BANKED RESEARCH / SOURCE LEVEL
polylog-k interior                             CLOSED MODULO COMPARISON
endpoint finite/power routers                  BANKED / CAPACITY
ENDPOINT-A-CENTERING45                         LEAN_PROVED_FINITE
ENDPOINT-2x2-MODEL-SPLIT45                     LEAN_PROVED_FINITE
ENDPOINT-2x2-CENTERED-REWRITING45              LEAN_PROVED_FINITE
ENDPOINT-MIXED-ADDMULT-SEQUENCE45              LEAN_PROVED_FINITE
ENDPOINT-MIXED-COLLISION-PARAM45               PROVED
ENDPOINT-MIXED-COEFF-L2-45                     PROVED_FINITE (actual multiplicity)
ENDPOINT-MIXED-GCD-MOMENT45                    SOURCE_OPEN / UNINHABITED
ENDPOINT-66107-RATIONAL-SIGNAL45               PROVED_ALGEBRAIC / CAPACITY_ONLY
ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45   SOURCE_OPEN
LICHTMAN-T18-COEFF-NORM-DICTIONARY45           SOURCE_OPEN
LICHTMAN-T18-HILBERT-LIFT45                    NOT CURRENTLY REQUIRED FOR SMALL-k
ENDPOINT-LICHTMAN-T18-LITERAL-CAPACITY45       CONDITIONAL / OPEN
ENDPOINT-MIXED-CONDITIONAL-COMPILER45          CONDITIONAL COMPILER
ENDPOINT-BETA-PHYSICAL-DICTIONARY45            SOURCE_BLOCKED / UNINHABITED
RANKONE-ENDPOINT-U-OFFDIAG45                   SUPERSEDED, REDUCED, NOT FALSE
ENDPOINT-CENTERED-BETA-RANK2-TWOFREQ45         REDUCED, NOT CLOSED
RANKONE-SMALLK-ENDPOINT45                      OPEN
RANKONE-HIGHK45                                OPEN
PURE5-COMPARISON-MAINTERM-PIN                  SOURCE_OPEN

GATE1B:                                        OPEN
```

Nothing in this run proves the external Lichtman-type theorem, the endpoint
bound, Gate 1B closure, Ford–Maynard, or twin primes.  The deliverable is a
machine-visible exact reduction of the centered `2|2` mixed endpoint to the
Lichtman source/capacity socket.
