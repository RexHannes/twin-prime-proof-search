# GATE 1B — HSTAR TWO-ANCHOR / CENTERED SOURCE / CAUCHY FIREWALL SAFE BANK

**Mode: strictly append-only.**  No existing file or theorem was edited,
weakened, renamed, deleted or relocated.  The only modification to an existing
file is a block of imports appended to the end of `Main.lean`.

---

## 0. Files added

| file | content |
|---|---|
| `Gate1B/HStarTwoAnchorPhysicalSource.lean` | §2 exact physical two-anchor source, defects, moduli, non-vacuity witness |
| `Gate1B/HStarTwoAnchorDifferenceAlgebra.lean` | §3, §5 derived two-`T` difference algebra and the source-exact equivalent system |
| `Gate1B/HStarTwoAnchorCounterguards.lean` | §4, §17, §18 non-converse firewall, independent-`H` firewall, single-line Δ retraction |
| `Gate1B/HStarOneTTwoTFirewall.lean` | §6, §7, §8 one-`T` rigidity, one-`T`/two-`T` firewall, Cauchy majorant vs exact square |
| `Gate1B/HStarCenteredAdditiveProjector.lean` | §10, §11 centred additive projector, zero mode, two-copy cancellation |
| `Gate1B/HStarHZeroFiniteRouter.lean` | §9 clean `H = 0` finite arithmetic router |
| `Gate1B/HStarMobiusPrimeSource.lean` | §12–§15 clean λ-cell Möbius algebra, prime typing, finite `Λ♯`, shift firewall |
| `Gate1B/HStarAnchorPreservingCovariance.lean` | §16 anchor-preserving centred covariance object |
| `Gate1B/HStarAnchorPreservingAnalyticInterface.lean` | §19, §20 uninhabited analytic interface and the FM722 metadata layer |
| `Gate1B/CurrentStatusGate1BHStarTwoAnchor.lean` | §21 new append-only status layer |
| `Gate1B/AxiomAuditGate1BHStarTwoAnchor.lean` | §22 axiom audit |
| `GATE1B_HSTAR_TWOANCHOR_SAFE_BANK_REPORT.md` | this report |

Existing banks preserved and reused unchanged: the punctured / product-Fourier
frame (`eM`, `eM_zero`, `full_char_sum`), the canonical R9/HNE bank, the V13
same-`q` / product-residue algebra, `ShiftTTStarLiteralSource`, the HSTAR
source-template bank and every previous status layer.  The new status layer
imports the previous layer and proves `previous_layer_preserved`.

`HSTAR-K0J0-V13-QK56-GRAM-LIFT45` is recorded in the ledger as
`notCurrentlyRequired` with the note "retired as an HSTAR provider:
source-ill-typed for the generated-Γ HSTAR packet.  **Not** a refutation of the
historical V13 finite algebra, which remains valid and untouched."  A kernel
theorem (`v13_provider_retired_not_refuted`) checks that this row is *not*
recorded as a refuted route.

---

## 1. Kernel-proved content (all `sorry`-free)

### Two-anchor physical source (§2)

`HStarTwoAnchorSource` carries the named physical variables
`g, e i, wp i, ell i, T i, pi i` with positivity fields, primality of both
Vaughan primes and both Ford primes, and the two **literal** anchors

```
g * e1 * wp1 * ell1 = T1 * pi1 + 2        (anchor1)
g * e2 * wp2 * ell2 = T2 * pi2 + 2        (anchor2)
```

The `+2` is never hidden in a weight.  Proved: `defect1_eq_two`,
`defect2_eq_two` (`C1 = C2 = 2`), the moduli `q i = g e i wp i` with
`q i ∣ T i π i + 2`, and `hStarTwoAnchorSource_nonempty` (explicit inhabitant
`g = 5`, `(e,wp,ℓ,T,π) = (1,7,1,11,3)` and `(1,2,1,4,2)`), so nothing quantified
over the source type is vacuous.

### Difference algebra (§3) and source-exact system (§5)

On raw integer configurations: `Hnum = T1π1 − T2π2`,
`quotDiff = e1wp1ℓ1 − e2wp2ℓ2`.  Proved

* `hnum_eq_g_mul_quotDiff` : anchors ⇒ `Hnum = g · quotDiff`;
* `anchors_imply_difference_system` : anchors ⇒ `∃ H, Hnum = gH ∧ quotDiff = H`;
* `hnum_eq_iff_quotDiff_eq` : for `g ≠ 0`, `Hnum = gH ↔ quotDiff = H`;
* `twoAnchor_iff_differenceSystem_with_anchor` :
  `anchor1 ∧ anchor2 ∧ quotDiff = H  ↔  Hnum = gH ∧ quotDiff = H ∧ C1 = 2`;
* `anchor2_of_differences_and_anchor1` : the second anchor follows from both
  difference lines plus the first `+2` anchor.

### Non-converse firewall (§4)

`differenceSystem_implies_common_defect` : the difference system gives
`C1 = C2` and nothing more.  `C1 = 2` is **not** derivable:
`differenceSystem_does_not_imply_physicalAnchors` exhibits the strictly
positive configuration

```
g = 1, e i = wp i = 1, ℓ1 = 5, ℓ2 = 3, T1 = T2 = 1, π1 = 5, π2 = 3, H = 2
```

with both difference lines satisfied and `C1 = C2 = 0 ≠ 2`; both anchors fail.
`differenceSystem_does_not_imply_defect_two` states the refutation directly.

### One-`T` specialisation (§6) and the one-`T`/two-`T` firewall (§7)

Namespace `OneT`: with `T1 = T2 = T`, `q i = g r i` and `T` a unit mod `g`,
`oneT_prime_congruence` gives `g ∣ π1 − π2`; after `π1 − π2 = g h`,
`oneT_length_relation` gives `r1ℓ1 − r2ℓ2 = T h`; `oneT_rigidity` packages both.

`twoT_congruence` : a general two-`T` physical source gives only
`g ∣ T1π1 − T2π2`.
`twoT_congruence_does_not_imply_prime_congruence` : the *actual physical
source* above (all four primes genuine) satisfies `T1π1 ≡ T2π2 (mod 5)` while
`π1 ≢ π2 (mod 5)`.  One-`T` rigidity may not be transported into the
pre-Cauchy Perron source.

### Cauchy firewall (§8)

Two distinct named objects, both constructed:

* `OneTCauchyMajorant Γ F = (∑‖Γ‖²)(∑‖F‖²)` with
  `sumV_norm_sq_le_majorant : ‖V‖² ≤ OneTCauchyMajorant`;
* `TwoTExactSquare Γ F = ∑_{T1,T2} Γ(T1) conj Γ(T2) F(T1) conj F(T2)` with
  `sumV_mul_conj_eq_twoTExactSquare : V · conj V = TwoTExactSquare`.

`oneTCauchyMajorant_ne_twoTExactSquare` : for `Γ = (1,−1)`, `F = (1,1)` the
exact square is `0` and the majorant is `4`.
`majorant_does_not_determine_exactSquare` : no function of the majorant can
recover the exact square.  **No theorem transports `Γ`-phase information
through the majorant.**

### `H = 0` router (§9)

`cross_dvd_of_coprime` : coprime `m1, m2` with `m1ℓ1 = m2ℓ2` give `m1 ∣ ℓ2` and
`m2 ∣ ℓ1`.  `hZero_impossible_of_short_length` : with `0 < ℓ2 < m1` this is
impossible (one inequality suffices); `hZero_impossible_of_short_lengths` is the
symmetric form as stated in the source.  `HZeroOffDiagonalCell` packages the
physical cell with the length separation as **explicit finite hypotheses**;
`hZeroOffDiagonalCell_impossible` and `not_nonempty_hZeroOffDiagonalCell` show it
has no inhabitant, and `hZero_two_anchor_source_impossible` specialises to the
physical two-anchor source at `H = 0`.  **No asymptotic scale inequality
(`m_i/ℓ_j ≥ x^{4/9−o(1)}`) is formalised anywhere.**

### Centred additive projector (§10) and two-copy zero mode (§11)

Ramanujan sum `c_q(h) = ∑_{a unit} e_q(−h a)` with `c_q(0) = φ(q)`; the
unit-sector principal model `unitPrincipal` of total mass `1`; the centred
projector `Δ_q(n) = 1_{n=−2} − P_q(n)` with

* `centeredProjector_total_mass_zero` : `∑_n Δ_q(n) = 0`;
* `centeredFourier_zero_eq_zero` : `Δ̂_q(0) = 0`;
* `eM_zero_sub_ramanujanSum_zero_div_totient` : the boxed target
  `e_q(0) − c_q(0)/φ(q) = 0`;
* `centeredFourier_eq_ramanujan_form` : `Δ̂_q(h) = e_q(−2h) − c_q(−h)/φ(q)`.

Two-copy: `twoCopyMode_eq_zero_of_second_zero`,
`centered_twoCopyMode_zero_zero`, `four_signed_pieces_cancel`
(`+1 −1 −1 +1 = 0` after factoring the common normalisation) and
`centered_four_pieces_cancel` for the literal `II, IP, PI, PP` pieces.  No
analytic estimate.

### Möbius-prime source (§12) and prime typing (§13)

`CleanSquarefreeCell` (`q = d·wp`, `wp` prime, `wp ∤ d`) with `μ(q) = −μ(d)`.
`moebius_common_g_cancel` : for `d i = g e i` with `g` squarefree and coprime to
each `e i`, `μ(d1)μ(d2) = μ(e1)μ(e2)` — the common `g`-sign appears squared.
`no_cancellation_in_residual_moebius` refutes any claim of cancellation in
`e1, e2`.  The repository's own `λ₃` is *not* redefined here; this module adds
only the cell-level Möbius algebra.

Prime typing: `PrimeRole` with two distinct constructors, separate types
`FordPrime` and `VaughanPrime` with their own role fields,
`value_does_not_determine_role`, `vaughan_not_dvd_g_of_gt` (`wp > g > 0 ⇒ wp ∤ g`)
and `no_cross_incidence` (`wp ∣ q1`, `wp ∤ gcd(q1,q2)` ⇒ `wp ∤ q2`).

### Finite `Λ♯` source (§14) and nonzero shift (§15)

`LambdaSharp E P w m = ∑_{e·wp = m, e ∈ E, wp ∈ P} μ(e) w(wp)` with an abstract
complex prime weight.  Proved: `lambdaSharp_support`, the deterministic
multiplicity bound `‖Λ♯(m)‖ ≤ τ(m)·W`, a finite Cauchy bound, and
`opened_shift_equation` : opening the source at shift `H` imposes
`e1wp1 − e2wp2 = H`.  Non-vacuity guard: `lambdaSharp_not_identically_zero`.
The cancellation itself and the mean-square input are the uninhabited
interfaces `LambdaSharpNonzeroShiftBound` and `LambdaSharpL2Input`; only the
deterministic consequence `shift_bound_of_interface` is proved, and only *given*
an argument of the interface type.

### Anchor-preserving covariance object (§16)

`AnchorPreservingCenteredCovariance S = Δ_{q1}(T1π1) · conj Δ_{q2}(T2π2)`, built
directly on the physical source.  `residue1_eq_neg_two`, `residue2_eq_neg_two`
prove that both residues are exactly `−2`, so the two `+2` projector conditions
are preserved by construction; `covariance_evaluated_at_neg_two` and
`factor i_eq` give the closed form; `norm_familyCovariance_le` is the
deterministic triangle bound for weighted finite families.
`covariance_source_not_freeHLine` forbids replacing the object by a free
`H`-line sum.

### Independent-`H` and single-line firewalls (§17, §18)

`AFactor`, `BFactor` are the two abstract `H`-energy factors.
`independentH_product_implies_common_defect` : a nonzero product enforces only
`C1 = C2`.  `independentHEnergy_not_physicalSource` and
`independentHEnergy_does_not_imply_anchors` : its support contains the
nonphysical countermodel.  `singleLineDelta_iff_common_defect` : the
eliminated-`H` line `T1π1 − T2π2 = g(e1wp1ℓ1 − e2wp2ℓ2)` is *exactly* `C1 = C2`;
`singleLineDelta_strictly_weaker` : it is implied by the anchors but does not
imply them.

---

## 2. Analytic interfaces — UNINHABITED

| interface | module | status |
|---|---|---|
| `LambdaSharpNonzeroShiftBound` | `HStarMobiusPrimeSource` | never inhabited |
| `LambdaSharpL2Input` | `HStarMobiusPrimeSource` | never inhabited |
| `HStarK0J0AnchorPreservingCovarianceBound` | `HStarAnchorPreservingAnalyticInterface` | never inhabited |
| `FM722AnchorPreservingQuadraticDivisorGeneratedSource` | `HStarAnchorPreservingAnalyticInterface` | never inhabited, stated only for generated families |

No axiom, no `sorry`, no default constructor, no instance.  Downstream results
(`single_source_bound`, `scaled_family_bound`, `shift_bound_of_interface`,
`fm722_bound_of_target`) are deterministic and take an argument of the interface
type.  Non-vacuity guards (`centeredProjector_neg_two_ne_zero`,
`lambdaSharp_not_identically_zero`) show the interfaces concern nonzero objects.

---

## 3. Build

* Each of the eleven new modules was built individually: **11/11 PASS**, zero
  errors, zero warnings, no `sorry` (verified by search).
* Repository-wide `lake build` still fails **exactly as before**, literally:

  ```
  error: no such file or directory (error code: 2)
    file: /workspace/request-project/RequestProject/FixedCertificateAlgebra.lean
  ```

  This is a PRE-EXISTING legacy failure.  Nothing was moved, renamed or deleted
  to conceal it.
* `lake build Gate1B` replays every new module successfully; the same 49 legacy
  targets fail on missing legacy files (`UniversalV8/BlockGram.lean`,
  `Gate1B/AdditiveCoordinate.lean`, …).  No new module appears in any failure
  list.

---

## 4. Axiom audit

`Gate1B/AxiomAuditGate1BHStarTwoAnchor.lean` runs `#print axioms` on **102**
principal declarations of this delta.  Result:

* 6 declarations depend on no axioms;
* 21 on `[propext]`;
* 9 on `[propext, Quot.sound]`;
* 66 on `[propext, Classical.choice, Quot.sound]`.

No `sorryAx`, no custom `axiom`, no `native_decide`, no `implemented_by`, no
`unsafe`, no `opaque` shortcut.

---

## FINAL BLOCK

TWO-ANCHOR PHYSICAL ALGEBRA:
KERNEL-PROVED.  Both `+2` anchors are literal fields; `C1 = C2 = 2`; the source
type is inhabited.

DIFFERENCE-SYSTEM FIREWALL:
KERNEL-PROVED.  Difference system ⇒ `C1 = C2` only; explicit positive
countermodel with `C1 = C2 = 0 ≠ 2`; `differenceSystem_does_not_imply_physicalAnchors`
banked.  The source-exact system is anchors ⇔ two difference lines + `C1 = 2`.

ONE-T / TWO-T FIREWALL:
KERNEL-PROVED.  One-`T` rigidity holds under a unit hypothesis mod `g`; the
two-`T` source gives only `T1π1 ≡ T2π2 (mod g)`, and an actual physical source
has `π1 ≢ π2 (mod g)`.

CENTERED ZERO MODE:
KERNEL-PROVED.  `e_q(0) − c_q(0)/φ(q) = 0`, `Δ̂_q(0) = 0`, and the two-copy
`+1 −1 −1 +1 = 0` cancellation.

H=0 ROUTER:
KERNEL-PROVED, conditional on explicit finite length hypotheses.  No asymptotic
scale inequality is formalised.

MOBIUS-PRIME SOURCE:
KERNEL-PROVED.  `μ(g e1) μ(g e2) = μ(e1) μ(e2)`; no cancellation claimed in
`e1, e2`; Ford and Vaughan primes are separate types.

SINGLE-LINE DELTA:
SUPERSEDED / INSUFFICIENT AS PHYSICAL SOURCE

INDEPENDENT-H FACTORIZATION:
INVALID AS PHYSICAL SOURCE

ANCHOR-PRESERVING COVARIANCE:
UNINHABITED ANALYTIC INTERFACE

CURRENT FORMAL FRONTIER:
The exact finite anchor-preserving centred covariance object is constructed and
its two `+2` conditions are kernel-proved; the only missing input is a bound for
it.

CURRENT RESEARCH FRONTIER:
HSTAR-K0J0-
PERRON-INTEGRATED-
SMALLG-
ANCHORPRESERVING-
CENTERED-MOBIUSPRIME-
COVARIANCE45

GLOBAL GATE1B:
OPEN

TWIN PRIME:
OPEN

BUILD:
11/11 new modules build individually, zero errors, zero warnings, no `sorry`.
Repository-wide `lake build` fails only on the PRE-EXISTING missing legacy file
`RequestProject/FixedCertificateAlgebra.lean`; `lake build Gate1B` fails only on
the same 49 pre-existing legacy targets.  No new module appears in any failure
list.

AXIOM AUDIT:
102 declarations audited; only `propext`, `Classical.choice`, `Quot.sound`
appear.  No `sorry`, no `sorryAx`, no custom axiom, no `unsafe`, no `opaque`,
no `native_decide`, no `implemented_by`.

STOP.
