# TWIN GATE1B R11 — FORMAL BANKING RUN REPORT

Append-only Lean delta.  Nothing pre-existing was edited, renamed or deleted.

## 1. New modules

| Module | Contents |
|---|---|
| `Gate1B/R11/VaughanCharts.lean` | cutoff truncations, four-lane Vaughan identity, `V*=2` specialization on odd `N`, chart-equivalence |
| `Gate1B/R11/Polytope611.lean` | 11-coordinate exponent polytope, `M ≤ 5/11`, uniform `6/11`, `L ≥ 2/11`, CARD5 chamber bounds, two counterexamples, Pascadi rational dictionary |
| `Gate1B/R11/CutoffConservation.lean` | `AT=D`, `KT=B`, `DK=X`, `AB=X` at exponent level and as real powers; hybrid `min` lemma |
| `Gate1B/R11/Reciprocity.lean` | reciprocity in `ℝ/ℤ` with explicit integer witness; exponential form at the fixed shift `2` |
| `Gate1B/R11/Bruhat.lean` | `det g = 1`; the SL₂ Bruhat factorisation; instantiation modulo an odd `c` |
| `Gate1B/R11/AffineParametrization.lean` | exact biconditional `t`-parametrization of `A·B + 2 = k·d` |
| `Gate1B/HilbertHMRD/Fourier.lean` | additive character on `ZMod s`, orthogonality, inversion, Parseval, `ℓ¹ ≤ √(φ(s))` |
| `Gate1B/HilbertHMRD/OperatorStability.lean` | `‖T ⊗ id_H‖ = ‖T‖` (both directions) |
| `Gate1B/HilbertHMRD/Core.lean` | the finite Hilbert packet, small-modulus branch, energy branch, interval corollary, full HMRD `min` |
| `Gate1B/R11/StatusBank.lean` | kernel-checked ledger; physical-caller firewall (uninhabited obligations) |
| `Gate1B/R11/AxiomAuditTwinGate1B.lean` | `#print axioms` for every principal theorem |

Existing modules reused, not modified: `Gate1B/R11/MobiusLogSplit.lean`,
`Gate1B/R11/LongMobius.lean`, `Gate1B/R11/Determinant.lean`,
`Universal/D0WP/AdditiveCharacterCore.lean`, `Universal/D0WP/ResidueEnergy.lean`.

## 2. Required output

```
VAUGHAN IDENTITY:                 KERNEL-PROVED
V*=2 MOBIUS-LOG:                  KERNEL-PROVED
FOUR-LANE = LONG-MOBIUS AT V=2:   KERNEL-PROVED   (literal equality; no mass lost)
POLYTOPE M<=5/11:                 KERNEL-PROVED
UNIFORM 6/11 GEOMETRY:            KERNEL-PROVED
PASCADI EXPONENT ARITHMETIC:      KERNEL-PROVED   (finite rational dictionary only)
LONG-MOBIUS REINDEXING:           KERNEL-PROVED
AB-kd=-2:                         KERNEL-PROVED
FOUR CROSS-GCDs:                  KERNEL-PROVED
AFFINE t-PARAMETRIZATION:         KERNEL-PROVED
KT=B CONSERVATION:                KERNEL-PROVED   (rational and real-power forms)
HYBRID MIN-LEMMA:                 KERNEL-PROVED
RECIPROCITY:                      KERNEL-PROVED   (ℝ/ℤ form and exponential form)
SL2 BRUHAT:                       KERNEL-PROVED   (exactly as claimed; no repair needed)
HILBERT-HMRD SMALL BRANCH:        KERNEL-PROVED
HILBERT-HMRD ENERGY BRANCH:       KERNEL-PROVED
FULL HILBERT-HMRD:                KERNEL-PROVED   (finite, abstract, min of the two branches)
TENSOR OPERATOR STABILITY:        KERNEL-PROVED   (both directions)
PHYSICAL HILBERT CALLER:          OPEN / NOT ATTEMPTED
R11:                              OPEN
GLOBAL GATE1B:                    OPEN
TWIN PRIME:                       OPEN
NO SORRY:                         YES
CUSTOM AXIOMS:                    NONE
LAKE BUILD:                       PASS for every new module (built individually);
                                  the repository-wide `lake build` still stops at the
                                  pre-existing baseline failures (missing
                                  `RequestProject/FixedCertificateAlgebra.lean`,
                                  `UniversalV8.BlockGram`, `Gate1A.Exponents`, …),
                                  unchanged by this delta.
```

## 3. Notes on the individual items

**§2–§4 Vaughan / `V*=2` / chart equivalence.**  `vaughan_identity` is an identity in the
commutative ring `ArithmeticFunction ℝ`, proved from `μ*ζ = 1` and `Λ*ζ = log`.  On odd `N`
lanes 1 and 3 vanish (`vTwo_lane_ledger`), lane 2 is the low Möbius–log block and lane 4 is
the long block, giving `vTwo_vaughan_eq_mobius_log_split`.  Both chart values are proved
equal to `Λ(N)`, so `FourLaneValue U 2 N = LongMobiusValue U N` is a literal equality.  No
analytic claim is made about either chart.

**§5 Polytope.**  `M+N+L = 1`, `M ≤ 5/11`, `1−M ≥ 6/11`, `L ≥ 2/11` follow from the ordering
and the normalisation alone.  The stronger `2/5 + (6/5)ε ≤ M` and `1/3 + (2/3)ε ≤ N` are
**not** consequences of the supplied CARD5 inequalities with a free `γ`: the module contains
two kernel-checked counterexamples (chamber conditions satisfied at `γ = 1`, but `M = 1/20`
resp. `N = 1/25`).  They are derivable exactly when the chamber parameter is pinned at
`γ ≤ 1/2 − ε`, which is carried explicitly as a hypothesis:
`M ≥ 1 − (6/5)γ` and `N ≥ (2/3)(1 − γ)` are the unpinned forms.

**§6 Pascadi margin.**  No analytic theorem is postulated.  `PascadiExponentConditions`
bundles only finite rational inequalities, and `pascadi_conditions_of_polytope` proves the
polytope supplies them at `θ = 7/32` (the recorded margin being `2θ = 7/16 < 6/11 ≤ 1−M`).

**§10 Conservation.**  Rational and `rpow` forms both proved; the hybrid `min` lemma is a
clean two-line exponent argument.

**§11 Reciprocity.**  The `ℝ/ℤ` identity is proved with the integer witness
`n = (A A' + k k' − 1)/(A k)` exhibited; the exponential identity follows by periodicity.
The shift is the fixed value `2`; nothing is averaged over the shift.

**§12 Bruhat.**  The claimed factorisation `g = U(λ A d⁻¹) D(d⁻¹) S U(B d⁻¹)` is confirmed
verbatim by the kernel — no sign or order convention differs.  Proved over an arbitrary
commutative ring with the inverses supplied as data, then instantiated in `ZMod c` for odd
`c` (where `−2` is automatically a unit).

**§13–§16 Hilbert-HMRD.**  Everything is finite and abstract.  The pairing is taken linear
in the first slot, matching the source convention (`inner ℂ (v w) (u d)` in Mathlib's
convention).  The small branch uses the kernel-proved Fourier `ℓ¹` cost `√(φ(s))` in the
normalisation `f̂(t) = s⁻¹ ∑_x f(x) e_s(−t x)`; the constant is exactly `√(φ(s))`, nothing is
hidden.  The energy branch pushes both variables to inverse residue classes, applies the
Hilbert-valued `√s` bilinear bound for the reciprocal kernel — obtained from the scalar
bound through the tensor-stability theorem, which is therefore load-bearing — and a
Hilbert-valued residue-class energy bound.  The interval corollary reproduces the shape
`√(s(1+D/s)(1+W/s)) A₂ B₂` using the banked counting lemma `card_residue_class_le`.  The
full theorem is the `min` of the two branches.  The effective modulus `s = r/gcd(A,r)` is
the separately banked `Universal.D0WP.ac_effective_modulus`; the Hilbert layer takes `s` to
be the effective modulus already.

**§17 Firewall.**  `PhysicalHilbertCaller`, `VectorMobiusPhysicalBound` and
`GlobalModeLedger` are recorded as explicit propositions and are never inhabited.  The only
theorem that mentions the caller is the conditional transport lemma
`hmrd_applies_of_physicalCaller`: *if* a target were exhibited as a finite Hilbert packet,
*then* the proved HMRD bound would apply.  There is no theorem asserting
`Ω(kd−2) → reciprocal HMRD packet`, no matched-Hecke Hilbert–Chowla postulate, and nothing
approaching R11, global Gate 1B or twin primes.

## 4. Axiom audit

`Gate1B/R11/AxiomAuditTwinGate1B.lean` prints axioms for all principal theorems.  Every one
depends only on `[propext, Classical.choice, Quot.sound]`.  A machine search over the new
layer finds no `sorry`, no `admit`, no `axiom`, no `native_decide` and no
`@[implemented_by]`.
