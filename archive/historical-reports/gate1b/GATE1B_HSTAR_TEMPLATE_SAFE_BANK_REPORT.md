# GATE 1B — HSTAR SOURCE-TEMPLATE SAFE BANK REPORT

Append-only extension of the existing Gate 1B canonical / HNE safe bank with the
SOURCE-EXACT HSTAR `k = 0`, `J = ∅` algebra, Vaughan convolution typing, the
determinant shell, the finite nuclear compiler algebra and the family-scope
firewalls.

Nothing analytic is proved. Nothing is promoted.

---

## FILES ADDED

| File | Content |
|---|---|
| `Gate1B/VaughanLambda3P3Bridge.lean` | §2–§3: λ₃/P₃ convolution typing, the λ₃ ≠ P₃ firewall, the exact switched divisor pairing and its finite reindexing |
| `Gate1B/HStarK0J0VaughanCentering.lean` | §4, §14: exact Vaughan identity `Λ = P₁ − P₂ + P₃`, generic centering against an abstract comparison sequence, shifted finite-pairing form, comparison-role firewall |
| `Gate1B/HStarK0J0SourceGrammar.lean` | §5–§6: the HSTAR `k = 0`, `J = ∅` source type (source DATA only) and the u/v source-factor firewall |
| `Gate1B/HStarK0J0DeterminantShell.lean` | §9: `d·p·r = m·n + 2 → q·ℓ − u·v = 2` and the exact modulus-coefficient reindexing |
| `Gate1B/HStarTemplateFamily.lean` | §10: the template type and the template **family** type, with the one-versus-family data firewalls |
| `Gate1B/HStarFiniteNuclearCompiler.lean` | §7, §8, §12: the nuclearization certificate interface, the deterministic finite nuclear compiler, raw finite energy algebra and the energy firewall |
| `Gate1B/Gate1BFamilyScopeFirewall.lean` | §11, §13: scalar vs family-uniform scope firewall and the Gate 1A scope firewall |
| `Gate1B/HStarTemplateUniformityInterface.lean` | §11, §15: the template-uniformity and Ford-to-Gate census interfaces, plus the deterministic compilers they feed |
| `Gate1B/CurrentStatusGate1BHStarTemplates.lean` | §15: the new status layer (imports the old status layer unchanged) |
| `Gate1B/AxiomAuditGate1BHStarTemplates.lean` | §16: `#print axioms` for all 78 public declarations of this delta |
| `GATE1B_HSTAR_TEMPLATE_SAFE_BANK_REPORT.md` | this report |

## FILES MODIFIED

`Main.lean` — **imports appended only**, at the end of the file. Nothing was
removed, reordered or edited.

## FILES DELETED

none.

---

## NEW KERNEL-PROVED ALGEBRA

**λ₃ / P₃ convolution typing** (no second `λ₃` is defined; the repository's own
`lambda3Sw` from `Gate1B/CanonicalSwitchedAggregate.lean` is reused).

* `lambda3AF_eq_highHighCoefficient` — λ₃(U,V) **is** the high-high modulus
  coefficient `μ_{>U} * Λ_{>V}`.
* **BOXED** `lambda3_conv_zeta_eq_highHighP3` — `λ₃ * ζ = highHighP3`, where
  `highHighP3 = (μ_{>U} * Λ_{>V}) * ζ` is the hard Vaughan `P₃`.
* `λ₃ = P₃` is **not** formalised, and is refuted:
  `lambda3_ne_highHighP3` with the explicit countermodel `U = V = 1`, `n = 8`
  (`highHighCoefficient 1 1 8 = −log 2`, `highHighP3 1 1 8 = −2 log 2`);
  `exists_af_conv_zeta_ne_self` (convolution with `ζ` is not the identity);
  `no_bridge_modulus_to_hard` (type-level counterguard: no value-preserving map
  from `HighHighModulusCoefficient` to `HardVaughanP3` sends the λ₃ wrapper to
  the P₃ wrapper).

**Switched finite reindexing.**

* `switchedClassPairing K g q = ∑_{2 ≤ q·r ≤ K+2} g(q·r − 2)` — fixed shift `2`,
  never averaged.
* `switched_sum_eq_pairSum`, `switched_pairing_reindex`:
  `∑_q f(q) C_g(q) = ∑_N (f * ζ)(N) g(N − 2)`.
* `switched_pairing_eq_highHighP3`: with `f = λ₃`, the `N`-side carries
  `highHighP3` — precisely the identification whose λ₃-for-P₃ substitution was
  the previously audited false formula.

**Vaughan centering algebra.**

* `exactVaughanIdentityR` — `Λ = P₁ − P₂ + P₃` in the arithmetic-function
  convolution ring (real coefficients), with
  `vaughanP3R = (μ_{>U} * Λ_{>V}) * ζ` and
  `vaughanP3R_eq_coefficient_conv_zeta` recording the same typing on the real
  side.
* `centering_identity` (generic, any additive commutative group),
  `vonMangoldt_centering`, `vonMangoldt_centering_apply`:
  `Λ − b = P₃ − (b − P₁ + P₂)` for an **arbitrary** comparison sequence `b`.
* `shifted_pairing_centering` — the fixed-shift finite-pairing form.

**HSTAR first-parent source / type distinctions.**

* `HStarK0J0Source`: `k = 0`, `J = ∅`, `g_∅ = 1` enforced by fields, plus the
  two source kinds, block-depth bounds, support intervals, discrete endpoint
  branches and a **finite** Perron parameter index. Source DATA only.
* `HStarK0J0Source.uKind_ne_vKind`, `hStarSourceKind_u_ne_v`.
* `uBase_ne_vBase`, `no_common_source_family`, `uBase_eq_zero_of_not_squarefree`,
  `vBase_ne_zero` — `μ(e)·twist(e)` versus `twist(e)` are genuinely different
  families (countermodel `e = 4`).
* `uBlock_primes_nodup`, `vBlock_support_not_strictly_ordered` — the strict
  prime-support ordering lives on the u-side only.

**Determinant shell (HSTAR-K0J0-DETERMINANT-SHELL).**

* `determinant_shell`, `determinant_shell_raw`, `determinant_shell_nat`,
  `shell_of_determinant`: `d·p·r = m·n + 2 ⟺ q·ℓ − u·v = 2` for `q = d·p`,
  `ℓ = r`, `u = m`, `v = n`.
* `sum_divisorPair_reindex`, `modulus_coefficient_reindex` — the exact
  modulus-coefficient reindexing at finite/algebraic level.

**Template and family types.**

* `HStarK0J0Template` (branch, source factors, dyadic supports, Perron
  decoration, `Y1`, `Y2`, determinant-shell data, expected-term data with the
  pinned shift `2`) and `HStarTemplateFamily`.
* `exists_family_not_singleton`, `member_does_not_determine_family` — one
  template is not a family, and one member does not determine the family.

**Deterministic finite nuclear compiler.**

* `nuclear_compiler`: `(∑ᵢ‖cᵢ‖ ≤ Nuclear) → (∀ i, ‖Tᵢ‖ ≤ PacketBound) →
  ‖∑ᵢ cᵢTᵢ‖ ≤ Nuclear·PacketBound`, with abstract nonnegative real budgets.
* `family_recombination_bound`, `parent_bound_of_certificate`,
  `parent_bound_of_certificates` — the specialisations through the certificate
  interfaces.

**Raw energy / codegree finite algebra.**

* `rawSourceEnergy_mono` (support restriction can only decrease energy),
  `rawSourceEnergy_unitTwist` (unit-modulus twists preserve the L² norm),
  `finite_cauchy_energy` (finite Cauchy–Schwarz compiler),
  `rawMultiplicativeEnergy_mono`, `card_divisorsAntidiagonal_le`
  (bounded-depth product-representation multiplicity).

**Scope firewalls.**

* `scalar_closed_but_not_family_uniform`,
  `scalar_does_not_imply_family_uniform` — scalar Gate 1B closure of the
  recombination does **not** propositionally imply the family-uniform template
  bound (explicit cancellation countermodel).
* `scalar_of_family_uniform`, `family_uniform_of_forall` — the two explicit
  bridges, with all hypotheses visible.
* `forgetWD_not_injective`, `no_physical_weight_from_template`,
  `rawEnergy_ne_gate1A_covarianceEnergy` — Gate 1A carries the common physical
  `W_D` field, the HSTAR template type does not, no map recovers `W_D` from a
  template, and the two energies are different definitions with different
  values. No analytic no-go theorem is claimed.

**Comparison role firewall.** `LocalRoughComparison` and `GlobalComparison` are
distinct wrapper types (`localRough_not_identified_with_global`); the only
transport, `centering_transport_of_bridge`, carries the bridge hypothesis
explicitly. No authoritative analytic comparison sequence is chosen.

---

## OPEN INTERFACES (never inhabited, never promoted)

* `HStarK0J0NuclearizationCertificate` — finite discrete template index, finite
  Perron surrogate index, coefficient of each template, exact decomposition
  identity, total nuclear bound. **No inhabitant is constructed anywhere in this
  bank and no axiom asserts one.** The continuous Perron nuclearization is
  marked in the source as external analytic input; only a finite-nuclear
  surrogate/compiler interface is formalised.
* `HStarTemplateUniformityCertificate` — the template-uniform Gate 1B bound.
  Never supplied for the physical HSTAR evaluation and the physical Gate 1B
  target. (For arbitrary parameters the structure is of course satisfiable; the
  open content is the physical instance, which is exactly the frontier label.)
* `FordToGateSourceCensus` — exhaustiveness of the finite family with respect to
  the upstream source production. Never supplied.
* Generic switched expected-term identification, and the downstream HSTAR
  remainder: recorded as open rows in the status layer, with no Lean content
  claiming them.

---

## SCALAR-vs-FAMILY FIREWALL

`Gate1BClosedScalarTBU (T B U) := |T| ≤ B ∧ U = 0` is a name-disjoint restatement
of the legacy scalar shape (the legacy declaration lives in a top-level tree
outside every library glob of this repository and is untouched and unimported).

`Gate1BFamilyUniformBound F T B := ∀ i : Fin F.size, ‖T i‖ ≤ B`
(with the synonym `HStarTemplateGate1BBound`) literally quantifies over every
template of the supplied finite family.

The two are **not** identified. The countermodel is
`samplePairFamily` with packet values `(10, −10)` and unit coefficients: the
recombination is `0`, so scalar closure holds with bound `1`, while the
family-uniform bound with the same constant fails at index `1`. Consequently

```
¬ ∀ F T B, Gate1BClosedScalarTBU ‖familyRecombination F T‖ B 0 →
      Gate1BFamilyUniformBound F T B
```

is a kernel theorem (`scalar_does_not_imply_family_uniform`). Passage from the
family bound to a scalar bound requires the explicit nuclear bridge
(`scalar_of_family_uniform`).

---

## BUILD

* **New modules, built individually: 10 / 10 PASS**, zero errors, zero
  `sorry`, zero warnings in the final state:
  `Gate1B.VaughanLambda3P3Bridge`, `Gate1B.HStarK0J0VaughanCentering`,
  `Gate1B.HStarK0J0SourceGrammar`, `Gate1B.HStarK0J0DeterminantShell`,
  `Gate1B.HStarTemplateFamily`, `Gate1B.HStarFiniteNuclearCompiler`,
  `Gate1B.Gate1BFamilyScopeFirewall`,
  `Gate1B.HStarTemplateUniformityInterface`,
  `Gate1B.CurrentStatusGate1BHStarTemplates`,
  `Gate1B.AxiomAuditGate1BHStarTemplates`.
* **Default repository build: PRE-EXISTING FAILURE, unchanged.** Literal error:

  ```
  error: no such file or directory (error code: 2)
    file: /workspace/request-project/RequestProject/FixedCertificateAlgebra.lean
  ```

  The broader `Gate1B` library target additionally reports 49 legacy targets
  failing on missing legacy files (`UniversalV8.BlockGram`, `Gate1A.Exponents`,
  `Gate1B.AdditiveCoordinate`, …). These failures pre-date this delta; **no new
  module appears in any failure list**, and no legacy file was moved or renamed
  to hide them.

---

## AXIOM AUDIT

`Gate1B/AxiomAuditGate1BHStarTemplates.lean` runs `#print axioms` on all 78
public declarations of this delta (70 theorems of the eight mathematical modules
plus the 8 invariants of the status layer). Every one depends on a subset of

```
propext, Classical.choice, Quot.sound
```

No `sorry`, no `sorryAx`, no custom `axiom`, no `native_decide`, no
`implemented_by`, no `opaque` proof shortcut, no `unsafe`.

---

## CURRENT FORMAL FRONTIER

The last kernel-proved step is the deterministic reassembly compiler
`parent_bound_of_certificates`: given a nuclearization certificate for the HSTAR
`k = 0`, `J = ∅` parent and a *family-uniform* bound for the very packets it
decomposes into, the parent bound `Nuclear · PacketBound` follows. Both inputs
are explicit arguments and neither is supplied.

## CURRENT RESEARCH FRONTIER

```
HSTAR-K0J0-SOURCETEMPLATE-GATE1B-UNIFORMITY45 : OPEN
```

## GLOBAL GATE1B

OPEN / NOT PROMOTED.

## TWIN PRIME

OPEN / NOT PROMOTED.

STOP.
