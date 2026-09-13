# GATE 1B / R11 — EP-M2 ROW REALISATION / JCORE DETERMINANT / CLEAN SUPPORT / COMBINED CONDUCTOR

Append-only run. **No pre-existing file was edited, renamed, weakened or deleted** (not even the
designated aggregators: the new modules are picked up by the library glob, so `Bank.lean` and the
older `AxiomAudit.lean` files were left untouched).

---

## PREVIOUS BANK

PRESERVED. CanonicalRootSync, TerminalRamanujan and ReciprocityBG are unchanged; the canonical
cut, `J2ResidualCenteredBound`, `EPM2Bound`, `EPM2TopBound`, `LowRamanujanBudget`,
`CrossTermBudget`, and the countermodel `epM2RowIdentification_load_bearing` all keep their
original statements.

## FILES ADDED

Under `Gate1B/R11/Frontier/CanonicalRootSync/TerminalRamanujan/ReciprocityBG/`:

* `RowIdentification.lean` (B13) — the row realisation and the canonical `j = 2` attachment;
* `RowFixture.lean` (B14) — a kernel-computed nondegenerate instance of that realisation.

Under `…/ReciprocityBG/JCore/`:

* `Core.lean` (J1) — the JCORE variables, masks and moment; square expansion with two copies;
* `RationalFrequency.lean` (J2) — the equal/unequal rational-frequency split;
* `Determinant.lean` (J3) — `Δ = n b ũ − ñ a u` and the exact frequency-difference identity;
* `MomentSplit.lean` (J4) — exact equal/off split, support of the off part = `{Δ ≠ 0}`;
* `CleanSupport.lean` (J5) — clean support `(z, vṽ) = 1` and the exact clean/overlap split;
* `CrossPhase.lean` (J6) — the three local phases and the exact cross-phase factorisation;
* `Conductor.lean` (J7) — exact source/core conductor lowering, complete-period identity;
* `CombinedConductor.lean` (J8) — CRT shift, `q_eff`, `A_eff`, one shifted reciprocal;
* `FactorisationData.lean` (J9) — the pairwise-coprime block record for `q_eff`;
* `Owners.lean` (J10) — the three JCORE analytic propositions and the reassembly;
* `Bridge.lean` (J11) — `JCoreBound → EPM2TopBound → EPM2Bound → J2ResidualCenteredBound`;
* `Firewall.lean` (J12) — second-factor firewall and the non-claims;
* `AxiomAudit.lean` (J13) — `#print axioms` for every principal theorem of this run.

Plus this report.

## FILES MODIFIED

None (other than this new report file).

## LAKE BUILD

PASS — full repository, all default targets.

## AXIOM AUDIT

PASS — every principal theorem of the new directories depends only on
`propext`, `Classical.choice`, `Quot.sound`. A scan of the new files finds no `sorry`, `admit`,
custom `axiom`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`.

---

## epM2RowIdentification

**PROVED — as a realisation** (`epM2RowIdentification_rowDataClosed`).

Note the exact status, since it is the only honest reading: the banked countermodel
`epM2RowIdentification_load_bearing` shows the sub-bridge is *false for general realisation
data*. It is therefore closed the only way it can be closed — by exhibiting explicit canonical
data on which it is a theorem. The data are:

* packet = chart image under `idx = Nat.pair`;
* canonical row kernel = the **divisor form** of the EP-M2 row,
  `K(⟨e,s⟩) = ∑_{z ∈ Z, e ∣ sz+2} β₅(z) · F((sz+2)/e)`, `F(N) = ∑_{d ∣ N} λ(d)`;
* EP-M2 row value = the **Ramanujan form** of the same row, centered,
  `R(e,s) = ∑_{z ∈ Z, e ∣ sz+2} β₅(z) ∑_{0<q≤Q_max} a(q) c_q((sz+2)/e) − c`.

The arithmetic content is `rowCoefficientIdentification` (divisor form = Ramanujan form), which
is the banked finite Ramanujan expansion applied at every row point; the centering constant is
matched to the packet kernel mean in the closed instance. The six suggested sub-identities are
all discharged (index, source, mask, kernel, centering, coefficient) — none was left as a
hypothesis.

## epM2Realisation

**PROVED** for the same instance (`epM2Realisation_rowDataClosed`), via the banked
`epM2Realisation_of_subBridges`: all seven sub-bridges hold, and the identification is an exact
equality of the canonical centered `j = 2` residual family with the EP-M2 row moment family
(no bound, no domination, no renaming).

## CANONICAL J2 ATTACHMENT

ESTABLISHED for the realised data: `j2_of_epM2Bound_rowDataClosed` and
`j2_of_terminal_parts_rowDataClosed` carry an EP-M2 budget to the *existing* canonical owner
`J2ResidualCenteredBound` with **no exact bridge left between EP-M2 and canonical `j = 2`**.
`EPM2Bound` and `EPM2TopBound` are **not** inhabited. Nondegeneracy: for the fixture
(`I = (0,3]×(0,1]`, `Z = {1}`, `β₅ ≡ 1`, `W ≡ 1`, `E₀ = {1}`, `S₀ = {1,2}`) the realised family is
the nonzero constant `−5`.

---

## JCORE OBJECT

Defined: outer variables `(e, z, k)`, core variables `(n, u, v)` with `n : ℤ` signed, second copy
`(ñ, ũ, ṽ)` appearing only through the square expansion `jMoment = jExpand`. Masks are explicit
predicates (`CoreAdmissible`, `OuterAdmissible`); the coefficient family is abstract.
`masks_do_not_give_cross_coprimality` proves the masks do **not** yield `(u,ṽ)=1` or `(ũ,v)=1`,
and neither is used anywhere.

## RATIONAL-FREQUENCY SPLIT

PROVED: under `(n,uv)=1`, `(ñ,ũṽ)=1`, `n/(uv) = ñ/(ũṽ) ↔ n = ñ ∧ uv = ũṽ`, signs included.
Distinct factorisations with the same product stay in the equal class
(`equalRationalFrequency_of_same_product`).

## DETERMINANT

PROVED: `n/(uv) − ñ/(ũṽ) = Δ/([v,ṽ]·u·ũ)` with `Δ = n b ũ − ñ a u`, `v = ha`, `ṽ = hb`,
`[v,ṽ] = hab`.

## DELTA = 0

PROVED: `Δ = 0 ↔ EqualRationalFrequency`; hence `Δ ≠ 0` on the unequal-frequency owner
(`delta_ne_zero_of_unequal`), and the off-diagonal part is exactly the `{Δ ≠ 0}` part
(`jOff_support_delta`).

## CLEAN SUPPORT

Defined exactly as `(z, vṽ) = 1`; proved a genuine restriction (`cleanSupport_not_automatic`).
No analytic claim about the complement.

## SOURCE/CORE OVERLAP OWNER

`SourceCoreOverlapBudget` — ordinary proposition, never inhabited. The decomposition
`jOff = jOffClean + jOffOverlap` is an exact identity of signed sums, and
`SourceCoreOverlapBudget + JCoreOffCleanBound ⇒ JCoreOffBound` is proved. No monotonicity under
deleting signed terms is used; `deleting_terms_not_monotone` records why.

## CROSS-PHASE

PROVED in `ℚ/ℤ` and for the exponential: the phase difference decomposes into the source residue
factor `e_z(A_s ē)`, the second reciprocal CRT factor `e_c(B_c · (z+ek)⁻¹)` and the determinant
factor `e(−2Δ/(eDz·ℓ·u·ũ))`, and `detPhase = (−2/(eDz))·(n/(uv) − ñ/(ũṽ))` exactly. Each local
inverse is used only modulo its own modulus, and each local phase is proved independent of the
choice of inverse representative. The decomposition of the phase difference into the three named
parts is carried as an explicit hypothesis, never fabricated.

## SECOND-FACTOR FIREWALL

PROVED (finite fixture, `z = 3`, `c = 5`, `k = 1`, `e ∈ {1,4}`): the source factors agree while
the second reciprocal factors differ as exponentials. Source-factor cancellation alone does not
give JCORE phase cancellation.

## SOURCE CONDUCTOR

PROVED: `e_z(A ē) = e_m((A/g) ē)`, `g = (A,z)`, `m = z/g`, exactly (rational and exponential
forms). No Weil-type estimate.

## CORE CONDUCTOR

PROVED: same lemma applied to `g_c = (B_c,c)`, `c_eff = c/g_c` (`crtPhase_lower`).

## COMBINED CONDUCTOR

PROVED in the clean small-label model: the CRT shift `t₀` with `m ∣ t₀`, `t₀ ≡ w (mod c)` exists
(`exists_crt_shift`), and the product of the two reciprocal phases is the single shifted
reciprocal at the inverse of `e + t₀`. The label reduction `z + ek ≡ k(e + z k̄) (mod c)` is
proved. The general-label case is **not** claimed: it is isolated as exactly one explicit
proposition `CombinedConductorRealisation`, never inhabited.

## q_EFF

`qEff m c = m·c`, `aEff A B m c = A·c + B·m`, both exact.

## FACTORISATION DATA

`QEffFactorisation`: a finite record with source / common-core / two private-core / small-label
blocks and all pairwise coprimalities; exact multiplication, coprimality and divisibility facts
proved. No Wu–Xi / Shen / Bourgain–Garaev estimate is formalised, assumed or named.

---

## JCORE EQUAL OWNER

`JCoreEqualBudget` — ordinary proposition, open, never inhabited.

## JCORE CLEAN-OFF OWNER

`JCoreOffCleanBound` — the single terminal JCORE analytic owner, open, never inhabited, proved
load-bearing (`jCore_needs_clean_owner`).

## JCORE REASSEMBLY

PROVED: `JCoreEqualBudget + SourceCoreOverlapBudget + JCoreOffCleanBound ⇒ JCoreBound`.

## JCORE → EP-M2 BRIDGE

`JCoreBound + jCoreMomentRealisation ⇒ EPM2TopBound` is proved; combined with the banked cross
and low budgets it gives `EPM2Bound`, and, for the realised row data, the canonical
`J2ResidualCenteredBound`. `jCoreMomentRealisation` is the one exact identification still missing
on this route, and is proved load-bearing.

---

## CANONICAL CUT

Unchanged (coarse cut): `rootChartRealisation`, `rankDecompositionRealisation`,
`j2CenteredSplitRealisation`, `canonicalRootErrorBudget`, `branchBound1/3/4/5`, `principalBudget`,
`J2ResidualCenteredBound` — ten nodes. Nothing was removed: no theorem-backed recomputation
discharges any of them, and canonical R11 closure is **not** claimed.

## EP-M2 CUT

Refined. Before this run the EP-M2 route cost `epM2RowIdentification` (exact) plus
`EPM2TopBound`, `CrossTermBudget`, `LowRamanujanBudget`. After this run, on the realised data,
the exact bridge is **discharged**, so the EP-M2 refined cut is the three analytic nodes
`EPM2TopBound`, `CrossTermBudget`, `LowRamanujanBudget`. This refines the route; it does **not**
shrink the canonical coarse cut, because `J2ResidualCenteredBound` is still owned (the EP-M2 route
replaces one open analytic owner by three).

## JCORE CUT

`jCoreMomentRealisation` (exact, open) + `JCoreEqualBudget` + `SourceCoreOverlapBudget` +
`JCoreOffCleanBound` + `CrossTermBudget` + `LowRamanujanBudget`. Additionally, the general-label
combined conductor is open as `CombinedConductorRealisation` (not on the minimal cut of the
budget DAG: the clean small-label case is proved).

---

## R11 STATUS

OPEN.

## HSTAR STATUS

OPEN.

## GATE1B STATUS

OPEN.

## TWIN-PRIME CLAIM

NONE. No parity or twin-prime statement is made anywhere in this run.

---

## MINIMUM EXACT OPEN BRIDGE

`jCoreMomentRealisation` (EP-M2 terminal moment family = JCORE moment family). The former minimum
exact bridge `epM2RowIdentification` is discharged on the realised data.

## MINIMUM ANALYTIC OWNER

`JCoreOffCleanBound` — the clean off-diagonal (unequal-frequency, `(z,vṽ)=1`) JCORE budget.

## NEXT ARISTOTLE TARGET

Prove `jCoreMomentRealisation` by the same realisation method used here for the row bridge:
construct the JCORE moment from the EP-M2 terminal row data (chart, masks, coefficient family) so
that the identification is a theorem, and then attack `JCoreOffCleanBound` through the proved
determinant / clean-support / combined-conductor algebra.
