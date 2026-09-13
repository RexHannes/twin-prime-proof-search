# GATE 1B / R11 — EP-M2 REALISATION + RECIPROCITY / LOW-FREQUENCY FORMAL SYNC

**Mode:** append-only. The canonical root bank and the terminal-Ramanujan bank are preserved
verbatim; no pre-existing file was edited, renamed, weakened or deleted. No `sorry`, no `admit`,
no custom axiom, no `native_decide`, no `unsafe`, no `opaque`. Every theorem below is
kernel-checked and audited in
`Gate1B/R11/Frontier/CanonicalRootSync/TerminalRamanujan/ReciprocityBG/AxiomAudit.lean`
(only `propext`, `Classical.choice`, `Quot.sound`).

New subdirectory:
`Gate1B/R11/Frontier/CanonicalRootSync/TerminalRamanujan/ReciprocityBG/`.

---

## 1. Status table

| Label | Status | Location |
|---|---|---|
| `epM2Realisation` sub-bridge decomposition (`epM2Realisation_of_subBridges`) | **PROVED** | `Realisation.lean` |
| `sourceWeightRealisation`, `normalisationRealisation` for the canonical instance | **PROVED** | `Realisation.lean` |
| `epM2RowIdentification` (the single remaining exact identification) | **OPEN_INPUT** (exact, not analytic) | `Realisation.lean` |
| `epM2RowIdentification_load_bearing` (countermodel) | **COUNTERMODEL** | `Realisation.lean` |
| CRT lift congruences `J ≡ 2z⁻¹ (u)`, `J ≡ 2z'⁻¹ (v)`, `J ≡ −s_* (C)` | **PROVED** | `CRTPhase.lean` |
| CRT uniqueness `C u v ∣ J₁ − J₂` | **PROVED** | `CRTPhase.lean` |
| exact phase factorisation in `ℚ/ℤ` (and its exponential form) | **PROVED** | `CRTPhase.lean` |
| `C`-factor firewall (dropping the `C`-part changes the phase) | **COUNTERMODEL** | `CRTPhase.lean` |
| reciprocity `A/b + B/a ≡ 1/(ab) (mod 1)` | **PROVED** | `Reciprocity.lean` |
| `Cᵢ = eᵢLᵢ`, `(Lᵢ, e/eᵢ) = 1` extraction algebra | **PROVED** | `Reciprocity.lean` |
| source relation removes `e` from the reciprocal denominator | **PROVED** | `Reciprocity.lean` |
| source-relation firewall (no reduction without `e ∣ z'−z`) | **COUNTERMODEL** | `Reciprocity.lean` |
| exact Möbius provenance `λ(a₀u) = μ(a₀)·alloc` | **PROVED** | `MobiusProvenance.lean` |
| exact Möbius provenance with square part `λ(a₀b₀²u) = μ(a₀)·alloc(κ₁,κ₂)` | **PROVED** | `MobiusProvenance.lean` |
| exact allocation counting `#alloc = τ(a₀)τ(u) = d₂(a₀u)` | **PROVED** | `ComplementCost.lean` |
| `∑_{m≤R} d₂(m)/m ≤ (∑_{m≤R} 1/m)²` and `∑_{m≤R} 1/m ≤ 1+log R` | **PROVED** | `ComplementCost.lean` |
| `ComplementAssemblyBudget` from the allocation splitting bound | **PROVED (conditional on the stated finite splitting hypothesis)** | `ComplementCost.lean` |
| exact dual-frequency split `Full = Low + High`, moment square/cross split | **PROVED** | `DualFrequency.lean` |
| non-monotonicity under deleting frequencies | **COUNTERMODEL** | `DualFrequency.lean` |
| `LowDualBourgainGaraevBound` | **OPEN_INPUT / EXTERNAL_ANALYTIC** (never inhabited, not an axiom) | `LowFrequencyOwner.lean` |
| `LowDualBourgainGaraevBound ⇒ LowRamanujanBudget` | **PROVED** | `LowFrequencyOwner.lean` |
| `HighDualJointAverageBound` | **OPEN_INPUT / EXTERNAL_ANALYTIC** (never inhabited, not an axiom) | `HighFrequencyOwner.lean` |
| atom bound ⇏ joint average (averaging firewall) | **COUNTERMODEL** | `HighFrequencyOwner.lean` |
| power-budget rational inequalities (`1/40000 < 1/20000`, `k=4` gap, banked wedge point) | **PROVED (exponent arithmetic only)** | `PowerBudget.lean` |
| bridge `dual owners + realisation ⇒ J2ResidualCenteredBound` | **PROVED (conditional)** | `Bridge.lean` |
| `J2ResidualCenteredBound`, `EPM2TopBound` | **still OPEN** | unchanged |
| twin primes / parity | **NOT CLAIMED** | — |

No Bourgain–Garaev theorem is created, assumed, approximated or axiomatised anywhere.

---

## 2. Dependency DAG

```
        exact dictionary (unconditional, kernel-proved)
        ────────────────────────────────────────────────
        CRTPhase:  J_modEq_u / J_modEq_v / J_modEq_C / shiftedJ_unique
                   phase_factorisation (ℚ/ℤ) → phase_factorisation_exp
        Reciprocity: reciprocity_mod_one, eComp_mul_Lcomp, coprime_Lcomp,
                     source_relation_reduces_denominator
        MobiusProvenance: lam_eq_divisors, sum_divisors_coprime_split,
                          lam_mobius_provenance, lam_mobius_provenance_sq
        ComplementCost: allocCount_eq_d2, sum_d2_div_le_harmR_sq,
                        complementAssemblyBudget_of_split
        DualFrequency: dual_row_split, momentOf_split

        analytic owners (open propositions, never inhabited)
        ────────────────────────────────────────────────────
        LowDualBourgainGaraevBound      HighDualJointAverageBound    CrossTermBudget (banked)
                 │                                │                        │
                 │ lowDualBudget_of_bg            │ epM2TopBound_of_high    │
                 ▼                                ▼                        ▼
        LowRamanujanBudget              EPM2TopBound            (banked arrow)
                 └──────────────┬───────────────────┴────────────────────┘
                                ▼   epM2Bound_of_dual_owners
                            EPM2Bound
                                │   + epM2Realisation
                                ▼
                    J2ResidualCenteredBound   (canonical owner — STILL OPEN)

        epM2Realisation  ⇐ epM2Realisation_of_subBridges ⇐
            indexSetRealisation ∧ chartInjectivity ∧ maskRealisation
          ∧ sourceSupportRealisation ∧ sourceWeightRealisation (PROVED for the canonical instance)
          ∧ normalisationRealisation (PROVED for the canonical instance)
          ∧ epM2RowIdentification   ← THE ONE REMAINING EXACT IDENTIFICATION
```

Open blockers: `epM2RowIdentification` (exact), `LowDualBourgainGaraevBound` (external
analytic), `HighDualJointAverageBound` (external analytic), `CrossTermBudget` (banked, open).

---

## 3. What was newly kernel-proved this run

1. **EP-M2 realisation opened up.** `epM2Realisation` is no longer a single unanalysed bridge:
   it is now the conjunction of seven explicit sub-bridges, and the implication
   "all sub-bridges ⇒ `epM2Realisation`" is kernel-proved. For the canonical instance
   `ofCanonical`, two of them are discharged by construction and the three chart conditions are
   bookkeeping, leaving exactly one genuinely arithmetic identification,
   `epM2RowIdentification` (centered canonical kernel = EP-M2 row value), proved load-bearing by
   a finite countermodel.
2. **Exact CRT phase normalisation** at the congruence level, including uniqueness of the lift,
   the phase factorisation in the additive circle, its exponential form, and the firewall
   showing the `C` contribution may not be dropped.
3. **Reciprocity and the exit of the large common factor `e`** from the reciprocal denominator,
   as an exact rational identity driven by the source relation `z' − z = e k`, with the
   firewall showing the reduction fails without that relation. **No analytic saving is stated.**
4. **Exact Möbius provenance** of the complement allocation, with sharp intervals, oddness and
   coprimality retained, in the general form `J = a₀b₀²` (the square part is proved to be forced
   into both factors).
5. **Complement-assembly cost**: exact allocation counting plus the kernel-proved harmonic
   inequalities, giving `∑_{m≤R} #alloc(Hm)/(Hm) ≤ (d₂(H)/H)(1+log R)²` from the finite
   splitting hypothesis.
6. **Dual-frequency split** with its exact moment square/cross decomposition, and the
   non-monotonicity countermodel.
7. **Low/high frequency owners** as ordinary open propositions with all surrounding implications
   proved, and the **averaging firewall**: a fixed-frequency atom bound is strictly weaker than
   the joint average (explicit witness).
8. **Power-budget arithmetic** as pure rational inequalities, with an explicit theorem that they
   close no analytic owner.

---

## 4. Ledger

* **Current strongest safe (unconditional) content:** the exact arithmetic dictionary — CRT
  phase normalisation, phase factorisation mod 1, reciprocity and `e`-exit, Möbius provenance
  (including the square part), allocation counting and the harmonic assembly inequality, and the
  dual-frequency split with its moment decomposition.
* **Current strongest conditional theorem:**
  `j2_of_subBridges_and_dual_owners` — the canonical `j = 2` owner follows from
  (i) the chart sub-bridges plus `epM2RowIdentification`, (ii) `LowDualBourgainGaraevBound`,
  (iii) `HighDualJointAverageBound`, (iv) the banked `CrossTermBudget`.
* **Exact next missing audit:** `epM2RowIdentification` — the identification of the centered
  canonical `j = 2` kernel with the EP-M2 row value at each chart point. It is the unique
  remaining *exact* (non-analytic) gap below EP-M2.
* **Unchanged:** canonical cut, `J2ResidualCenteredBound` OPEN, `EPM2TopBound` OPEN, R11 OPEN,
  Gate1B OPEN, HSTAR OPEN, no twin-prime claim, no parity claim.
