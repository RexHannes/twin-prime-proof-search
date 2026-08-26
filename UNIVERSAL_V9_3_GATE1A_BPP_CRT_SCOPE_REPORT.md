# UNIVERSAL v9.3 — GATE 1A BPP / CRT SCOPE AUDIT

Scope-and-audit pass between the v9.2 corrected-source line and the v9.4 corrected BPP
bank. This pass produced **no new axioms and no new analytic claims**; its output is the
scope determination that the v9.4 files then formalise.

---

## A. Regression / environment

Lean `v4.28.0`, pinned Mathlib, `lake build` = 8435 jobs, 0 errors. No file modified, no
theorem weakened.

## B. What the CRT scope audit established

1. **Shift convention.** The corrected quotient kernel reproduces both authoritative
   repository factors only under `c = -2` with kernel `e_C(-h s)`
   (`correctedQuotient_authoritative_match`); the `c = +2` convention matches the
   `q`-factor alone (`correctedQuotient_match_c_two`). Any BPP argument phrased in the
   `+2` convention is therefore out of scope until the sign is pinned at the source.

2. **Normalisation.** `Uq q H = q / H` (`Uq_div_q`), and the reciprocal form is a genuine
   countermodel (`Uq_ne_reciprocal_of_ne`). Budget arithmetic that used `H/q` is out of
   scope.

3. **Coordinate change is ℓ²-neutral.** `oldNewQCoordinate_l2Preserved` and
   `oldNewQCoordinate_card_preserved` show that energy-level statements survive the
   correction, while `oldNew_rootSets_differ` shows root-level statements do not. This is
   the exact scope boundary between what could be re-exported and what had to be reproved.

4. **BPP participation is an interface, not a theorem.** No prime-participation /
   Huxley–Guth–Maynard input is proved in Lean. It is carried as the structure field
   `ParticipationEnvelope` / `PrimeParticipationCertificate`
   (`PrimeParticipationFinite.lean`), and only the *finite consequences* are proved
   (`participation_of_plateau`, `sup_le_envelope`, `envelopeMass_le_of_participation`,
   `familyEnergy_of_participation`).

5. **Retraction.** The direct R1 weighted-family promotion previously used as a closure
   step is **retracted**. `V94Retractions.lean` records
   `directR1WeightedFamilyPromotion_retracted`,
   `directR1WeightedFamilyPromotion_not_proved`, and an explicit finite countermodel
   `directR1_promotion_countermodel` (plus its general form): pairwise-orthogonal rows
   have coherent energy strictly below the naive natural energy, so the promotion is
   false as a closure step.

## C. Consequences for the ledger

| previously quoted margin | status |
|---|---|
| `1/12`, `1/9`, `5/48` | **RETRACTED** (`obsolete_margins`, `ledgers_not_interchangeable`) |
| corrected `V1 = 1/72`, `V2 = 1/24`, `V3 = 1/32` | proved exactly in ℚ (`bpp_gate_margin_V1/V2/V3`) |

The two ledgers are proved *not* interchangeable, so no silent upgrade is possible.

## D. Audit result

```
CRT SIGN CONVENTION      : PINNED (c = -2), reported
NORMALISATION Uq         : PROVED q/H, reciprocal refuted
COORDINATE CHANGE        : ℓ²-NEUTRAL (proved)
BPP PARTICIPATION        : INTERFACE OPEN (no Lean proof, no axiom)
DIRECT R1 PROMOTION      : RETRACTED with countermodel
OLD MARGIN LEDGER        : RETRACTED
GATE 1A                  : OPEN
FULL TYPE II / TWIN PRIMES : NOT DECLARED
```
