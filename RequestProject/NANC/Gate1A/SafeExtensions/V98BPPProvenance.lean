/-
# NANC Gate 1A v9.8 — provenance discipline, the BPP finite compiler and the
external analytic interface

## Sections 2 and 12 — conservative provenance

`Provenance` distinguishes `leanProved`, `externallyPublished`,
`sourceInspectedNotProved`, `sourceSpecificAnalyticPass`, `assumedSourceReading`
and `interfaceOpen`.  A source reading is never turned into a Lean proof: the
predicate `Provenance.isLeanEvidence` is true for `leanProved` only, and
`provenance_not_lean_evidence` proves that the other five do not qualify.

## Section 11 — the BPP finite compiler

The finite implication

    participation `P` + row count `S` + pair codegree `D`
      ⟹  E_off ≤ (D·S/P²) · T_abs

is the already proved `V94.familyEnergy_of_participation`; it is *reused*.
What is added is

* `Gate1ABPPPrimeParticipationInput`, the narrowest external analytic interface
  (band-limited plateau participation), with an explicit provenance field and a
  citation string;
* `primeParticipation_familyEnergy`, the deterministic compiler from that
  interface to the family-energy inequality;
* the exact rational exponent bookkeeping `S = R^{1+o}`, `P = R^{3/4-o}`,
  `D = X^o` ⟹ ratio `R^{-1/2+o}`, and the one root `R^{-1/4+o}`;
* the vertex margins `V1 = 1/72`, `V2 = 1/24`, `V3 = 1/32`, re-exported from the
  frozen `V94.BPPBudget` ledger (retracted `R^{-1}` route untouched);
* `directGateComparison_of_margin`, which converts the exponent margin into the
  actual required comparison `M · R^{-1/4} ≤ H`.

No inhabitant of the external interface is constructed and no axiom is added.
-/
import Mathlib
import RequestProject.NANC.Gate1A.SafeExtensions.BPPBudget
import RequestProject.NANC.Gate1A.SafeExtensions.BPPFamilyEnergy
import RequestProject.NANC.Gate1A.SafeExtensions.PrimeParticipationFinite

namespace TwinPrimeProject.NANC.Gate1A.V98

open Finset
open TwinPrimeProject.NANC.Gate1A.V94

/-! ## 1. Conservative provenance -/

/-- Provenance classes, matching the conservative discipline of the NANC
Gate 0/2 bank. -/
inductive Provenance
  /-- Proved in Lean, kernel checked, in this repository. -/
  | leanProved
  /-- A published theorem of the literature, not formalised here. -/
  | externallyPublished
  /-- Read off the authoritative source document; not proved. -/
  | sourceInspectedNotProved
  /-- A source-specific analytic pass, verified by hand in the source. -/
  | sourceSpecificAnalyticPass
  /-- An assumed reading of the source. -/
  | assumedSourceReading
  /-- An open interface with no inhabitant. -/
  | interfaceOpen
  deriving DecidableEq, Repr

/-- Only `leanProved` is Lean evidence. -/
def Provenance.isLeanEvidence : Provenance → Bool
  | .leanProved => true
  | _ => false

/-- **Provenance firewall.**  A source reading, a published theorem, a
source-specific analytic pass, an assumed reading and an open interface are all
*not* Lean evidence. -/
theorem provenance_not_lean_evidence :
    Provenance.isLeanEvidence .externallyPublished = false ∧
    Provenance.isLeanEvidence .sourceInspectedNotProved = false ∧
    Provenance.isLeanEvidence .sourceSpecificAnalyticPass = false ∧
    Provenance.isLeanEvidence .assumedSourceReading = false ∧
    Provenance.isLeanEvidence .interfaceOpen = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. The external BPP analytic interface -/

/-- **The narrowest external analytic input of the BPP route.**  It packages the
band-limited plateau participation statement: for a continuous-envelope
participation datum, the plateau of every state has at least `P/c₀` rows.  Its
five ingredients (uniform smoothness of `F_X(r/R)`, Fourier truncation at degree
`R^{1/4}`, a Bernstein plateau of length `R^{3/4}`, primes in intervals shorter
than `R^{3/4}`, and deletion of `X^{o(1)}` fixed states) are *not* formalised in
this repository; the interface records them with an explicit provenance and
citation, and has no inhabitant here. -/
structure Gate1ABPPPrimeParticipationInput (Row State : Type*) [Fintype Row] [Fintype State]
    [DecidableEq Row] where
  /-- The continuous-envelope participation datum (v9.4 bank). -/
  envelope : ParticipationEnvelope Row State
  /-- The participation parameter. -/
  P : ℝ
  /-- Positivity. -/
  P_pos : 0 < P
  /-- The plateau lower bound — the external analytic statement. -/
  plateau_lower_bound : ∀ X, P ≤ envelope.c0 * ((envelope.plateau X).card : ℝ)
  /-- Where the statement comes from. -/
  provenance : Provenance
  /-- The exact citation / source pointer. -/
  citation : String

namespace Gate1ABPPPrimeParticipationInput

variable {Row State : Type*} [Fintype Row] [Fintype State] [DecidableEq Row]

/-- **The deterministic compiler.**  The external participation input plus a
pair-codegree bound gives the controlling family-energy inequality
`E_off ≤ (D·S/P²)·T_abs`, with `S = #rows`. -/
theorem primeParticipation_familyEnergy (I : Gate1ABPPPrimeParticipationInput Row State)
    (A : State → ℝ) (hA : ∀ X, A X ≤ I.envelope.Menv X) (hA0 : ∀ X, 0 ≤ A X)
    (D Eoff : ℝ) (hD : 0 ≤ D) (hcodeg : Eoff ≤ D * (∑ X, A X) ^ 2) :
    Eoff ≤ (D * (Fintype.card Row : ℝ) / I.P ^ 2) *
      totalAbsEnergy (fun r X => |I.envelope.c r X|) := by
  refine familyEnergy_of_participation (fun r X => |I.envelope.c r X|) A I.P D Eoff I.P_pos hD
    (fun r X => abs_nonneg _) hA0 ?_ hcodeg
  intro X
  refine le_trans ?_ (I.envelope.participation_of_plateau A hA hA0 X)
  exact mul_le_mul_of_nonneg_right (I.plateau_lower_bound X) (hA0 X)

/-- **Hostile guard: the external interface cannot inhabit itself.**  With an
empty plateau the required lower bound is false, so the interface is a genuine
analytic restriction and not a definitional consequence of its own data. -/
theorem participationInput_not_self_inhabiting :
    ∃ (E : ParticipationEnvelope (Fin 1) (Fin 1)) (P : ℝ), 0 < P ∧
      ¬ (∀ X, P ≤ E.c0 * ((E.plateau X).card : ℝ)) := by
  refine ⟨{ c := fun _ _ => 0
          , Menv := fun _ => 0
          , Menv_nonneg := fun _ => le_rfl
          , upper := fun _ _ => by simp
          , c0 := 1
          , c0_pos := one_pos
          , plateau := fun _ => ∅
          , plateau_lower := by intro X r hr; simp at hr }, 1, one_pos, ?_⟩
  intro h
  have := h 0
  simp at this
  linarith

end Gate1ABPPPrimeParticipationInput

/-! ## 3. Exact exponent bookkeeping for the controlling BPP route -/

/-- `D = X^{o(1)}`: codegree exponent. -/
def codegreeExp : ℚ := 0

/-- `S = R^{1+o(1)}`: row-count exponent (in `R`). -/
def rowCountExp : ℚ := 1

/-- `P = R^{3/4-o(1)}`: participation exponent (in `R`). -/
def participationExp : ℚ := 3 / 4

/-- The controlling family-energy exponent `D·S/P²`. -/
def familyEnergyExp : ℚ := codegreeExp + rowCountExp - 2 * participationExp

/-- **`R^{-1/2+o(1)}` family energy.** -/
theorem familyEnergyExp_eq : familyEnergyExp = -(1 / 2) := by
  norm_num [familyEnergyExp, codegreeExp, rowCountExp, participationExp]

/-- **Exactly one root**: the family-energy exponent halves to `-1/4` at the
variance/operator level, in exact rational arithmetic. -/
theorem oneRoot_exponent : familyEnergyExp / 2 = -(1 / 4) := by
  norm_num [familyEnergyExp, codegreeExp, rowCountExp, participationExp]

/-- The real-analytic form of the one root, re-exported from the v9.4 bank. -/
theorem oneRoot_real {R : ℝ} (hR : 0 < R) :
    Real.sqrt (R ^ (-(1 : ℝ) / 2)) = R ^ (-(1 : ℝ) / 4) :=
  oneRoot_energy_to_operator hR

/-! ## 4. Vertex margins (Section 13), re-exported from the frozen ledger -/

/-- `V₁` margin `1/72`. -/
theorem directMargin_V1 : bppGateMargin bppV1.1 bppV1.2 = 1 / 72 := bpp_gate_margin_V1

/-- `V₂` margin `1/24`. -/
theorem directMargin_V2 : bppGateMargin bppV2.1 bppV2.2 = 1 / 24 := bpp_gate_margin_V2

/-- `V₃` margin `1/32`. -/
theorem directMargin_V3 : bppGateMargin bppV3.1 bppV3.2 = 1 / 32 := bpp_gate_margin_V3

/-- All three controlling margins are strictly positive. -/
theorem directMargins_pos :
    0 < bppGateMargin bppV1.1 bppV1.2 ∧ 0 < bppGateMargin bppV2.1 bppV2.2 ∧
      0 < bppGateMargin bppV3.1 bppV3.2 := bpp_gate_margins_pos

/-- The `U^{-2}` recombination-error margins `1/18, 1/18, 1/24`. -/
theorem directErrorMargins_U2 :
    errorMarginU2 bppV1.1 = 1 / 18 ∧ errorMarginU2 bppV2.1 = 1 / 18 ∧
      errorMarginU2 bppV3.1 = 1 / 24 := errorMarginU2_vertices

/-- **The margin really is the required comparison.**  If `M = X^{μ}`,
`R = X^{a}` and `H = X^{η}` with `X > 1` and `η ≥ μ − a/4`, then
`M · R^{-1/4} ≤ H`. -/
theorem directGateComparison_of_margin (X mu a eta : ℝ) (hX : 1 < X)
    (hmargin : mu - a / 4 ≤ eta) :
    (X ^ mu) * (X ^ a) ^ (-(1 : ℝ) / 4) ≤ X ^ eta := by
  have hX0 : (0 : ℝ) < X := lt_trans zero_lt_one hX
  have hpow : (X ^ a) ^ (-(1 : ℝ) / 4) = X ^ (a * (-(1 : ℝ) / 4)) := by
    rw [← Real.rpow_mul hX0.le]
  rw [hpow, ← Real.rpow_add hX0]
  exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)

end TwinPrimeProject.NANC.Gate1A.V98
