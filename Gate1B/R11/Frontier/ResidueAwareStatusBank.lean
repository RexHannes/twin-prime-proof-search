/-
# Gate1B / R11 / Frontier : residue-aware status bank, firewalls and current frontier

Append-only ledger of the residue-aware / generated-grammar delta.  Nothing pre-existing is
edited, renamed or weakened: `R_hi` and `R_newcrit` remain in the bank as historical coordinates.

Contents:

* **§22 Disconnected-hypergraph firewall** — a finite counterexample: a source whose dependency
  hypergraph is disconnected (a product of singleton nonconstant factors) but whose ordinary
  highest-order interaction `Q_old W` is *not* zero.
* **§23 mod-3 / mod-5 firewall** — the unit function space modulo `3` has dimension `2` and the
  two-function span `{1, χ₃}` exhausts it, while modulo `5` the space has dimension `4` and the
  analogous two-function span does *not* exhaust it.  Hence the mod-3 derived caller does not
  automatically generalise to mod 5.  (No impossibility theorem for a mod-5 analytic treatment
  is asserted.)
* **§24 Status taxonomy** — the evidence levels, with every `kernelProved` row re-ascribed to an
  actual theorem of this layer, so a regression breaks the build.
* **§25 The current frontier object** — `residueAwareHistorical_open_frontier`.  No open
  proposition is inhabited anywhere in this layer.
-/
import Gate1B.R11.Frontier.HistoricalFordGrammarInterface

namespace Gate1B.R11.Frontier

open Finset TwinPrimeProject.Gate1BV11

/-! ## 1. The disconnected-hypergraph firewall -/

/-- A nonconstant single-coordinate factor. -/
def cmFactor : Fin 2 → ℚ := fun y => if y = 0 then 1 else -1

/-- A source which is a product of singleton nonconstant factors: its dependency hypergraph is
disconnected (no edge joins the two coordinates). -/
def cmSource : (∀ _ : Fin 2, Fin 2) → ℚ := fun x => cmFactor (x 0) * cmFactor (x 1)

/-- **Disconnected-hypergraph firewall.**  A disconnected dependency hypergraph does **not**
imply that the ordinary highest-order interaction vanishes: for the product source above,
`Q_old` acts as the identity and the top interaction equals `1` at the corner point. -/
theorem disconnected_hypergraph_firewall :
    ResidueProj.Qold (α := fun _ : Fin 2 => Fin 2) [0, 1] cmSource (fun _ => 0) = 1 := by
  simp [ResidueProj.Qold, ResidueProj.subP, ResidueProj.binAvg, ResidueProj.coordAvg,
    cmSource, cmFactor, Fin.sum_univ_two]

/-- The firewall in the form used downstream: there is a product source (disconnected hypergraph)
whose ordinary top projection is not identically zero. -/
theorem disconnected_does_not_kill_top_interaction :
    ∃ (f g : Fin 2 → ℚ) (W : (∀ _ : Fin 2, Fin 2) → ℚ),
      (∀ x, W x = f (x 0) * g (x 1)) ∧
        ResidueProj.Qold (α := fun _ : Fin 2 => Fin 2) [0, 1] W ≠ fun _ => 0 := by
  refine ⟨cmFactor, cmFactor, cmSource, fun _ => rfl, ?_⟩
  intro h
  have := congrFun h (fun _ => 0)
  rw [disconnected_hypergraph_firewall] at this
  norm_num at this

/-! ## 2. The mod-3 / mod-5 firewall -/

/-- The mod-5 quadratic character, as an exact rational-valued function. -/
def chi5 (n : ℕ) : ℚ :=
  if n % 5 = 1 ∨ n % 5 = 4 then 1 else if n % 5 = 2 ∨ n % 5 = 3 then -1 else 0

/-- Functions on the units modulo `3` form a `2`-dimensional space. -/
theorem finrank_units_mod3 : Module.finrank ℚ ((ZMod 3)ˣ → ℚ) = 2 := by
  rw [Module.finrank_fintype_fun_eq_card]
  decide

/-- Functions on the units modulo `5` form a `4`-dimensional space. -/
theorem finrank_units_mod5 : Module.finrank ℚ ((ZMod 5)ˣ → ℚ) = 4 := by
  rw [Module.finrank_fintype_fun_eq_card]
  decide

/-- **The two-function span suffices modulo 3**: every function on the unit residues mod `3` is
`c₀ + c₁ χ₃`. -/
theorem mod3_unit_span (v : ℕ → ℚ) :
    ∃ c0 c1 : ℚ, ∀ a ∈ ({1, 2} : Finset ℕ), v a = c0 + c1 * chi3 a := by
  refine ⟨(v 1 + v 2) / 2, (v 1 - v 2) / 2, ?_⟩
  intro a ha
  fin_cases ha <;> norm_num [chi3] <;> ring

/-- **The two-function span fails modulo 5**: the indicator of the residue `1` is not of the
form `c₀ + c₁ χ₅` on the unit residues mod `5`. -/
theorem mod5_unit_two_function_span_fails :
    ∃ v : ℕ → ℚ, ¬ ∃ c0 c1 : ℚ, ∀ a ∈ ({1, 2, 3, 4} : Finset ℕ), v a = c0 + c1 * chi5 a := by
  refine ⟨fun n => if n = 1 then 1 else 0, ?_⟩
  rintro ⟨c0, c1, h⟩
  have h1 := h 1 (by decide)
  have h4 := h 4 (by decide)
  norm_num [chi5] at h1 h4
  linarith

/-- Hence the mod-3 derived caller does **not** automatically generalise to mod 5. -/
theorem mod3_to_mod5_not_automatic :
    (∀ v : ℕ → ℚ, ∃ c0 c1 : ℚ, ∀ a ∈ ({1, 2} : Finset ℕ), v a = c0 + c1 * chi3 a)
      ∧ ¬ (∀ v : ℕ → ℚ, ∃ c0 c1 : ℚ, ∀ a ∈ ({1, 2, 3, 4} : Finset ℕ), v a = c0 + c1 * chi5 a) := by
  refine ⟨mod3_unit_span, ?_⟩
  obtain ⟨v, hv⟩ := mod5_unit_two_function_span_fails
  exact fun h => hv (h v)

/-! ## 3. The status taxonomy -/

/-- The evidence level of a row of the residue-aware bank. -/
inductive EvidenceLevel
  /-- Proved in Lean and checked by the kernel. -/
  | kernelProved
  /-- True conditionally on an explicitly stated analytic input carried as a hypothesis. -/
  | conditionalAnalytic
  /-- An external analytic theorem, not formalised here. -/
  | externalAnalytic
  /-- Backed by a certificate object which is defined but not inhabited. -/
  | certificateBacked
  /-- Analysed and retired as a closing mechanism. -/
  | retiredNonclosing
  /-- Open. -/
  | openRow
  /-- Not entered. -/
  | notEntered
  deriving DecidableEq, Repr

/-- Rows of the residue-aware / generated-grammar bank. -/
inductive ResidueAwareRow
  | modulusLiftingAlgebra
  | localPrincipalCorrection
  | logSplit
  | mod3SelectorAlgebra
  | mod3DerivedCaller
  | directResidueFirewall
  | projectionIdempotence
  | q3AbsorbsQold
  | residueAwareTelescoping
  | noDoubleCharge
  | rlocTop3Definition
  | rlocTop3AnalyticBound
  | freshPrimeGrammarConvolution
  | amplitudeRecursion
  | variationRecursion
  | zeroExtensionCost
  | evaluationPointFirewall
  | disconnectedGateFirewall
  | mod3Mod5Firewall
  | threeFactorSelectedOwner
  | pascadiRectangular
  | mod3CenteredCaller
  | localPrincipalAnalytic
  | realFordGrammarCertificate
  | historicalWeightedPushforward
  | q3ProvenanceResidual
  | ordinaryLocalTop
  | rHiHistorical
  | rNewcritHistorical
  | R11
  | globalGate1B
  | hstar
  | twinPrime
  deriving DecidableEq, Repr

open EvidenceLevel ResidueAwareRow in
/-- The status assignment of the residue-aware bank. -/
def residueAwareStatus : ResidueAwareRow → EvidenceLevel
  | modulusLiftingAlgebra => kernelProved
  | localPrincipalCorrection => kernelProved
  | logSplit => kernelProved
  | mod3SelectorAlgebra => kernelProved
  | mod3DerivedCaller => kernelProved
  | directResidueFirewall => kernelProved
  | projectionIdempotence => kernelProved
  | q3AbsorbsQold => kernelProved
  | residueAwareTelescoping => kernelProved
  | noDoubleCharge => kernelProved
  | rlocTop3Definition => kernelProved
  | rlocTop3AnalyticBound => openRow
  | freshPrimeGrammarConvolution => kernelProved
  | amplitudeRecursion => kernelProved
  | variationRecursion => kernelProved
  | zeroExtensionCost => kernelProved
  | evaluationPointFirewall => kernelProved
  | disconnectedGateFirewall => kernelProved
  | mod3Mod5Firewall => kernelProved
  | threeFactorSelectedOwner => kernelProved
  | pascadiRectangular => externalAnalytic
  | mod3CenteredCaller => externalAnalytic
  | localPrincipalAnalytic => externalAnalytic
  | realFordGrammarCertificate => openRow
  | historicalWeightedPushforward => openRow
  | q3ProvenanceResidual => openRow
  | ordinaryLocalTop => retiredNonclosing
  | rHiHistorical => retiredNonclosing
  | rNewcritHistorical => openRow
  | R11 => openRow
  | globalGate1B => openRow
  | hstar => openRow
  | twinPrime => openRow

/-! ### Re-ascription of the `kernelProved` rows

Each `bank_*` below is a type ascription of a theorem actually proved in this layer, so the
kernel re-checks that the claimed status matches a proof. -/

/-- MODULUS-LIFTING IDENTITY: KERNEL-PROVED. -/
theorem bank_modulus_lifting {h d : ℕ} (hcop : Nat.Coprime h d) (n : ℕ) :
    deltaSel h n * centeredSel d n = centeredSel (h * d) n + LocalPrincipalCorrection h d n :=
  modulus_lift_identity hcop n

/-- LOCAL PRINCIPAL CORRECTION (not erased by lifting): KERNEL-PROVED. -/
theorem bank_local_principal_correction :
    ∃ h d n : ℕ, Odd h ∧ Nat.Coprime h d ∧ LocalPrincipalCorrection h d n ≠ 0 :=
  modulus_lift_does_not_erase_localPrincipalCorrection

/-- LOGARITHM SPLIT: KERNEL-PROVED. -/
theorem bank_log_split (n h d : ℕ) (hh : 0 < h) (hd : 0 < d) :
    Real.log (((n : ℝ) + 2) / d) = Real.log (((n : ℝ) + 2) / ((h : ℝ) * d)) + Real.log h :=
  log_split_shift n h d hh hd

/-- MOD-3 SELECTOR ALGEBRA: KERNEL-PROVED. -/
theorem bank_mod3_selector (b : ℕ → ℚ) (a p R : ℕ) (ha : a = 1 ∨ a = 2) (hp : p % 3 ≠ 0)
    (hR : R % 3 ≠ 0) :
    indMod3 a p * b R = bRes b (3 - a) R + I3 (p * R) * (bRes b a R - bRes b (3 - a) R) :=
  mod3_selector_identity b a p R ha hp hR

/-- MOD-3 DERIVED CALLER (via modulus lifting): KERNEL-PROVED. -/
theorem bank_mod3_derived_caller {d : ℕ} (hcop : Nat.Coprime 3 d) (n : ℕ) :
    I3 n * centeredSel d n = centeredSel (3 * d) n + LocalPrincipalCorrection 3 d n :=
  mod3_caller_via_modulus_lifting hcop n

/-- DIRECT-RESIDUE FIREWALL: KERNEL-PROVED. -/
theorem bank_direct_residue_firewall :
    ¬ ∀ (S : Finset ℕ) (c : ℕ → ℚ),
        MeanZeroOn S c → MeanZeroOn (S.filter (fun n => n % 3 = 1)) c :=
  restricted_residue_not_automatically_meanZero

/-- `Q₃ Q_old = Q₃`: KERNEL-PROVED. -/
theorem bank_q3_qold {ι : Type} [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
    {res : ∀ i, α i → ℕ} {l : List ι} (hl : l.Nodup) (W : (∀ i, α i) → ℚ) :
    ResidueProj.Q3 res l (ResidueProj.Qold l W) = ResidueProj.Q3 res l W :=
  ResidueProj.Q3_Qold hl W

/-- RESIDUE-AWARE TELESCOPING: KERNEL-PROVED. -/
theorem bank_residue_aware_telescoping {ι : Type} [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] {res : ∀ i, α i → ℕ} (l : List ι) (W : (∀ i, α i) → ℚ) :
    (fun x => ResidueProj.Qold l W x - ResidueProj.Q3 res l W x)
      = ResidueProj.telescope res l W :=
  ResidueProj.Qold_sub_Q3_eq_telescope l W

/-- FRESH-PRIME GRAMMAR CONVOLUTION: KERNEL-PROVED. -/
theorem bank_fresh_prime_convolution (f g : ℕ → ℂ) {p R : ℕ} (hp : p.Prime) (hR : R ≠ 0)
    (hpR : ¬ p ∣ R) :
    dconv f g (p * R) = ∑ e ∈ R.divisors, (f (p * e) * g (R / e) + f e * g (p * R / e)) :=
  dconv_fresh_prime f g hp hR hpR

/-- GRAMMAR AMPLITUDE RECURSION: KERNEL-PROVED. -/
theorem bank_amplitude_recursion (r : ℕ) (c : ℂ) (f g : GenExpr) :
    ampBudget r (.add f g) ≤ ampBudget r f + ampBudget r g
      ∧ ampBudget r (.mul f g) ≤ ampBudget r f * ampBudget r g
      ∧ ampBudget r (.smul c f) ≤ ‖c‖ * ampBudget r f
      ∧ ampBudget r (.conv f g) ≤ (2 : ℝ) ^ r * (ampBudget r f * ampBudget r g) :=
  ⟨ampBudget_add_le r f g, ampBudget_mul_le r f g, ampBudget_smul_le r c f,
    ampBudget_conv_le r f g⟩

/-- EVALUATION-POINT FIREWALL: KERNEL-PROVED. -/
theorem bank_evaluation_point_firewall :
    ∃ (E : GenExpr) (l : List ℕ), E.Admissible
      ∧ pathVar l (fun p => semExpr E p) = 0
      ∧ pathVar l (fun p => semExpr E (p + 2)) ≠ 0 :=
  unshifted_variation_does_not_imply_shifted

/-- DISCONNECTED-GATE FIREWALL: KERNEL-PROVED. -/
theorem bank_disconnected_gate_firewall :
    ∃ (f g : Fin 2 → ℚ) (W : (∀ _ : Fin 2, Fin 2) → ℚ),
      (∀ x, W x = f (x 0) * g (x 1)) ∧
        ResidueProj.Qold (α := fun _ : Fin 2 => Fin 2) [0, 1] W ≠ fun _ => 0 :=
  disconnected_does_not_kill_top_interaction

/-- MOD3 → MOD5 AUTOMATIC EXTENSION: REJECTED (kernel-proved refutation of the span step). -/
theorem bank_mod3_mod5_firewall :
    ¬ (∀ v : ℕ → ℚ, ∃ c0 c1 : ℚ, ∀ a ∈ ({1, 2, 3, 4} : Finset ℕ), v a = c0 + c1 * chi5 a) :=
  mod3_to_mod5_not_automatic.2

/-! ## 4. The current frontier object -/

/-- The frontier record of the residue-aware / historical layer. -/
structure ResidueAwareFrontier where
  /-- The ordinary local-top coordinate, superseded by the residue-aware one. -/
  ordinaryLocalTop : EvidenceLevel
  /-- The modulo-3 removed component, controlled at external analytic scope. -/
  mod3RemovedComponent : EvidenceLevel
  /-- The current exact residual `R_loc-top,3`. -/
  rLocTop3 : EvidenceLevel
  /-- The generated grammar, at the declared finite algebra scope. -/
  generatedGrammar : EvidenceLevel
  /-- The historical realisation obligation. -/
  historicalRealisation : EvidenceLevel
  /-- Whether a major new Type-II necessity has been established. -/
  majorNewTypeIINecessity : Bool
  /-- The status of `R11`. -/
  r11 : EvidenceLevel

open EvidenceLevel in
/-- **The current frontier**: the ordinary local top is superseded, the modulo-3 removed
component is controlled only at external analytic scope, `R_loc-top,3` is the current open
residual, the generated grammar is kernel-proved at the declared finite algebra scope, the
historical realisation is open, no major new Type-II necessity is established, and `R11` is
open. -/
def residueAwareHistorical_open_frontier : ResidueAwareFrontier where
  ordinaryLocalTop := retiredNonclosing
  mod3RemovedComponent := externalAnalytic
  rLocTop3 := openRow
  generatedGrammar := kernelProved
  historicalRealisation := openRow
  majorNewTypeIINecessity := false
  r11 := openRow

/-- No open row of the frontier is tagged proved. -/
theorem frontier_open_rows_not_proved :
    residueAwareHistorical_open_frontier.rLocTop3 ≠ EvidenceLevel.kernelProved
      ∧ residueAwareHistorical_open_frontier.historicalRealisation ≠ EvidenceLevel.kernelProved
      ∧ residueAwareHistorical_open_frontier.r11 ≠ EvidenceLevel.kernelProved
      ∧ residueAwareHistorical_open_frontier.majorNewTypeIINecessity = false := by
  refine ⟨by decide, by decide, by decide, rfl⟩

/-- The analytic bound for `R_loc-top,3` is an open row of the status table. -/
theorem rlocTop3_analytic_bound_open :
    residueAwareStatus .rlocTop3AnalyticBound = EvidenceLevel.openRow := rfl

/-- The historical realisation certificate is an open row of the status table. -/
theorem realFordGrammarCertificate_open :
    residueAwareStatus .realFordGrammarCertificate = EvidenceLevel.openRow := rfl

/-- `R11`, global Gate 1B, HSTAR and the twin prime conjecture all remain open rows. -/
theorem downstream_all_open :
    residueAwareStatus .R11 = EvidenceLevel.openRow
      ∧ residueAwareStatus .globalGate1B = EvidenceLevel.openRow
      ∧ residueAwareStatus .hstar = EvidenceLevel.openRow
      ∧ residueAwareStatus .twinPrime = EvidenceLevel.openRow :=
  ⟨rfl, rfl, rfl, rfl⟩

end Gate1B.R11.Frontier
