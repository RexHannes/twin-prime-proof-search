/-
# Gate1B / R11 / Frontier : status bank, graveyard and dependency firewall

Machine-checked status data for the new frontier layer, together with the exact source definition
of the authoritative physical residual `R_hi`.

Two things are enforced by the kernel here:

* **Graveyard firewall.**  The *abstract* Hilbert-HMRD theorem keeps status `kernelProved`
  (it is re-ascribed below from the existing bank, so a regression would fail to compile), while
  the *physical* delta + single-Poisson caller has status `retiredNonclosing`.  The two are
  distinct rows, and no row of this bank is a proved physical owner of `R11`
  (`physicalR11Owners = []`).
* **Chain firewall.**  The authoritative chain is
  `audited rough-conductor low-frequency closure → exact first-moment high-pass reduction →
  R_hi (open) → R11 (open)`, and the old three-sector FSHC formulation is `superseded`, hence not
  an open requirement.

Status values are *metadata*: `researchBank` and `closedConditional` explicitly mean "not a Lean
proof of the analytic statement".  Only `kernelProved` rows are re-ascribed to actual theorems.
-/
import Gate1B.R11.StatusBank
import Gate1B.R11.Frontier.MatchedLine
import Gate1B.R11.Frontier.GcdDescent
import Gate1B.R11.Frontier.MeanZeroFourier
import Gate1B.R11.Frontier.LowHighProjection
import Gate1B.R11.Frontier.RoughConductorDescent
import Gate1B.R11.Frontier.AuditCorrections
import Gate1B.R11.Frontier.RoughModulusInterface

namespace Gate1B.R11.Frontier

open Finset Gate1B.HilbertHMRD

/-! ## 1. Status values and rows -/

/-- Status values of the frontier bank. -/
inductive FrontierStatus
  /-- Proved in Lean, checked by the kernel. -/
  | kernelProved
  /-- Analysed and retired as a saving mechanism; must not be imported as a proved owner. -/
  | retiredNonclosing
  /-- Superseded formulation; not an open requirement. -/
  | superseded
  /-- Closed at the physical first-moment level *conditional* on the audited analytic bank. -/
  | closedConditional
  /-- Audited research bank only; explicitly not a Lean proof. -/
  | researchBank
  /-- Open. -/
  | openRow
  /-- Not started. -/
  | notStarted
  deriving DecidableEq, Repr

/-- Rows of the frontier bank. -/
inductive FrontierRow
  | abstractHilbertHMRD
  | physicalHilbertCallerDeltaSinglePoisson
  | twoCopyDeterminant
  | heckeMatrixFactorisation
  | gcdDescent
  | meanZero
  | finiteFourierInversion
  | parseval
  | lowHighReassembly
  | mixedQuadraticFirewall
  | imprimitiveCharacterDescent
  | principal2jCorrection
  | ledger114Correction
  | cellQminFirewall
  | roughModulusVariance
  | roughConductorLowFrequencyClosure
  | firstMomentHighPassReduction
  | oldSectorA
  | oldFSHCThreeSector
  | rhiResidual
  | R11
  | censusRGe8
  | globalGate1B
  | hstar
  | twinPrime
  deriving DecidableEq, Repr

open FrontierRow FrontierStatus in
/-- The status assignment of the frontier bank. -/
def frontierStatus : FrontierRow → FrontierStatus
  | abstractHilbertHMRD => kernelProved
  | physicalHilbertCallerDeltaSinglePoisson => retiredNonclosing
  | twoCopyDeterminant => kernelProved
  | heckeMatrixFactorisation => kernelProved
  | gcdDescent => kernelProved
  | meanZero => kernelProved
  | finiteFourierInversion => kernelProved
  | parseval => kernelProved
  | lowHighReassembly => kernelProved
  | mixedQuadraticFirewall => kernelProved
  | imprimitiveCharacterDescent => kernelProved
  | principal2jCorrection => kernelProved
  | ledger114Correction => kernelProved
  | cellQminFirewall => kernelProved
  | roughModulusVariance => researchBank
  | roughConductorLowFrequencyClosure => closedConditional
  | firstMomentHighPassReduction => kernelProved
  | oldSectorA => closedConditional
  | oldFSHCThreeSector => superseded
  | rhiResidual => openRow
  | R11 => openRow
  | censusRGe8 => notStarted
  | globalGate1B => openRow
  | hstar => openRow
  | twinPrime => openRow

/-! ## 2. Re-ascription of the kernel-proved rows

Each `bank_*` below is a type ascription of an already-proved theorem, so the kernel re-checks
that the claimed `kernelProved` status matches an actual proof.  Nothing new is proved here. -/

/-- ABSTRACT HILBERT-HMRD: KERNEL-PROVED (existing layer, re-ascribed; a regression would break
this build). -/
theorem bank_abstract_hilbert_hmrd :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
      {s : ℕ} [NeZero s] (Dset Wset : Finset ℕ) (al be : ℕ → ℂ) (u v : ℕ → H)
      (xr yr : ℕ → ZMod s) (f : ZMod s → ℂ),
      (∀ x, ¬ IsUnit x → f x = 0) → (∀ x, ‖f x‖ ≤ 1) → ∀ P B1 : ℝ,
      (∀ m : ZMod s, ‖∑ d ∈ Dset, (al d * ez s (m * xr d)) • u d‖ ≤ P) →
      (∑ w ∈ Wset, ‖be w‖ * ‖v w‖ ≤ B1) →
      ∀ (A : ZMod s), IsUnit A → ∀ pin qin : ℕ → ZMod s,
      (∀ d ∈ Dset, ∀ w ∈ Wset, f (xr d * yr w) = ez s (A * (pin d * qin w))) →
      ∀ cD cW : ℝ,
      (∀ z : ZMod s, ((Dset.filter (fun d => pin d = z)).card : ℝ) ≤ cD) →
      (∀ z : ZMod s, ((Wset.filter (fun w => qin w = z)).card : ℝ) ≤ cW) →
      ‖packet s Dset Wset al be u v xr yr f‖
        ≤ min (Real.sqrt (Nat.totient s) * (P * B1))
            (Real.sqrt ((s : ℝ) * cD * cW)
              * (Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2)
                * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2))) :=
  fun Dset Wset al be u v xr yr f => Gate1B.R11.bank_hilbert_hmrd Dset Wset al be u v xr yr f

/-- TWO-COPY DETERMINANT `2h`: KERNEL-PROVED. -/
theorem bank_two_copy_determinant :
    ∀ {A k d0 B0 : ℤ}, A * B0 - k * d0 = -2 → ∀ t h : ℤ,
      dLine d0 A t * BLine B0 k (t + h) - dLine d0 A (t + h) * BLine B0 k t = 2 * h :=
  fun h0 t h => twoCopy_det h0 t h

/-- HECKE MATRIX FACTORISATION: KERNEL-PROVED. -/
theorem bank_hecke_factorisation :
    ∀ d0 A B0 k t h : ℤ, Mmat d0 A B0 k t h = Nmat d0 A B0 k t * !![1, 1; 0, h] :=
  Mmat_factorisation

/-- `det N_t = 2`: KERNEL-PROVED. -/
theorem bank_det_N :
    ∀ {A k d0 B0 : ℤ}, A * B0 - k * d0 = -2 → ∀ t : ℤ, (Nmat d0 A B0 k t).det = 2 :=
  fun h0 t => det_Nmat h0 t

/-- GCD DESCENT: KERNEL-PROVED (with the coprimality derived from the determinant and oddness). -/
theorem bank_gcd_descent :
    ∀ {A k d0 B0 : ℤ}, A * B0 - k * d0 = -2 → ∀ t : ℤ, Odd (dLine d0 A t) → ∀ h : ℤ,
      Int.gcd (dLine d0 A t) (dLine d0 A (t + h)) = Int.gcd (dLine d0 A t) h :=
  fun h0 t hodd h => gcd_dLine_two_copy_of_det h0 t hodd h

/-- DETERMINANT DESCENT after removing `g`: KERNEL-PROVED. -/
theorem bank_determinant_descent :
    ∀ {A k d0 B0 : ℤ}, A * B0 - k * d0 = -2 → ∀ t h g d' d'' h' : ℤ, g ≠ 0 →
      dLine d0 A t = g * d' → dLine d0 A (t + h) = g * d'' → h = g * h' →
      d' * BLine B0 k (t + h) - d'' * BLine B0 k t = 2 * h' :=
  fun h0 => twoCopy_det_descent h0

/-- MEAN ZERO: KERNEL-PROVED. -/
theorem bank_mean_zero :
    ∀ {Q : ℕ} [NeZero Q] (I : Finset (ZMod Q)) (b : ZMod Q → ℂ), I.Nonempty →
      ∑ t ∈ I, bPerp I b t = 0 :=
  fun I b hI => sum_bPerp_interval I b hI

/-- FINITE FOURIER INVERSION: KERNEL-PROVED. -/
theorem bank_fourier_inversion_row :
    ∀ {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) (x : ZMod Q),
      ∑ t : ZMod Q, fcoef Q f t * ez Q (t * x) = f x :=
  fun f x => bank_fourier_inversion f x

/-- PARSEVAL: KERNEL-PROVED. -/
theorem bank_parseval_row :
    ∀ {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ),
      ∑ t : ZMod Q, ‖fcoef Q f t‖ ^ 2 = (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖f x‖ ^ 2 :=
  fun f => bank_parseval f

/-- LOW/HIGH FIRST-MOMENT REASSEMBLY: KERNEL-PROVED. -/
theorem bank_first_moment_reassembly :
    ∀ {Q : ℕ} [NeZero Q] (S : Finset (ZMod Q)) (w f : ZMod Q → ℂ),
      Rtotal w f = Rlo S w f + Rhi S w f :=
  fun S w f => Rtotal_eq_Rlo_add_Rhi S w f

/-- MIXED-QUADRATIC FIREWALL: KERNEL-PROVED (the cross term is real and may not be deleted). -/
theorem bank_mixed_quadratic :
    (∀ z w : ℂ, ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * (starRingEnd ℂ) w).re) ∧
      ∃ z w : ℂ, ‖z + w‖ ^ 2 ≠ ‖z‖ ^ 2 + ‖w‖ ^ 2 :=
  ⟨norm_sq_add, mixed_term_not_deletable⟩

/-- IMPRIMITIVE CHARACTER DESCENT: KERNEL-PROVED (not library-blocked). -/
theorem bank_imprimitive_descent :
    ∀ {f r : ℕ} (hf : f ≠ 0) (hr : r ≠ 0) (chiStar : DirichletCharacter ℂ f) (a : ℕ → ℂ) (T : ℕ),
      haveI : NeZero (f * r) := ⟨Nat.mul_ne_zero hf hr⟩
      ∑ n ∈ Finset.range T, a n * (DirichletCharacter.changeLevel (Dvd.intro r rfl) chiStar)
          (n : ZMod (f * r))
        = ∑ e ∈ r.divisors, (ArithmeticFunction.moebius e : ℂ) * chiStar (e : ZMod f) *
            ∑ m ∈ (Finset.range T).filter (fun m => e * m < T),
              a (e * m) * chiStar (m : ZMod f) :=
  fun hf hr chiStar a T => dirichlet_conductor_descent hf hr chiStar a T

/-- PRINCIPAL `2^j` CORRECTION: KERNEL-PROVED. -/
theorem bank_principal_2j :
    (∀ (j : ℕ) (c : ℝ), ∑ _S ∈ (Finset.univ : Finset (Fin j)).powerset, c = 2 ^ j * c) ∧
      ∀ c : ℝ, 0 < c → (5 : ℝ) * c < ∑ _S ∈ (Finset.univ : Finset (Fin 5)).powerset, c :=
  ⟨subset_cost_identity, literal_j_cost_insufficient⟩

/-- LEDGER `114` CORRECTION: KERNEL-PROVED. -/
theorem bank_ledger_114 :
    (∀ b : ℚ, staleLedgerExponent b + 1 = ledgerExponent b) ∧ ledgerExponent 0 = 114 :=
  ⟨ledger_correction, ledger_at_zero⟩

/-- CELL `Qmin`/`H_C` FIREWALL: KERNEL-PROVED. -/
theorem bank_cell_cap :
    ∀ {α : Type} {C : Finset α} (hC : C.Nonempty) (Qf : α → ℕ) (H : ℕ),
      2 * H < QminCell C hC Qf → ∀ A ∈ C, 2 * H < Qf A :=
  fun hC Qf H hH => cell_cap_uniform hC Qf H hH

/-! ## 3. The authoritative physical residual `R_hi` -/

variable {Q : ℕ} [NeZero Q]

/-- **Exact source definition of `R_hi`**: the high-frequency first-moment projection of the
mean-zero target `b` on the line interval `I` against the Möbius coordinate weight `w`. -/
noncomputable def RhiFrontier (S I : Finset (ZMod Q)) (w b : ZMod Q → ℂ) : ℂ := Rhi S w (bPerp I b)

/-- The corresponding low-frequency first moment. -/
noncomputable def RloFrontier (S I : Finset (ZMod Q)) (w b : ZMod Q → ℂ) : ℂ := Rlo S w (bPerp I b)

/-- **EXACT FIRST-MOMENT HIGH-PASS REDUCTION.**  The total first moment of the mean-zero target
splits exactly into the low-frequency part and `R_hi`. -/
theorem highPass_reduction (S I : Finset (ZMod Q)) (w b : ZMod Q → ℂ) :
    Rtotal w (bPerp I b) = RloFrontier S I w b + RhiFrontier S I w b :=
  Rtotal_eq_Rlo_add_Rhi S w (bPerp I b)

/-- The **open** analytic estimate for `R_hi`, recorded as a proposition.  No declaration of this
bank inhabits it. -/
def RhiAnalyticEstimate (S I : Finset (ZMod Q)) (w b : ZMod Q → ℂ) (bound : ℝ) : Prop :=
  ‖RhiFrontier S I w b‖ ≤ bound

/-- The `R_hi` row is open, and the bank says so. -/
theorem rhi_row_open : frontierStatus FrontierRow.rhiResidual = FrontierStatus.openRow := rfl

/-! ## 4. Graveyard and dependency firewalls -/

/-- ABSTRACT HILBERT-HMRD keeps status `kernelProved`. -/
theorem abstract_hmrd_kernelProved :
    frontierStatus FrontierRow.abstractHilbertHMRD = FrontierStatus.kernelProved := rfl

/-- PHYSICAL DELTA + SINGLE-POISSON CALLER is retired as a saving mechanism. -/
theorem physical_caller_retired :
    frontierStatus FrontierRow.physicalHilbertCallerDeltaSinglePoisson
      = FrontierStatus.retiredNonclosing := rfl

/-- **GRAVEYARD FIREWALL.**  The retired physical caller is a different row from the abstract
theorem, and its status is not `kernelProved`: it may not be imported as a proved result. -/
theorem physical_caller_firewall :
    FrontierRow.physicalHilbertCallerDeltaSinglePoisson ≠ FrontierRow.abstractHilbertHMRD ∧
      frontierStatus FrontierRow.physicalHilbertCallerDeltaSinglePoisson
        ≠ FrontierStatus.kernelProved := by
  decide

/-- The list of rows claimed to be **proved physical owners of `R11`** — deliberately empty. -/
def physicalR11Owners : List FrontierRow := []

/-- **NO PROVED PHYSICAL `R11` OWNER.**  In particular the retired caller is not one. -/
theorem no_physical_R11_owner : ∀ r : FrontierRow, r ∉ physicalR11Owners := by
  intro r hr
  simp [physicalR11Owners] at hr

/-- The authoritative dependency chain. -/
def frontierChain : List FrontierRow :=
  [FrontierRow.roughConductorLowFrequencyClosure, FrontierRow.firstMomentHighPassReduction,
   FrontierRow.rhiResidual, FrontierRow.R11]

/-- **CHAIN FIREWALL.**  Conditional low-frequency closure → kernel-proved high-pass reduction →
`R_hi` open → `R11` open. -/
theorem frontier_chain_statuses :
    frontierStatus FrontierRow.roughConductorLowFrequencyClosure
        = FrontierStatus.closedConditional ∧
      frontierStatus FrontierRow.firstMomentHighPassReduction = FrontierStatus.kernelProved ∧
      frontierStatus FrontierRow.rhiResidual = FrontierStatus.openRow ∧
      frontierStatus FrontierRow.R11 = FrontierStatus.openRow := by
  decide

/-- **OLD FSHC IS SUPERSEDED** and therefore is not an open requirement. -/
theorem oldFSHC_superseded_not_open :
    frontierStatus FrontierRow.oldFSHCThreeSector = FrontierStatus.superseded ∧
      frontierStatus FrontierRow.oldFSHCThreeSector ≠ FrontierStatus.openRow := by
  decide

/-- **OLD SECTOR A** is closed only conditionally on the audited analytic bank — never
`kernelProved`. -/
theorem oldSectorA_conditional :
    frontierStatus FrontierRow.oldSectorA = FrontierStatus.closedConditional ∧
      frontierStatus FrontierRow.oldSectorA ≠ FrontierStatus.kernelProved := by
  decide

/-- **ROUGH-MODULUS VARIANCE** is research-bank metadata, not a Lean proof. -/
theorem roughModulus_researchBank :
    frontierStatus FrontierRow.roughModulusVariance = FrontierStatus.researchBank ∧
      frontierStatus FrontierRow.roughModulusVariance ≠ FrontierStatus.kernelProved := by
  decide

/-- The global rows stay open (and the `r ≥ 8` census is not started). -/
theorem global_rows_open :
    frontierStatus FrontierRow.globalGate1B = FrontierStatus.openRow ∧
      frontierStatus FrontierRow.hstar = FrontierStatus.openRow ∧
      frontierStatus FrontierRow.twinPrime = FrontierStatus.openRow ∧
      frontierStatus FrontierRow.censusRGe8 = FrontierStatus.notStarted := by
  decide

/-- No row of this layer claims a proof of twin primes, global Gate 1B, `H*` or `R11`. -/
theorem no_global_claim :
    ∀ r ∈ [FrontierRow.twinPrime, FrontierRow.globalGate1B, FrontierRow.hstar, FrontierRow.R11],
      frontierStatus r ≠ FrontierStatus.kernelProved := by
  decide

end Gate1B.R11.Frontier
