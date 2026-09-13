/-
# Gate1B / R11 / Frontier : status bank of the unmodified-row delta (`R_newcrit`)

Machine-checked status data for the new frontier layer, together with the exact finite source
definition of the current frontier residual `R_newcrit` and the *conditional* implication that
would bound it.

The status values are reused from `Gate1B.R11.Frontier.StatusBank` (`FrontierStatus`), with the
following reading for this delta:

* `kernelProved` — proved in Lean, re-ascribed below so that a regression breaks the build;
* `retiredNonclosing` — analysed and retired as a *mechanism*; must never be imported as a proved
  saving.  (Retirement of a mechanism is not an impossibility theorem.)
* `superseded` — historical coordinate, kept and still valid, but no longer the current frontier;
* `closedConditional` — an **external / conditional analytic input**: an explicit theorem
  hypothesis, never a Lean proof and never a custom axiom;
* `openRow` — open.

Enforced by the kernel here:

* the old empty-site repair is `kernelProved` **as an algebraic source-preserving transform** and
  `retiredNonclosing` **as a free principal-removal mechanism**; the two are different rows and
  the retired one is provably not `kernelProved`;
* the previous authoritative coordinate `R_hi` is `superseded`, *not deleted*: its exact high-pass
  reduction is re-ascribed below and still holds;
* `R_newcrit`, `R11`, global Gate 1B, `H*` and twin primes are `openRow`, and no row of this bank
  is a proved owner of any of them.
-/
import Gate1B.R11.Frontier.StatusBank
import Gate1B.R11.Frontier.OccupiedRowKernel
import Gate1B.R11.Frontier.ProductFibrePushforward
import Gate1B.R11.Frontier.EmptySiteRepairTransfer
import Gate1B.R11.Frontier.UnmodifiedRowInterpolation
import Gate1B.R11.Frontier.CriticalMixedIncidence
import Gate1B.R11.Frontier.CriticalMaskFirewall
import Gate1B.R11.Frontier.RealOverlapSupport

namespace Gate1B.R11.Frontier

open Finset Gate1B.HilbertHMRD

noncomputable section

/-! ## 1. Rows and statuses of the delta -/

/-- Rows of the unmodified-row frontier delta. -/
inductive NewCritRow
  /-- The exact original occupied-row arithmetic source and its finite reassembly. -/
  | originalRowSource
  /-- The product-fibre pushforward algebra `b = N·w`. -/
  | productFibrePushforward
  /-- The bound `‖w‖ ≤ 1`. -/
  | weightBoundedByOne
  /-- Product-fibre equality is not tuplewise equality. -/
  | productFibreTuplewiseFirewall
  /-- The old empty-site repair as an algebraic source-preserving transform. -/
  | emptySiteRepairAlgebra
  /-- The old empty-site repair as a *free principal-removal* mechanism. -/
  | emptySiteRepairFreePrincipalRemoval
  /-- `L_nonprincipal(repair) = L_principal(original row)`. -/
  | repairTransferIdentity
  /-- Principal cancellation is not removal from the complete spectrum. -/
  | principalTransferFirewall
  /-- Full orthogonality inside a critical character mask. -/
  | criticalMaskFullOrthogonality
  /-- A masked Fourier sum as a point mass. -/
  | maskedFourierPointMass
  /-- The modular relation of the critical mixed moment. -/
  | mixedIncidenceModularRelation
  /-- Exact sample recovery of the unmodified-row compiler. -/
  | interpolationSampleRecovery
  /-- The Fourier-transform statement for the interpolation kernel. -/
  | interpolationFourierInterface
  /-- The exact width/Mellin-height scale identities. -/
  | widthScalingIdentity
  /-- "Narrow interpolation itself creates an arithmetic saving." -/
  | narrowInterpolationCreatesSaving
  /-- The real-overlap logarithmic support control. -/
  | realOverlapSupport
  /-- The narrow-interpolation arbitrary-log principal estimate. -/
  | narrowInterpolationPrincipalEstimate
  /-- Conductor / time tail bounds. -/
  | conductorTailEstimates
  /-- External large-sieve / Chen-Gupta-Li / Maynard-Pandey-Radziwill inputs. -/
  | externalLargeSieveInputs
  /-- The critical signed mixed-covariance estimate. -/
  | criticalMixedIncidenceEstimate
  /-- The previous authoritative coordinate `R_hi`. -/
  | rhiHistoricalCoordinate
  /-- The current frontier residual. -/
  | Rnewcrit
  /-- The `R11` row. -/
  | R11row
  /-- Global Gate 1B. -/
  | globalGate1B
  /-- The `H*` row. -/
  | hstar
  /-- Twin primes. -/
  | twinPrime
  deriving DecidableEq, Repr

open NewCritRow FrontierStatus in
/-- The status assignment of the delta. -/
def newCritStatus : NewCritRow → FrontierStatus
  | originalRowSource => kernelProved
  | productFibrePushforward => kernelProved
  | weightBoundedByOne => kernelProved
  | productFibreTuplewiseFirewall => kernelProved
  | emptySiteRepairAlgebra => kernelProved
  | emptySiteRepairFreePrincipalRemoval => retiredNonclosing
  | repairTransferIdentity => kernelProved
  | principalTransferFirewall => kernelProved
  | criticalMaskFullOrthogonality => retiredNonclosing
  | maskedFourierPointMass => retiredNonclosing
  | mixedIncidenceModularRelation => kernelProved
  | interpolationSampleRecovery => kernelProved
  | interpolationFourierInterface => closedConditional
  | widthScalingIdentity => kernelProved
  | narrowInterpolationCreatesSaving => retiredNonclosing
  | realOverlapSupport => kernelProved
  | narrowInterpolationPrincipalEstimate => closedConditional
  | conductorTailEstimates => closedConditional
  | externalLargeSieveInputs => closedConditional
  | criticalMixedIncidenceEstimate => closedConditional
  | rhiHistoricalCoordinate => superseded
  | Rnewcrit => openRow
  | R11row => openRow
  | globalGate1B => openRow
  | hstar => openRow
  | twinPrime => openRow

/-! ## 2. Re-ascription of the kernel-proved rows

Each `newbank_*` is a type ascription of an already-proved theorem of this delta, so the kernel
re-checks the `kernelProved` claims.  Nothing new is proved in this section. -/

/-- ORIGINAL OCCUPIED ROW SOURCE: KERNEL-PROVED (exact finite reassembly). -/
theorem newbank_original_row_reassembly :
    ∀ {Q : ℕ} [NeZero Q] {ι : Type} (rows : Finset ι) (R : ι → OccupiedRow Q) (N : Finset ℕ)
      (v : ZMod Q),
      DpreTotal rows R N v = ∑ n ∈ N, ∑ i ∈ rows, muOdd n * Gamma (R i) v n :=
  fun rows R N v => DpreTotal_eq_double_sum rows R N v

/-- ORIGINAL OCCUPIED ROW SOURCE: the mean-subtracted row kernel really has zero row mean. -/
theorem newbank_row_mean_zero :
    ∀ {Q : ℕ} (R : OccupiedRow Q) (N : Finset ℕ), ∑ v ∈ R.I, Drow R N v = 0 :=
  fun R N => Drow_mean_zero R N

/-- ORIGINAL OCCUPIED ROW SOURCE: the full-mask evaluation of the actual row averages. -/
theorem newbank_freqMask_univ :
    ∀ {Q : ℕ} [NeZero Q] (R : OccupiedRow Q), R.maskSet = Finset.univ →
      (∀ xi, R.maskCoef xi = 1) → ∀ v : ZMod Q,
      freqMask R v = (R.I.card : ℂ)⁻¹ * (Q : ℂ) * (if v ∈ R.I then 1 else 0) :=
  fun R hmask hcoef v => freqMask_univ R hmask hcoef v

/-- PRODUCT-FIBRE PUSHFORWARD: KERNEL-PROVED. -/
theorem newbank_pushforward :
    ∀ {ι : Type} {N : ι → ℝ} {b : ι → ℂ} (v : ι), ‖b v‖ ≤ N v →
      b v = (N v : ℂ) * fibreWeight N b v :=
  fun v hb => pushforward_factorisation v hb

/-- `‖w‖ ≤ 1`: KERNEL-PROVED. -/
theorem newbank_weight_le_one :
    ∀ {ι : Type} {N : ι → ℝ} {b : ι → ℂ} (v : ι), ‖b v‖ ≤ N v →
      ‖fibreWeight N b v‖ ≤ 1 :=
  fun v hb => norm_fibreWeight_le_one v hb

/-- PRODUCT-FIBRE vs TUPLEWISE FIREWALL: KERNEL-PROVED. -/
theorem newbank_productFibre_firewall :
    ∃ (P : Fin 2 → Fin 1) (s s' : Fin 2 → ℂ),
      (∀ t, ‖s t‖ ≤ 1) ∧ (∀ t, ‖s' t‖ ≤ 1) ∧
      (∀ v, pushforward P s v = pushforward P s' v) ∧ s ≠ s' :=
  productFibre_equality_ne_tuplewise_equality

/-- OLD EMPTY-SITE REPAIR, ALGEBRAIC SOURCE PRESERVATION: KERNEL-PROVED. -/
theorem newbank_repair_source_preserving :
    ∀ {U : Type} [DecidableEq U] {O E : Finset U} {m d0 : U → ℂ}, Disjoint O E →
      Lphys O (repairCorrection O E m d0) = 0 :=
  fun hdisj => Lphys_repair_zero hdisj

/-- REPAIR TRANSFER `L_nonprincipal(repair) = L_principal(original)`: KERNEL-PROVED. -/
theorem newbank_repair_transfer :
    ∀ {U : Type} [DecidableEq U] {O E : Finset U} {m d0 : U → ℂ}, Disjoint O E →
      (∀ u ∉ O, d0 u = 0) → gramEmpty E m ≠ 0 →
      Lnonprin (O ∪ E) O m (repairCorrection O E m d0) = Lprin (O ∪ E) m d0 :=
  fun hdisj hd0 hG => Lnonprin_repair_eq_Lprin_original hdisj hd0 hG

/-- PRINCIPAL-TRANSFER FIREWALL: KERNEL-PROVED. -/
theorem newbank_principal_transfer_firewall :
    ∃ (O E : Finset (Fin 2)) (m d0 : Fin 2 → ℂ),
      Disjoint O E ∧ gramEmpty E m ≠ 0 ∧
      Lprin (O ∪ E) m (repairedRow O E m d0) = 0 ∧
      Lphys O (repairedRow O E m d0) ≠ 0 ∧
      Lnonprin (O ∪ E) O m (repairedRow O E m d0) ≠ 0 :=
  principal_cancellation_is_not_removal

/-- CRITICAL MASK FULL-ORTHOGONALITY FIREWALL: KERNEL-PROVED. -/
theorem newbank_critical_mask_firewall :
    ∃ (q : ℕ) (_ : NeZero q) (S : Finset (ZMod q)),
      S ⊂ Finset.univ ∧
      ∀ n a : ZMod q, (q : ℂ)⁻¹ * maskedSum q S (n - a) ≠ (if n = a then 1 else 0) :=
  proper_mask_not_congruence_indicator

/-- MASKED FOURIER SUM FIREWALL: KERNEL-PROVED. -/
theorem newbank_masked_fourier_firewall :
    ∃ (q : ℕ) (_ : NeZero q) (S : Finset (ZMod q)) (x : ZMod q),
      S ⊂ Finset.univ ∧ x ≠ 0 ∧ maskedSum q S x ≠ 0 :=
  masked_frequency_sum_not_point_mass

/-- MIXED INCIDENCE MODULAR RELATION: KERNEL-PROVED. -/
theorem newbank_mixed_incidence :
    ∀ {qi qj A B k : ℤ}, qi * A ≡ qj * B [ZMOD k] → ∃ ell : ℤ, qi * A - qj * B = ell * k :=
  fun h => mixedIncidence_relation h

/-- UNMODIFIED-ROW COMPILER, EXACT SAMPLE RECOVERY: KERNEL-PROVED. -/
theorem newbank_interpolation_sample :
    ∀ {ι : Type} (C : CardinalInterpolation ι) (S : Finset ι) (d : ι → ℂ) (u : ι), u ∈ S →
      interpolant C S d (C.z u) = d u :=
  fun C S d _ hu => interpolant_sample C S d hu

/-- NARROW-INTERPOLATION SCALE IDENTITY: KERNEL-PROVED. -/
theorem newbank_scale_identity :
    ∀ {L P m theta T1 : ℝ}, 0 < L → theta = L ^ (-m) → T1 = P * theta⁻¹ * L ^ (3 : ℝ) →
      T1 = P * L ^ (m + 3) :=
  fun hL ht hT => mellin_height_scale hL ht hT

/-- REAL-OVERLAP SUPPORT: KERNEL-PROVED (explicit constants, no `O(·)`). -/
theorem newbank_real_overlap :
    ∀ {A B Biu Bjv hi hj Cp : ℝ}, 0 < A → 0 < B → 0 < Biu → 0 < Bjv → 0 ≤ hi → 0 ≤ hj →
      hi + hj ≤ 1 → A * Bjv ≤ Cp → B * Biu ≤ Cp → logOverlap A B Biu Bjv hi hj →
      |A * Bjv - B * Biu| ≤ 2 * Cp * (hi + hj) :=
  fun hA hB h1 h2 h3 h4 h5 h6 h7 h => overlap_abs_sub_le hA hB h1 h2 h3 h4 h5 h6 h7 h

/-- `R_hi` IS NOT DELETED: the historical coordinate keeps its exact high-pass reduction. -/
theorem newbank_rhi_still_valid :
    ∀ {Q : ℕ} [NeZero Q] (S I : Finset (ZMod Q)) (w b : ZMod Q → ℂ),
      Rtotal w (bPerp I b) = RloFrontier S I w b + RhiFrontier S I w b :=
  fun S I w b => highPass_reduction S I w b

/-! ## 3. Firewalls on the status assignment -/

/-- OLD EMPTY-SITE REPAIR: algebraically valid **and** retired as a free removal mechanism.  The
two readings are different rows, and the retired one is provably not `kernelProved`. -/
theorem empty_site_repair_firewall :
    newCritStatus NewCritRow.emptySiteRepairAlgebra = FrontierStatus.kernelProved ∧
      newCritStatus NewCritRow.emptySiteRepairFreePrincipalRemoval
        = FrontierStatus.retiredNonclosing ∧
      NewCritRow.emptySiteRepairAlgebra ≠ NewCritRow.emptySiteRepairFreePrincipalRemoval ∧
      newCritStatus NewCritRow.emptySiteRepairFreePrincipalRemoval
        ≠ FrontierStatus.kernelProved := by
  decide

/-- The three retired mechanisms are retired, and none of them is `kernelProved`. -/
theorem retired_mechanisms :
    ∀ r ∈ [NewCritRow.emptySiteRepairFreePrincipalRemoval,
           NewCritRow.criticalMaskFullOrthogonality,
           NewCritRow.maskedFourierPointMass,
           NewCritRow.narrowInterpolationCreatesSaving],
      newCritStatus r = FrontierStatus.retiredNonclosing := by
  decide

/-- The analytic inputs are conditional, never kernel-proved. -/
theorem conditional_analytic_rows :
    ∀ r ∈ [NewCritRow.interpolationFourierInterface,
           NewCritRow.narrowInterpolationPrincipalEstimate,
           NewCritRow.conductorTailEstimates,
           NewCritRow.externalLargeSieveInputs,
           NewCritRow.criticalMixedIncidenceEstimate],
      newCritStatus r = FrontierStatus.closedConditional ∧
        newCritStatus r ≠ FrontierStatus.kernelProved := by
  decide

/-- `R_hi` IS HISTORICAL / SUPERSEDED AS THE CURRENT COORDINATE — and is neither deleted nor an
open requirement (its exact reduction is re-ascribed in `newbank_rhi_still_valid`). -/
theorem rhi_superseded_as_current_coordinate :
    newCritStatus NewCritRow.rhiHistoricalCoordinate = FrontierStatus.superseded ∧
      newCritStatus NewCritRow.rhiHistoricalCoordinate ≠ FrontierStatus.openRow ∧
      newCritStatus NewCritRow.rhiHistoricalCoordinate ≠ FrontierStatus.kernelProved := by
  decide

/-- The open rows of the delta stay open. -/
theorem newcrit_open_rows :
    ∀ r ∈ [NewCritRow.Rnewcrit, NewCritRow.R11row, NewCritRow.globalGate1B,
           NewCritRow.hstar, NewCritRow.twinPrime],
      newCritStatus r = FrontierStatus.openRow ∧
        newCritStatus r ≠ FrontierStatus.kernelProved := by
  decide

/-- The list of rows claimed to be proved owners of `R_newcrit` — deliberately empty. -/
def newCritOwners : List NewCritRow := []

/-- **NO PROVED OWNER OF `R_newcrit`.** -/
theorem no_newcrit_owner : ∀ r : NewCritRow, r ∉ newCritOwners := by
  intro r hr
  simp [newCritOwners] at hr

/-! ## 4. The current frontier residual `R_newcrit` -/

variable {Q : ℕ} [NeZero Q]

/-- **Exact finite source definition of `R_newcrit`**: the first moment of the *original occupied
arithmetic rows*, with mean subtraction and **no empty-site correction**. -/
def RnewcritSource {ι : Type*} (rows : Finset ι) (R : ι → OccupiedRow Q) (N : Finset ℕ)
    (w : ZMod Q → ℂ) : ℂ := ∑ i ∈ rows, Rtotal w (Drow (R i) N)

/-- The per-row first moments whose signed mixed covariance is the open problem. -/
def rowFunctional {ι : Type*} (R : ι → OccupiedRow Q) (N : Finset ℕ) (w : ZMod Q → ℂ)
    (i : ι) : ℂ := Rtotal w (Drow (R i) N)

/-- `R_newcrit` is exactly the sum of the per-row functionals. -/
theorem RnewcritSource_eq_sum {ι : Type*} (rows : Finset ι) (R : ι → OccupiedRow Q)
    (N : Finset ℕ) (w : ZMod Q → ℂ) :
    RnewcritSource rows R N w = ∑ i ∈ rows, rowFunctional R N w i := rfl

/-- The declared (and **open**) estimate for `R_newcrit`.  No declaration of this bank inhabits
it. -/
def RnewcritEstimate (val : ℂ) (bound : ℝ) : Prop := ‖val‖ ≤ bound

/-- **The critical mixed-incidence hypothesis**, stated as an ordinary theorem parameter: the
signed mixed covariance of the per-row functionals is bounded by `C²`.  This is *not* an axiom and
is never inhabited here. -/
def CriticalMixedIncidenceHypothesis {ι : Type*} (rows : Finset ι) (L : ι → ℂ) (C : ℝ) : Prop :=
  ∑ i ∈ rows, ∑ j ∈ rows, ‖L i‖ * ‖L j‖ ≤ C ^ 2

/-- **THE DOWNSTREAM CONDITIONAL IMPLICATION** (kernel-proved): the mixed-incidence hypothesis
implies the declared estimate for a sum of per-row functionals. -/
theorem bound_of_criticalMixedIncidence {ι : Type*} (rows : Finset ι) (L : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (h : CriticalMixedIncidenceHypothesis rows L C) :
    ‖∑ i ∈ rows, L i‖ ≤ C := by
  have htri : ‖∑ i ∈ rows, L i‖ ≤ ∑ i ∈ rows, ‖L i‖ := norm_sum_le _ _
  have hS : 0 ≤ ∑ i ∈ rows, ‖L i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hsq : (∑ i ∈ rows, ‖L i‖) ^ 2 ≤ C ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact h
  have : ∑ i ∈ rows, ‖L i‖ ≤ C := by nlinarith
  exact le_trans htri this

/-- **`R_newcrit` CONDITIONAL BOUND.**  Under the critical mixed-incidence hypothesis for the
per-row functionals, the declared `R_newcrit` estimate follows.  The hypothesis itself is *open*:
nothing in this bank inhabits it. -/
theorem Rnewcrit_estimate_of_hypothesis {ι : Type*} (rows : Finset ι) (R : ι → OccupiedRow Q)
    (N : Finset ℕ) (w : ZMod Q → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : CriticalMixedIncidenceHypothesis rows (rowFunctional R N w) C) :
    RnewcritEstimate (RnewcritSource rows R N w) C := by
  rw [RnewcritEstimate, RnewcritSource_eq_sum]
  exact bound_of_criticalMixedIncidence rows (rowFunctional R N w) hC h

/-- The current frontier row is open, and the bank says so. -/
theorem Rnewcrit_row_open : newCritStatus NewCritRow.Rnewcrit = FrontierStatus.openRow := rfl

/-! ## 5. The ledger -/

/-- The kernel-proved rows of the delta. -/
def newCritKernelProved : List NewCritRow :=
  [NewCritRow.originalRowSource, NewCritRow.productFibrePushforward,
   NewCritRow.weightBoundedByOne, NewCritRow.productFibreTuplewiseFirewall,
   NewCritRow.emptySiteRepairAlgebra, NewCritRow.repairTransferIdentity,
   NewCritRow.principalTransferFirewall, NewCritRow.mixedIncidenceModularRelation,
   NewCritRow.interpolationSampleRecovery, NewCritRow.widthScalingIdentity,
   NewCritRow.realOverlapSupport]

/-- Every row of the kernel-proved list really has status `kernelProved`. -/
theorem newCritKernelProved_correct :
    ∀ r ∈ newCritKernelProved, newCritStatus r = FrontierStatus.kernelProved := by
  decide

/-- No open row is listed as kernel-proved. -/
theorem newCritKernelProved_excludes_open :
    ∀ r ∈ [NewCritRow.Rnewcrit, NewCritRow.R11row, NewCritRow.globalGate1B, NewCritRow.hstar,
           NewCritRow.twinPrime], r ∉ newCritKernelProved := by
  decide

end

end Gate1B.R11.Frontier
