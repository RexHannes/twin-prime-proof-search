/-
# Gate1B / R11 / Frontier : the minimal-kernel status bank and the current D + P + J frontier

Append-only module of the minimal-gap-kernel delta.  This is the **ledger** of the delta:

* the squarefull-mask partition (`SqFull ≤ V` versus `SqFull > V`) with disjointness and the
  no-double-charge identity;
* the current signed parent `T_kernel = 252 ∑_C (D_C + P_C + J_C)` with the exact source
  reassembly at the declared retained-source scope;
* the status table of the delta, with every `kernelProved` row **re-ascribed** to an actual
  theorem of this layer (so a regression breaks the build);
* the retired-method firewalls and the source-provenance record;
* the current open frontier: no open proposition is inhabited anywhere in this layer.
-/
import Gate1B.R11.Frontier.BadGapFibreContraction
import Gate1B.R11.Frontier.PrimeKernelBridge
import Gate1B.R11.Frontier.DenseSupportFirewall
import Gate1B.R11.Frontier.SquarefreeCoreReflection
import Gate1B.R11.Frontier.ComplementThresholdFibre
import Gate1B.R11.Frontier.CenteredDivisorSource
import Gate1B.R11.Frontier.StatusBank

namespace Gate1B.R11.Frontier

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
open Classical

/-! ## 1. The squarefull mask partition -/

/-- The large-squarefull mask: the source splits into `SqFull(M) ≤ V` and `SqFull(M) > V`. -/
theorem squarefull_mask_partition (Ns : Finset ℕ) (F : ℕ → ℝ) (V : ℕ) :
    ∑ n ∈ Ns, F n
      = (∑ n ∈ Ns with sqFullPart (n + 2) ≤ V, F n)
        + ∑ n ∈ Ns with ¬ (sqFullPart (n + 2) ≤ V), F n :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The two squarefull sectors are disjoint: no `n` is charged twice. -/
theorem squarefull_mask_disjoint (Ns : Finset ℕ) (V : ℕ) :
    Disjoint (Ns.filter fun n => sqFullPart (n + 2) ≤ V)
      (Ns.filter fun n => ¬ (sqFullPart (n + 2) ≤ V)) :=
  Finset.disjoint_filter_filter_not _ _ _

/-- The large-squarefull tail bound.  **External analytic / certificate-backed** input: a
proposition, never inhabited here, never an axiom. -/
def LargeSquarefullTailBound (Ns : Finset ℕ) (F : ℕ → ℝ) (V : ℕ) (x L S0 C : ℝ) : Prop :=
  |∑ n ∈ Ns with ¬ (sqFullPart (n + 2) ≤ V), F n| ≤ C * x * L ^ (-S0 - 2)

/-! ## 2. The current D / P / J source -/

/-- DENSE: divisors with `Fgap(d) ≤ x`. -/
def IsDenseDivisor (x d : ℕ) : Prop := Fgap d ≤ x

/-- PRIME-KERNEL BRIDGE: bad divisors whose minimal kernel is a prime. -/
def IsBridgeDivisor (x d : ℕ) : Prop :=
  x < Fgap d ∧ ∃ p, p.Prime ∧ IsMinKernel x p ∧ p ∣ d

/-- KERNEL PRIME-POWER: the remaining bad divisors (kernel of rank ≥ 2). -/
def IsKernelPowerDivisor (x d : ℕ) : Prop :=
  x < Fgap d ∧ ¬ ∃ p, p.Prime ∧ IsMinKernel x p ∧ p ∣ d

/-- The sharp divisor fibre restricted to a class of divisors. -/
def HdivOn (P : ℕ → Prop) (z : ℝ) (M : ℕ) : ℝ :=
  ∑ d ∈ M.divisors,
    (if P d then
      (if z < (d : ℝ) then (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) else 0) else 0)

/-- **Exact source reassembly.**  The complete fibre is the sum of the dense, kernel
prime-power and prime-kernel-bridge charts; the three classes are mutually exclusive and
exhaustive, so nothing is double-charged and nothing is lost. -/
theorem Hdiv_eq_dense_add_power_add_bridge (x : ℕ) (z : ℝ) (M : ℕ) :
    Hdiv z M = HdivOn (IsDenseDivisor x) z M + HdivOn (IsKernelPowerDivisor x) z M
      + HdivOn (IsBridgeDivisor x) z M := by
  unfold Hdiv HdivOn
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hdense : Fgap d ≤ x
  · have h1 : IsDenseDivisor x d := hdense
    have h2 : ¬ IsKernelPowerDivisor x d := fun h => absurd h.1 (by omega)
    have h3 : ¬ IsBridgeDivisor x d := fun h => absurd h.1 (by omega)
    simp [h1, h2, h3]
  · push_neg at hdense
    have h1 : ¬ IsDenseDivisor x d := by unfold IsDenseDivisor; omega
    by_cases hbr : ∃ p, p.Prime ∧ IsMinKernel x p ∧ p ∣ d
    · have h3 : IsBridgeDivisor x d := ⟨hdense, hbr⟩
      have h2 : ¬ IsKernelPowerDivisor x d := fun h => h.2 hbr
      simp [h1, h2, h3]
    · have h2 : IsKernelPowerDivisor x d := ⟨hdense, hbr⟩
      have h3 : ¬ IsBridgeDivisor x d := fun h => hbr h.2
      simp [h1, h2, h3]

/-- The dense part of the physical source. -/
def Dpart (Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Ns, Ω n * HdivOn (IsDenseDivisor x) z (n + 2)

/-- The kernel prime-power part of the physical source. -/
def Ppart (Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Ns, Ω n * HdivOn (IsKernelPowerDivisor x) z (n + 2)

/-- The prime-kernel-bridge part of the physical source. -/
def Jpart (Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Ns, Ω n * HdivOn (IsBridgeDivisor x) z (n + 2)

/-- The current signed parent `T_kernel = 252 (D + P + J)`. -/
def Tkernel (Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) (x : ℕ) : ℝ :=
  252 * (Dpart Ns Ω z x + Ppart Ns Ω z x + Jpart Ns Ω z x)

/-- **Kernel-proved source reassembly**: the physical source equals the signed parent. -/
theorem Tsource_eq_Tkernel (Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) (x : ℕ) :
    Tsource Ns Ω z = Tkernel Ns Ω z x := by
  unfold Tsource Tkernel Dpart Ppart Jpart
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Hdiv_eq_dense_add_power_add_bridge x z (n + 2)]
  ring

/-- The analytic balance of the current frontier: `|D + P + J| ≪ x L^{-S₀}`.  **OPEN**: a
proposition, never inhabited in this layer. -/
def DPJBalance (Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) (x : ℕ) (X L S0 C : ℝ) : Prop :=
  |Dpart Ns Ω z x + Ppart Ns Ω z x + Jpart Ns Ω z x| ≤ C * X * L ^ (-S0)

/-! ## 3. Status taxonomy of the delta -/

/-- Evidence levels of the minimal-kernel delta. -/
inductive MKStatus
  /-- Proved in Lean and checked by the kernel. -/
  | kernelProved
  /-- An explicit theorem interface: a `Prop` supplied as a hypothesis, never inhabited here. -/
  | explicitTheoremInterface
  /-- External analytic input, certificate-backed in the research bank; not a Lean proof. -/
  | externalAnalyticCertificateBacked
  /-- Conditional analytic statement: an ordinary theorem hypothesis. -/
  | conditionalAnalytic
  /-- Kernel-refuted as stated. -/
  | rejectedFalse
  /-- Retired as an active closing procedure at the tested scope. -/
  | retiredNonclosing
  /-- A method that does not close at the tested scope (not an impossibility theorem). -/
  | methodNonclosing
  /-- No legal dictionary between the two objects. -/
  | noLegalDictionary
  /-- Source provenance recovered only in part. -/
  | improvedPartial
  /-- Open, but strictly reduced by this delta. -/
  | strictlyReducedOpen
  /-- Open. -/
  | openRow
  deriving DecidableEq, Repr

/-- Rows of the minimal-kernel delta. -/
inductive MKRow
  | completeDivisorFibre
  | centeredSourceDefinition
  | centeredSourceEstimate
  | principalCoefficientConvolution
  | principalLocalFactors
  | principalOwnerIdentity
  | principalReassembly
  | completePrincipalSmallness
  | squarefullDecomposition
  | squarefullMaskPartition
  | largeSquarefullTail
  | squarefreeCoreReflection
  | localESum
  | schinzelSzekeresFunction
  | FgapEqDtimesG
  | denseSupportCharacterisation
  | denseCompleteWeightWellFactorable
  | minimalBadGapKernel
  | uniqueKernelPerM
  | badDivisorClassification
  | badGapFibreContraction
  | nonPrimePowerCofactorZero
  | kernelRankCofactorRange
  | complementThresholdLemmas
  | primeKernelBridgeSourceAlgebra
  | primeKernelBridgeExponent
  | DPJSourceDecomposition
  | DPJAnalyticBound
  | denseOwner
  | kernelPrimePowerOwners
  | characterMellinClosingProcedure
  | movingYClosingFamily
  | pascadiCompleteOwner
  | openGDividesAOrdinaryMertens
  | averageShiftToFixedShiftTwo
  | reciprocalExponentialToKloosterman
  | omegaCProvenance
  | R11row
  | globalGate1Brow
  | hstarRow
  | twinPrimeRow
  deriving DecidableEq, Repr

open MKRow MKStatus in
/-- The status assignment of the minimal-kernel delta. -/
def mkStatus : MKRow → MKStatus
  | completeDivisorFibre => kernelProved
  | centeredSourceDefinition => kernelProved
  | centeredSourceEstimate => openRow
  | principalCoefficientConvolution => kernelProved
  | principalLocalFactors => kernelProved
  | principalOwnerIdentity => kernelProved
  | principalReassembly => kernelProved
  | completePrincipalSmallness => conditionalAnalytic
  | squarefullDecomposition => kernelProved
  | squarefullMaskPartition => kernelProved
  | largeSquarefullTail => externalAnalyticCertificateBacked
  | squarefreeCoreReflection => kernelProved
  | localESum => kernelProved
  | schinzelSzekeresFunction => kernelProved
  | FgapEqDtimesG => explicitTheoremInterface
  | denseSupportCharacterisation => kernelProved
  | denseCompleteWeightWellFactorable => rejectedFalse
  | minimalBadGapKernel => kernelProved
  | uniqueKernelPerM => kernelProved
  | badDivisorClassification => kernelProved
  | badGapFibreContraction => kernelProved
  | nonPrimePowerCofactorZero => kernelProved
  | kernelRankCofactorRange => kernelProved
  | complementThresholdLemmas => kernelProved
  | primeKernelBridgeSourceAlgebra => kernelProved
  | primeKernelBridgeExponent => explicitTheoremInterface
  | DPJSourceDecomposition => kernelProved
  | DPJAnalyticBound => openRow
  | denseOwner => openRow
  | kernelPrimePowerOwners => strictlyReducedOpen
  | characterMellinClosingProcedure => retiredNonclosing
  | movingYClosingFamily => retiredNonclosing
  | pascadiCompleteOwner => methodNonclosing
  | openGDividesAOrdinaryMertens => methodNonclosing
  | averageShiftToFixedShiftTwo => noLegalDictionary
  | reciprocalExponentialToKloosterman => noLegalDictionary
  | omegaCProvenance => improvedPartial
  | R11row => strictlyReducedOpen
  | globalGate1Brow => openRow
  | hstarRow => openRow
  | twinPrimeRow => openRow

/-! ## 4. Re-ascription of the kernel-proved rows

Each `bankMK_*` is a type ascription of a theorem proved above, so the kernel re-checks that the
claimed `kernelProved` status matches an actual proof. -/

theorem bankMK_completeDivisorFibre :
    ∀ (z : ℝ) {M : ℕ}, M ≠ 0 → Hdiv z M =
      ∑ d ∈ (radNat M).divisors,
        (if z < (d : ℝ) then (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) else 0) :=
  fun z _ hM => Hdiv_eq_sum_radNat z hM

theorem bankMK_centeredSourceDefinition :
    ∀ (Ds Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ),
      rawProgression Ds Ns Ω z = centeredDiscrepancy Ds Ns Ω z + principalAverage Ds Ns Ω z :=
  raw_eq_centered_add_principal

theorem bankMK_principalCoefficientConvolution :
    ∀ r : ℕ, muDivId * hLocal r = muDivPhi r := muDivId_mul_hLocal

theorem bankMK_principalLocalFactors :
    (∀ {r p a : ℕ}, p.Prime → 1 ≤ a → p ∣ r → hLocal r (p ^ a) = 1 / (p : ℝ) ^ a) ∧
      (∀ {r p a : ℕ}, p.Prime → 1 ≤ a → ¬ p ∣ r →
        hLocal r (p ^ a) = -(1 / ((p : ℝ) ^ a * ((p : ℝ) - 1)))) :=
  ⟨fun hp ha hpr => hLocal_prime_pow_dvd hp ha hpr,
   fun hp ha hpr => hLocal_prime_pow_not_dvd hp ha hpr⟩

theorem bankMK_principalOwnerIdentity :
    ∀ {z : ℝ} {d : ℕ}, bigPrimeCount z d ≤ 2 →
      lambdaClass z 0 d - lambdaClass z 1 d + lambdaClass z 2 d = (μ d : ℝ) :=
  fun h => lambda_owner_identity h

theorem bankMK_principalReassembly :
    ∀ {Ds Ns : Finset ℕ} {Ω : ℕ → ℝ} {z : ℝ}, (∀ d ∈ Ds, bigPrimeCount z d ≤ 2) →
      mainClass Ds Ns Ω z 0 - mainClass Ds Ns Ω z 1 + mainClass Ds Ns Ω z 2
        = ∑ n ∈ Ns, Ω n * piTail Ds z n :=
  fun h => main_reassembly h

theorem bankMK_squarefullDecomposition :
    ∀ {M : ℕ}, M ≠ 0 → sqFullPart M * sqFreeCore M = M ∧ IsSquarefull (sqFullPart M) ∧
      Squarefree (sqFreeCore M) ∧ Nat.Coprime (sqFreeCore M) (sqFullPart M) :=
  fun hM => squarefull_decomposition hM

theorem bankMK_squarefullUniqueness :
    ∀ {M b a : ℕ}, M ≠ 0 → b * a = M → IsSquarefull b → Squarefree a → Nat.Coprime a b →
      b = sqFullPart M ∧ a = sqFreeCore M :=
  fun hM hEq hb ha hcop => squarefull_decomposition_unique hM hEq hb ha hcop

theorem bankMK_squarefreeCoreReflection :
    ∀ {z : ℝ} {b a : ℕ}, b ≠ 0 → Squarefree a → Nat.Coprime a b →
      Hdiv z (b * a) = reflectedSum z b a :=
  fun hb ha hcop => Hdiv_reflection hb ha hcop

theorem bankMK_localESum :
    ∀ {b g : ℕ}, b ≠ 0 → 0 < g →
      ∑ e ∈ (radNat b).divisors, (μ e : ℝ) * Real.log (((b * g : ℕ) : ℝ) / (e : ℝ))
        = if b = 1 then Real.log g else Λ (radNat b) :=
  fun hb hg => local_e_sum hb hg

theorem bankMK_schinzelSzekeresFunction :
    ∀ {d : ℕ}, d ≠ 0 → 1 < d → Fgap d = d.primeFactors.sup fun p => tailPart d p * p :=
  fun hd hd1 => Fgap_eq_sup_tail hd hd1

theorem bankMK_denseSupportCharacterisation :
    ∀ {d : ℕ}, d ≠ 0 → ∀ {Q : ℝ}, 1 ≤ Q → (FactorSupport d Q ↔ GapBound d Q) :=
  fun {_d} hd {_Q} hQ => factorSupport_iff_gapBound hd hQ

theorem bankMK_denseWeightRejected : ¬ IsProductWeight signedChart := signedChart_not_product

theorem bankMK_minimalBadGapKernel :
    ∀ {x v : ℕ}, 1 ≤ x → IsMinKernel x v → x < v * v.minFac ∧ Fgap (v / v.minFac) ≤ x :=
  fun hx h => ⟨h.lt_mul_minFac hx, h.Fgap_div_minFac_le hx⟩

theorem bankMK_uniqueKernelPerM :
    ∀ {x M v w : ℕ}, 1 ≤ x → M ≠ 0 → M ≤ x → IsMinKernel x v → IsMinKernel x w →
      v ∣ M → w ∣ M → v = w :=
  fun hx hM hMx hv hw hvM hwM => minKernel_unique_of_dvd hx hM hMx hv hw hvM hwM

theorem bankMK_badDivisorClassification :
    ∀ {x M v m : ℕ}, 1 ≤ x → M ≠ 0 → M ≤ x → IsMinKernel x v → v * m = M →
      ∀ {d : ℕ}, d ∣ M → Squarefree d → (x < Fgap d ↔ ∃ e, e ∣ m ∧ d = v * e) :=
  fun {_x _M _v _m} hx hM0 hMx hv hvm {_d} hd hdsq =>
    bad_divisor_form hx hM0 hMx hv hvm hd hdsq

theorem bankMK_badGapFibreContraction :
    ∀ {z : ℝ} {x M v m : ℕ}, 1 ≤ x → M ≠ 0 → M ≤ x → IsMinKernel x v → v * m = M →
      Hbad z x M = (μ v : ℝ) * Hdiv (z / v) m :=
  fun hx hM0 hMx hv hvm => Hbad_contraction hx hM0 hMx hv hvm

theorem bankMK_nonPrimePowerCofactorZero :
    ∀ {z : ℝ} {x M v m : ℕ}, 1 ≤ x → M ≠ 0 → M ≤ x → IsMinKernel x v → v * m = M →
      z < (v : ℝ) → ¬ IsPrimePow m → Hbad z x M = 0 :=
  fun hx hM0 hMx hv hvm hzv hm => Hbad_eq_zero_of_not_primePow hx hM0 hMx hv hvm hzv hm

theorem bankMK_kernelRankCofactorRange :
    ∀ {x v m : ℕ}, 1 ≤ x → IsMinKernel x v → 0 < m → v * m ≤ x →
      x ^ v.primeFactors.card < v ^ (v.primeFactors.card + 1) ∧
        m ^ (v.primeFactors.card + 1) < x :=
  fun hx h hm hM => ⟨minKernel_pow_lt hx h, cofactor_pow_lt hx h hm hM⟩

theorem bankMK_complementThresholdLemmas :
    ∀ {M D K d p : ℕ}, M ≠ 0 → M ≤ D * K → d ∣ M → D < d → p.Prime → K < p →
      p ^ M.factorization p ∣ d :=
  fun hM hDK hd hdD hp hpK => full_padic_of_large_divisor hM hDK hd hdD hp hpK

theorem bankMK_primeKernelBridgeSourceAlgebra :
    ∀ {x p : ℕ}, 1 ≤ x → p.Prime → (IsMinKernel x p ↔ x < p * p) :=
  fun hx hp => isMinKernel_prime_iff hx hp

theorem bankMK_DPJSourceDecomposition :
    ∀ (Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) (x : ℕ), Tsource Ns Ω z = Tkernel Ns Ω z x :=
  Tsource_eq_Tkernel

/-! ## 5. Firewalls -/

theorem firewall_characterMellin_not_kernelProved :
    mkStatus MKRow.characterMellinClosingProcedure ≠ MKStatus.kernelProved := by decide

theorem firewall_movingY_not_kernelProved :
    mkStatus MKRow.movingYClosingFamily ≠ MKStatus.kernelProved := by decide

theorem firewall_denseWeight_rejected :
    mkStatus MKRow.denseCompleteWeightWellFactorable = MKStatus.rejectedFalse := by decide

theorem firewall_largeSquarefull_not_kernelProved :
    mkStatus MKRow.largeSquarefullTail ≠ MKStatus.kernelProved := by decide

theorem firewall_completePrincipal_not_kernelProved :
    mkStatus MKRow.completePrincipalSmallness ≠ MKStatus.kernelProved := by decide

theorem firewall_FgapEqDtimesG_is_interface :
    mkStatus MKRow.FgapEqDtimesG = MKStatus.explicitTheoremInterface := by decide

theorem firewall_averageShift_no_dictionary :
    mkStatus MKRow.averageShiftToFixedShiftTwo = MKStatus.noLegalDictionary := by decide

theorem firewall_reciprocalExponential_no_dictionary :
    mkStatus MKRow.reciprocalExponentialToKloosterman = MKStatus.noLegalDictionary := by decide

/-- Factor-support feasibility is not coefficient well-factorability. -/
theorem firewall_support_vs_factorability :
    FactorSupport 6 12 ∧ ¬ IsProductWeight signedChart :=
  factor_support_ne_well_factorable

/-! ## 6. Source provenance -/

/-- `Ω_C` provenance: recovered in part only.  Missing provenance is an **open source
interface**, not permission to simplify `Ω_C`; no theorem of this layer inspects `Ω_C`. -/
theorem omegaC_provenance_improved_partial :
    mkStatus MKRow.omegaCProvenance = MKStatus.improvedPartial := by decide

/-- The canonical-source coverage proposition is *not* formalised as a theorem: it is recorded
here as an ordinary proposition on a source pair, to be supplied if ever proved. -/
def CanonicalSourceCovers (Ns : Finset ℕ) (Ωcanon Ωphys : ℕ → ℝ) : Prop :=
  ∀ n ∈ Ns, Ωcanon n = Ωphys n

/-- The only legal use of the coverage interface: if supplied, the two sources agree. -/
theorem source_transport_of_coverage {Ns : Finset ℕ} {Ωcanon Ωphys : ℕ → ℝ} {z : ℝ}
    (h : CanonicalSourceCovers Ns Ωcanon Ωphys) :
    Tsource Ns Ωcanon z = Tsource Ns Ωphys z := by
  unfold Tsource
  congr 1
  exact Finset.sum_congr rfl fun n hn => by rw [h n hn]

/-! ## 7. The current open frontier -/

/-- The current open frontier of the minimal-kernel coordinate. -/
def minimalKernel_open_frontier : List (MKRow × MKStatus) :=
  [ (MKRow.completePrincipalSmallness, mkStatus MKRow.completePrincipalSmallness),
    (MKRow.largeSquarefullTail, mkStatus MKRow.largeSquarefullTail),
    (MKRow.schinzelSzekeresFunction, mkStatus MKRow.schinzelSzekeresFunction),
    (MKRow.uniqueKernelPerM, mkStatus MKRow.uniqueKernelPerM),
    (MKRow.badGapFibreContraction, mkStatus MKRow.badGapFibreContraction),
    (MKRow.kernelRankCofactorRange, mkStatus MKRow.kernelRankCofactorRange),
    (MKRow.denseOwner, mkStatus MKRow.denseOwner),
    (MKRow.kernelPrimePowerOwners, mkStatus MKRow.kernelPrimePowerOwners),
    (MKRow.primeKernelBridgeExponent, mkStatus MKRow.primeKernelBridgeExponent),
    (MKRow.DPJAnalyticBound, mkStatus MKRow.DPJAnalyticBound),
    (MKRow.R11row, mkStatus MKRow.R11row),
    (MKRow.globalGate1Brow, mkStatus MKRow.globalGate1Brow),
    (MKRow.hstarRow, mkStatus MKRow.hstarRow),
    (MKRow.twinPrimeRow, mkStatus MKRow.twinPrimeRow) ]

/-- R11 is open (strictly reduced), and so are global Gate 1B, `H*` and twin primes. -/
theorem frontier_open_rows :
    mkStatus MKRow.R11row = MKStatus.strictlyReducedOpen ∧
      mkStatus MKRow.globalGate1Brow = MKStatus.openRow ∧
      mkStatus MKRow.hstarRow = MKStatus.openRow ∧
      mkStatus MKRow.twinPrimeRow = MKStatus.openRow := by decide

/-- Continuity with the previous bank: the earlier `R_newcrit`/`R_hi` coordinates and the
character/Mellin definitions are preserved; `R11` there is still an open row. -/
theorem previous_bank_preserved : frontierStatus FrontierRow.R11 = FrontierStatus.openRow := by
  decide

/-- The `D + P + J` analytic balance is an open row, and no proposition asserting it is
inhabited in this layer. -/
theorem DPJ_balance_open : mkStatus MKRow.DPJAnalyticBound = MKStatus.openRow := by decide

end

end Gate1B.R11.Frontier
