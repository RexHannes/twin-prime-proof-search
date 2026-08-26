/-
NANC V4 — Type-II reassembly interfaces.

PERMANENT FIREWALL:
    Gate1A + Gate1B  ≠  FULL FORD–MAYNARD TYPE II
without an explicit reassembly certificate.

Nothing in this file inhabits `FullFMTypeIIReassembly`.
-/
import Mathlib
import RequestProject.NANC.V4.FordMaynardPredicates

namespace NANC.V4

/-- Abstract, source-specific Gate-1A output: a bound for one designated pair of
coefficient sequences on one designated block. -/
structure Gate1AOutput where
  X : ℕ
  mRange : Finset ℕ
  nRange : Finset ℕ
  w : ℕ → ℂ
  xi0 : ℕ → ℂ
  kappa0 : ℕ → ℂ
  target : ℝ
  bound : SourceSpecificTypeII X mRange nRange w xi0 kappa0 target

/-- Abstract, source-specific Gate-1B output. -/
structure Gate1BOutput where
  X : ℕ
  mRange : Finset ℕ
  nRange : Finset ℕ
  w : ℕ → ℂ
  xi0 : ℕ → ℂ
  kappa0 : ℕ → ℂ
  target : ℝ
  bound : SourceSpecificTypeII X mRange nRange w xi0 kappa0 target

/-- The bookkeeping obligations that a genuine reassembly of the source packets
into the full Ford–Maynard Type-II hypothesis must discharge. -/
structure FMTypeIIReassemblyData where
  /-- Every dyadic Type-II block is covered. -/
  dyadicBlocksCovered : Prop
  /-- Arbitrary divisor-bounded `ξ, κ` are retained (no specialization). -/
  arbitraryCoefficientsRetained : Prop
  /-- No source packet is omitted. -/
  noSourcePacketOmitted : Prop
  /-- All exceptional sectors are routed. -/
  exceptionalSectorsRouted : Prop
  /-- All multiplicities are controlled. -/
  multiplicitiesControlled : Prop
  /-- The exact source main term is subtracted. -/
  exactMainSubtraction : Prop
  /-- No block is spent twice. -/
  noDoubleSpending : Prop

/-- **Full Ford–Maynard Type-II reassembly.**  UNINHABITED. -/
def FullFMTypeIIReassembly (D : FMTypeIIReassemblyData) : Prop :=
  D.dyadicBlocksCovered ∧ D.arbitraryCoefficientsRetained ∧ D.noSourcePacketOmitted ∧
    D.exceptionalSectorsRouted ∧ D.multiplicitiesControlled ∧ D.exactMainSubtraction ∧
    D.noDoubleSpending

/-- A reassembly certificate for a Gate-1A/Gate-1B pair: it *asserts* each of the
bookkeeping obligations.  UNINHABITED. -/
structure Gate1ABReassemblyCertificate (_A : Gate1AOutput) (_B : Gate1BOutput)
    (D : FMTypeIIReassemblyData) : Prop where
  covered : D.dyadicBlocksCovered
  arbitrary : D.arbitraryCoefficientsRetained
  complete : D.noSourcePacketOmitted
  routed : D.exceptionalSectorsRouted
  multiplicities : D.multiplicitiesControlled
  mainTerm : D.exactMainSubtraction
  noDouble : D.noDoubleSpending

/-- The certificate — and only the certificate — yields full reassembly. -/
theorem gate1AB_certificate_imp_full_reassembly {A : Gate1AOutput} {B : Gate1BOutput}
    {D : FMTypeIIReassemblyData} (h : Gate1ABReassemblyCertificate A B D) :
    FullFMTypeIIReassembly D :=
  ⟨h.covered, h.arbitrary, h.complete, h.routed, h.multiplicities, h.mainTerm, h.noDouble⟩

/-- **Firewall.**  Gate-1A and Gate-1B outputs exist for data on which the full
Ford–Maynard Type-II hypothesis is false; so possessing both packets does not,
by itself, give Type II. -/
theorem gate1A_gate1B_not_FMTypeII :
    ∃ (A : Gate1AOutput) (B : Gate1BOutput) (dwM dwN : ℕ → ℝ),
      A.X = B.X ∧ A.mRange = B.mRange ∧ A.nRange = B.nRange ∧ A.w = B.w ∧
      A.target = B.target ∧
      ¬ FMTypeIIAtScale A.X A.mRange A.nRange dwM dwN A.w A.target := by
  refine ⟨⟨1, {1}, {1}, fun _ => 1, fun _ => 0, fun _ => 0, 0, ?_⟩,
          ⟨1, {1}, {1}, fun _ => 1, fun _ => 0, fun _ => 0, 0, ?_⟩,
          fun _ => 1, fun _ => 1, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simp [SourceSpecificTypeII, typeIISum]
  · simp [SourceSpecificTypeII, typeIISum]
  · intro h
    have h1 := h (fun _ => 1) (fun _ => 1) (fun m _ => by norm_num) (fun m _ => by norm_num)
    simp [typeIISum, dyadicSupport] at h1

end NANC.V4
