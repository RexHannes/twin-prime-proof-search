/-
# NANC Gate 1A v9.5 — adapters, exception certificates and the closure compilers

This file contains the *compilers*.  Every theorem is finite operator algebra;
no analytic estimate is created.

* `ESharpAdapter` routes a generic packet into the `E♯`/BPP engine with an
  explicit unitary-relabel cost and diagonal-multiplier bound, and proves that
  the packet returns to the **same** target.
* `ExceptionalPacketCertificate` routes an exceptional packet, and demands a
  *weighted global* bound at the same target — a local identity is not
  accepted.
* `allM_packet_exhaustive` is the central v9.5 theorem: if every packet carries
  one of the two certificates, every packet meets the Gate 1A target.  The
  classification is a *total function*, so there is no "all other cases"
  escape.
* `Gate1AAllMClosureCertificate.toTarget` and
  `Gate1ACleanP3ClosureCertificateV95.toTarget` are the two closure compilers.
  They are kept strictly separate: the clean-P3 compiler does not require the
  all-`m` census.

**Neither certificate is constructed.**  The census
(`V95PacketCensus.unroutedPackets`) exhibits the packets that block the
construction.
-/
import Mathlib
import RequestProject.NANC.Gate1A.SafeExtensions.PositiveRowEnlargement
import RequestProject.NANC.Gate1A.SafeExtensions.V95PacketCensus
import RequestProject.NANC.Gate1A.SafeExtensions.V95ESharpScope
import RequestProject.CenteredCRTRootNormalForm

namespace TwinPrimeProject.NANC.Gate1A.V95

open Finset

variable {Packet : Type*} [Fintype Packet] [DecidableEq Packet]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ## 1. Generic `E♯` adapter -/

/-- An adapter carrying one generic packet into the `E♯`/BPP engine.  Literal
equality is not required: an exact unitary/permutation relabelling together
with a row-diagonal conjugation is enough, but every cost is explicit. -/
structure ESharpAdapter (contribution : Packet → E) (genericTarget : ℝ) (p : Packet) where
  /-- Cost of the unitary/permutation relabelling (`1` for a genuine unitary). -/
  relabelCost : ℝ
  relabelCost_nonneg : 0 ≤ relabelCost
  /-- Norm bound of the row-diagonal multiplier. -/
  multiplierBound : ℝ
  multiplierBound_nonneg : 0 ≤ multiplierBound
  /-- The packet is carried into the engine with these costs. -/
  sourceNormPreserved : ‖contribution p‖ ≤ relabelCost * multiplierBound * genericTarget
  /-- The costs return the packet to the **same** target. -/
  targetPreserved : relabelCost * multiplierBound ≤ 1

omit [Fintype Packet] [DecidableEq Packet] [NormedSpace ℂ E] in
/-- An adapter yields the generic target for its packet. -/
theorem ESharpAdapter.packetBound {contribution : Packet → E} {genericTarget : ℝ} {p : Packet}
    (A : ESharpAdapter contribution genericTarget p) (hT : 0 ≤ genericTarget) :
    ‖contribution p‖ ≤ genericTarget := by
  refine A.sourceNormPreserved.trans ?_
  calc A.relabelCost * A.multiplierBound * genericTarget
      ≤ 1 * genericTarget := mul_le_mul_of_nonneg_right A.targetPreserved hT
    _ = genericTarget := one_mul _

/-! ## 2. Exceptional packet certificate -/

/-- A routed exceptional packet.  The bound is on the **weighted global** packet
contribution; a local identity such as `ρ_p(A) = -1/p` is not a substitute (see
`localRepair_does_not_imply_targetClosed`). -/
structure ExceptionalPacketCertificate (contribution : Packet → E) (gateTarget : ℝ)
    (p : Packet) where
  exceptionKind : Gate1AException
  /-- The exact router used. -/
  routerName : String
  /-- Absolute bound on the weighted global contribution. -/
  absoluteBound : ℝ
  routed : ‖contribution p‖ ≤ absoluteBound
  /-- The exceptional packet returns to the same Gate 1A target. -/
  sameTarget : absoluteBound ≤ gateTarget

omit [Fintype Packet] [DecidableEq Packet] [NormedSpace ℂ E] in
theorem ExceptionalPacketCertificate.packetBound {contribution : Packet → E} {gateTarget : ℝ}
    {p : Packet} (C : ExceptionalPacketCertificate contribution gateTarget p) :
    ‖contribution p‖ ≤ gateTarget :=
  C.routed.trans C.sameTarget

/-! ## 3. Classification and the central exhaustiveness theorem -/

/-- The classification of a packet: generic adapter or exceptional certificate.
There is deliberately no third constructor. -/
def PacketClassified (contribution : Packet → E) (genericTarget gateTarget : ℝ) (p : Packet) :
    Type _ :=
  ESharpAdapter contribution genericTarget p ⊕
    ExceptionalPacketCertificate contribution gateTarget p

omit [Fintype Packet] [DecidableEq Packet] [NormedSpace ℂ E] in
/-- **`allM_packet_exhaustive`.**  If every packet is classified, then every
packet meets the Gate 1A target.  The classification is a total function on the
packet type, which is exactly the "no unclassified packet" requirement. -/
theorem allM_packet_exhaustive {contribution : Packet → E} {genericTarget gateTarget : ℝ}
    (classify : ∀ p, PacketClassified contribution genericTarget gateTarget p)
    (hgen : 0 ≤ genericTarget) (hle : genericTarget ≤ gateTarget) (p : Packet) :
    ‖contribution p‖ ≤ gateTarget := by
  rcases classify p with A | C
  · exact (A.packetBound hgen).trans hle
  · exact C.packetBound

/-! ## 4. Source-exact packet dictionary -/

/-- The packet dictionary.  `coversActualSource` is an **equality**: every
actual source contribution appears with its true coefficient and its true
number of analytic copies.  There is no "up to ignored labels" field. -/
structure SourceExactPacketDictionary (Packet : Type*) [Fintype Packet]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  /-- The literal source coefficient of each packet. -/
  coefficient : Packet → ℂ
  /-- The base analytic object of each packet. -/
  basePacket : Packet → E
  /-- The number of analytic copies produced by ordered factorizations,
  HB/Vaughan labels, Mellin partitions and routing labels. -/
  copies : Packet → ℕ
  /-- The actual source. -/
  actualSource : E
  /-- Exact coverage, with true coefficients and true multiplicities. -/
  coversActualSource :
    actualSource = ∑ p, (copies p : ℂ) • (coefficient p • basePacket p)
  /-- The target normalization every packet must return to. -/
  target : ℝ

namespace SourceExactPacketDictionary

variable (Dct : SourceExactPacketDictionary Packet E)

/-- The literal contribution of a packet, copies included. -/
def contribution (p : Packet) : E := (Dct.copies p : ℂ) • (Dct.coefficient p • Dct.basePacket p)

omit [DecidableEq Packet] in
theorem actualSource_eq_sum_contribution :
    Dct.actualSource = ∑ p, Dct.contribution p :=
  Dct.coversActualSource

end SourceExactPacketDictionary

/-! ## 5. ALL-`m` exhaustiveness and closure -/

/-- The ALL-`m` source exhaustiveness certificate. -/
structure AllMExhaustiveness (Packet : Type*) [Fintype Packet] [DecidableEq Packet]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  dictionary : SourceExactPacketDictionary Packet E
  genericTarget : ℝ
  genericTarget_nonneg : 0 ≤ genericTarget
  genericTarget_le : genericTarget ≤ dictionary.target
  /-- Total classification: no unclassified packet is representable. -/
  classify : ∀ p, PacketClassified dictionary.contribution genericTarget dictionary.target p

namespace AllMExhaustiveness

variable (X : AllMExhaustiveness Packet E)

/-- Every packet of an exhaustive census meets the Gate 1A target. -/
theorem packet_bound (p : Packet) : ‖X.dictionary.contribution p‖ ≤ X.dictionary.target :=
  allM_packet_exhaustive X.classify X.genericTarget_nonneg X.genericTarget_le p

end AllMExhaustiveness

/-- The ALL-`m` closure certificate. -/
structure Gate1AAllMClosureCertificate (Packet : Type*) [Fintype Packet] [DecidableEq Packet]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  exhaustiveness : AllMExhaustiveness Packet E
  /-- The generic engine, as a certificate interface. -/
  genericBPP : GenericBPPBound
  /-- The final Gate 1A target. -/
  finalTarget : ℝ
  /-- Finite assembly arithmetic. -/
  assembly_arith :
    (Fintype.card Packet : ℝ) * exhaustiveness.dictionary.target ≤ finalTarget

/-- **The ALL-`m` closure compiler.**  Finite operator algebra only. -/
theorem Gate1AAllMClosureCertificate.toTarget
    (C : Gate1AAllMClosureCertificate Packet E) :
    ‖C.exhaustiveness.dictionary.actualSource‖ ≤ C.finalTarget := by
  rw [C.exhaustiveness.dictionary.actualSource_eq_sum_contribution]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun p _ => C.exhaustiveness.packet_bound p) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact C.assembly_arith

/-! ## 6. Clean-P3 closure, kept separate -/

/-- The clean-P3 closure certificate.  It uses positive row enlargement and a
generic bound; it does **not** require the all-`m` census. -/
structure Gate1ACleanP3ClosureCertificateV95 (Row : Type*) [Fintype Row] where
  enlargement : V94.PositiveRowEnlargement Row
  energy : Row → ℝ
  energy_nonneg : ∀ r, 0 ≤ energy r
  /-- The generic `E♯` bound. -/
  genericBound : ℝ
  esharp_controlled : ∑ r ∈ enlargement.esharpRows, energy r ≤ genericBound
  /-- The clean exception bank. -/
  exceptionalEnergy : ℝ
  exceptionBank : ℝ
  exceptional_controlled : exceptionalEnergy ≤ exceptionBank
  /-- The clean-P3 target. -/
  cleanP3Target : ℝ
  budget : genericBound + exceptionBank ≤ cleanP3Target

/-- **The clean-P3 closure compiler.** -/
theorem Gate1ACleanP3ClosureCertificateV95.toTarget {Row : Type*} [Fintype Row]
    (C : Gate1ACleanP3ClosureCertificateV95 Row) :
    (∑ r ∈ C.enlargement.cleanRows, C.energy r) + C.exceptionalEnergy ≤ C.cleanP3Target := by
  have h1 : ∑ r ∈ C.enlargement.cleanRows, C.energy r ≤ C.genericBound :=
    C.enlargement.cleanP3_energy_le_of_esharp_bound C.energy C.energy_nonneg C.genericBound
      C.esharp_controlled
  have h2 := C.exceptional_controlled
  have h3 := C.budget
  linarith

/-! ## 7. Target normalization bridges -/

/-- Normalized and physical Gate 1A targets: `M H L⁴ = (M L⁴ / H) · H²`. -/
theorem gate1A_target_bridge (M L H : ℝ) (hH : H ≠ 0) :
    M * H * L ^ 4 = (M * L ^ 4 / H) * H ^ 2 := by
  field_simp

/-- Re-export of the repository's target identity: under `D · H = L²` the
common-coefficient D2 target is exactly `M L⁴ / H`. -/
theorem commonD2_target_eq_ML4_over_H (d : TwinPrimeProject.CenteredCRTRoot.CommonD2Data)
    (hH : d.H ≠ 0) (hscale : d.D * d.H = d.L ^ 2) :
    d.M * d.L ^ 2 * d.D = d.M * d.L ^ 4 / d.H :=
  TwinPrimeProject.CenteredCRTRoot.CommonD2Data.target_eq_ML4_over_H d hH hscale

end TwinPrimeProject.NANC.Gate1A.V95
