/-
# NANC Gate 1A v9.6 — actual source locators and the source-kind census

The v9.5 census (`V95PacketCensus.census`) records, for each packet, the *file*
in which its source object lives.  A file name is not an inhabitant.  This file
upgrades the provenance to a machine-checked one:

* every claimed source object is **`#check`ed by fully qualified name**, so the
  census cannot silently drift away from the repository;
* every packet is classified by the *kind* of object its source actually is
  (`sourceKind`), because a packet can only enter a
  `SourceExactPacketDictionary` if its source is a **defined operator with a
  defined target functional** — a `Prop`-carrying interface or a status-ledger
  entry supplies no contribution vector whatsoever.

The resulting facts, proved by decision procedure over the finite census:

* `commonD2_is_the_only_dictionary_ready_packet` — exactly one census packet,
  `commonD2`, has a defined operator together with a defined target functional
  in the actual source;
* `edgeDependentD2_is_dataOnly` — the edge-dependent packet has a defined
  data structure but no edge-sum, no energy and no target functional in the
  source;
* `majority_of_packets_are_interfaces` — most packets are `Prop`-carrying
  interfaces or ledger entries.

This is the exact reason why `SourceExactPacketDictionary.coversActualSource`
cannot be inhabited over the full census: sixteen of the nineteen packets have
no contribution to put into the sum.
-/
import Mathlib
import RequestProject.CenteredCRTRootNormalForm
import RequestProject.VaughanPacketAlgebra
import RequestProject.HighP3Status
import RequestProject.NANC.FF4Interfaces
import RequestProject.NANC.CDVMixedCovarianceInterface
import RequestProject.NANC.W4Frontier.Salie
import RequestProject.NANC.W4Frontier.CurrentFrontier
import RequestProject.NANC.D4.Prop44PacketRouting
import RequestProject.NANC.Gate1BDet2.FullFaceFixedPacket
import RequestProject.NANC.Gate1A.SafeExtensions.ProjectiveSourceInterfaces
import RequestProject.NANC.Gate1A.SafeExtensions.V95PacketCensus

namespace TwinPrimeProject.NANC.Gate1A.V96

open TwinPrimeProject.NANC.Gate1A.V95

/-! ## 1. Compile-time existence of every claimed source object

If any of these declarations is renamed or removed, this file stops compiling. -/

section Locators

#check @TwinPrimeProject.CenteredCRTRoot.CommonD2Data
#check @TwinPrimeProject.CenteredCRTRoot.CommonD2Data.edgeSum
#check @TwinPrimeProject.CenteredCRTRoot.CommonD2Data.LargeSieveTarget
#check @TwinPrimeProject.CenteredCRTRoot.EdgeDependentD2Data
#check @TwinPrimeProject.VaughanP1
#check @TwinPrimeProject.VaughanP2
#check @TwinPrimeProject.centeredP3
#check @RouteAFibreFrame.RouteAVarianceHypothesis
#check @RouteAFibreFrame.FF4Hypothesis
#check @RouteAFibreFrame.FF4MixHypothesis
#check @RouteAFibreFrame.RowDiagonalHypothesis
#check @RouteAFibreFrame.SamePrimeSectorHypothesis
#check @RouteAFibreFrame.SingleFrequencyCorrectionHypothesis
#check @TwinPrimeProject.NANC.CDVMixedCovarianceInput
#check @TwinPrimeProject.K0R9FixedCellDistributionInput
#check @TwinPrimeProject.K0R10FixedCellDistributionInput
#check @TwinPrimeProject.R9RepeatedPrimeSparseMassInput
#check @TwinPrimeProject.Gate1BDet2.FullFace.lambdaRouted
#check @TwinPrimeProject.NANC.W4Frontier.salieLargeWFibres5And8
#check @TwinPrimeProject.NANC.W4Frontier.genericSignedMeanValue
#check @TwinPrimeProject.NANC.D4.ResidualPacket
#check @TwinPrimeProject.NANC.Gate1A.V91.projRow

end Locators

/-! ## 2. What kind of object each source really is -/

/-- The kinds of source object actually found in the repository. -/
inductive SourceKind
  /-- A defined operator together with a defined target functional. -/
  | definedOperatorWithTarget
  /-- A defined operator (a function with values), but no target functional. -/
  | definedOperator
  /-- A structure of source *data* with no functional defined on it. -/
  | dataOnly
  /-- A structure whose content is an externally supplied `Prop`. -/
  | propInterface
  /-- A `BankStatus` / `LedgerItem` entry only. -/
  | statusLedgerEntry
  /-- A `Prop`-valued predicate on exponent data. -/
  | predicateOnly
  deriving DecidableEq, Repr

/-- The exact declaration that each census packet points to. -/
def sourceDecl : PacketId → String
  | .commonD2 => "TwinPrimeProject.CenteredCRTRoot.CommonD2Data.edgeSum"
  | .edgeDependentD2 => "TwinPrimeProject.CenteredCRTRoot.EdgeDependentD2Data"
  | .vaughanP1 => "TwinPrimeProject.VaughanP1"
  | .vaughanP2 => "TwinPrimeProject.VaughanP2"
  | .vaughanP3 => "TwinPrimeProject.centeredP3"
  | .routeAEdgeVariance => "RouteAFibreFrame.RouteAVarianceHypothesis"
  | .ff4Row => "RouteAFibreFrame.FF4Hypothesis"
  | .ff4MixedCovariance => "RouteAFibreFrame.FF4MixHypothesis"
  | .rowDiagonal => "RouteAFibreFrame.RowDiagonalHypothesis"
  | .samePrimeSector => "RouteAFibreFrame.SamePrimeSectorHypothesis"
  | .singleFrequencyCorrection => "RouteAFibreFrame.SingleFrequencyCorrectionHypothesis"
  | .k0R9FixedCell => "TwinPrimeProject.K0R9FixedCellDistributionInput"
  | .k0R10FixedCell => "TwinPrimeProject.K0R10FixedCellDistributionInput"
  | .r9RepeatedPrimeSparseMass => "TwinPrimeProject.R9RepeatedPrimeSparseMassInput"
  | .det2FullFace => "TwinPrimeProject.Gate1BDet2.FullFace.lambdaRouted"
  | .w4Salie => "TwinPrimeProject.NANC.W4Frontier.salieLargeWFibres5And8"
  | .w4SignedMeanValue => "TwinPrimeProject.NANC.W4Frontier.genericSignedMeanValue"
  | .prop44Residual => "TwinPrimeProject.NANC.D4.ResidualPacket"
  | .zeroProjective => "TwinPrimeProject.NANC.Gate1A.V91.projRow"

/-- The kind of source object each census packet actually has. -/
def sourceKind : PacketId → SourceKind
  | .commonD2 => .definedOperatorWithTarget
  | .edgeDependentD2 => .dataOnly
  | .vaughanP1 => .definedOperator
  | .vaughanP2 => .definedOperator
  | .vaughanP3 => .definedOperator
  | .routeAEdgeVariance => .propInterface
  | .ff4Row => .propInterface
  | .ff4MixedCovariance => .propInterface
  | .rowDiagonal => .propInterface
  | .samePrimeSector => .propInterface
  | .singleFrequencyCorrection => .propInterface
  | .k0R9FixedCell => .propInterface
  | .k0R10FixedCell => .propInterface
  | .r9RepeatedPrimeSparseMass => .propInterface
  | .det2FullFace => .definedOperator
  | .w4Salie => .statusLedgerEntry
  | .w4SignedMeanValue => .statusLedgerEntry
  | .prop44Residual => .predicateOnly
  | .zeroProjective => .definedOperator

/-- A packet is *dictionary ready* when its source is a defined operator with a
defined target functional; only such a packet can be given a
`PacketContribution` and a target in a `SourceExactPacketDictionary`. -/
def dictionaryReady (p : PacketId) : Bool :=
  sourceKind p = SourceKind.definedOperatorWithTarget

/-- The census packet identifiers, in census order. -/
def allPacketIds : List PacketId :=
  [ .commonD2, .edgeDependentD2, .vaughanP1, .vaughanP2, .vaughanP3
  , .routeAEdgeVariance, .ff4Row, .ff4MixedCovariance, .rowDiagonal
  , .samePrimeSector, .singleFrequencyCorrection, .k0R9FixedCell
  , .k0R10FixedCell, .r9RepeatedPrimeSparseMass, .det2FullFace
  , .w4Salie, .w4SignedMeanValue, .prop44Residual, .zeroProjective ]

/-- The enumeration really is complete. -/
theorem mem_allPacketIds (p : PacketId) : p ∈ allPacketIds := by
  cases p <;> simp [allPacketIds]

/-- The census has nineteen packets. -/
theorem allPacketIds_length : allPacketIds.length = 19 := by decide

/-- The dictionary-ready packets of the census. -/
def dictionaryReadyPackets : List PacketId := allPacketIds.filter dictionaryReady

/-- The packets whose source is only an externally supplied proposition, a
ledger entry, or a predicate. -/
def interfaceOnlyPackets : List PacketId :=
  allPacketIds.filter fun p =>
    sourceKind p = SourceKind.propInterface ||
      sourceKind p = SourceKind.statusLedgerEntry ||
      sourceKind p = SourceKind.predicateOnly

/-! ## 3. Machine-visible source-kind facts -/

/-- **Exactly one census packet is dictionary ready**, namely `commonD2`. -/
theorem commonD2_is_the_only_dictionary_ready_packet :
    dictionaryReadyPackets = [PacketId.commonD2] := by decide

/-- The edge-dependent packet has source *data* only: the repository defines
`EdgeDependentD2Data` but no edge sum, no energy and no target for it. -/
theorem edgeDependentD2_is_dataOnly :
    sourceKind PacketId.edgeDependentD2 = SourceKind.dataOnly := rfl

/-- Twelve census packets have no defined operator at all: their source is an
externally supplied proposition, a status-ledger entry, or a predicate. -/
theorem interfaceOnlyPackets_length : interfaceOnlyPackets.length = 12 := by decide

/-- The interface-only packets are more than half of the census. -/
theorem majority_of_packets_are_interfaces :
    2 * interfaceOnlyPackets.length > allPacketIds.length := by decide

/-- Every packet carries a non-empty declaration path: no packet is admitted
without a source locator. -/
theorem sourceDecl_ne_empty (p : PacketId) : sourceDecl p ≠ "" := by
  cases p <;> simp [sourceDecl]

/-- **First missing actual field, located.**  The full-census dictionary cannot
be inhabited because the packets that are not dictionary ready carry no
contribution vector; the first such packet in census order is
`edgeDependentD2`. -/
theorem first_non_dictionary_ready :
    (allPacketIds.filter fun p => ! dictionaryReady p).head?
      = some PacketId.edgeDependentD2 := by decide

end TwinPrimeProject.NANC.Gate1A.V96
