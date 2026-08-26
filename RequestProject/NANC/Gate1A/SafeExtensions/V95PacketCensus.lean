/-
# NANC Gate 1A v9.5 — actual source packet census

This file is the *inventory* step.  It records, as machine-readable data, every
actual Gate 1A / high-P3 source object that exists in this repository, together
with its operator kind, coefficient kind, weight dependence, multiplicity
status, target normalization and route.

Two rules are enforced by construction:

* **No packet is merged with another merely because its exponent range
  matches.**  Two entries with the same ranges but different provenance are two
  entries.
* **Nothing important lives in a comment.**  Every field that the closure
  compiler reads is a field of `Gate1APacket`.

The census is *not* a proof that the list is complete: completeness is exactly
the field `SourceExactPacketDictionary.coversActualSource`, which has no
inhabitant.  What the census does give is a machine-visible list of the packets
that are currently unrouted.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V95

/-! ## 1. Enumerations -/

/-- Identifiers of the actual source objects found in the repository.  Each
constructor names a definition or interface that really exists here; the
provenance is carried in the `sourceFile` field of `Gate1APacket`. -/
inductive PacketId
  /-- `CommonD2Data` — common-coefficient D2 normal form. -/
  | commonD2
  /-- `EdgeDependentD2Data` — genuinely edge-dependent `W_{D,e}` coefficients. -/
  | edgeDependentD2
  /-- `VaughanP1` packet. -/
  | vaughanP1
  /-- `VaughanP2` packet. -/
  | vaughanP2
  /-- `VaughanP3` packet (centred form `centeredP3`). -/
  | vaughanP3
  /-- Route-A edge variance (`RouteAVarianceHypothesis`). -/
  | routeAEdgeVariance
  /-- One-row fourth moment (`FF4Hypothesis`). -/
  | ff4Row
  /-- Mixed-prime covariance (`FF4MixHypothesis`, `CDVMixedCovariance`). -/
  | ff4MixedCovariance
  /-- Row diagonal sector (`RowDiagonalHypothesis`). -/
  | rowDiagonal
  /-- Same-prime sector (`SamePrimeSectorHypothesis`). -/
  | samePrimeSector
  /-- Single-frequency correction (`SingleFrequencyCorrectionHypothesis`). -/
  | singleFrequencyCorrection
  /-- High-P3 fixed-cell distribution, `K0R9`. -/
  | k0R9FixedCell
  /-- High-P3 fixed-cell distribution, `K0R10`. -/
  | k0R10FixedCell
  /-- High-P3 repeated-prime sparse mass, `R9`. -/
  | r9RepeatedPrimeSparseMass
  /-- Determinant-2 full-face fixed packet. -/
  | det2FullFace
  /-- Salié fibres 5 and 8 of the W4 frontier. -/
  | w4Salie
  /-- Generic signed mean value of the W4 frontier. -/
  | w4SignedMeanValue
  /-- Prop-44 residual packet. -/
  | prop44Residual
  /-- Zero-reduced / projective packet. -/
  | zeroProjective
  deriving DecidableEq, Repr, Fintype

/-- The kind of operator carried by the packet. -/
inductive Gate1AOperatorKind
  | bilinearLargeSieve
  | fourthMomentGram
  | dispersionSquare
  | projectiveCrossedConvolution
  | localCorrection
  deriving DecidableEq, Repr

/-- The kind of coefficient carried by the packet. -/
inductive CoefficientKind
  | divisorBounded
  | smoothEnvelope
  | characterTwisted
  | indicator
  deriving DecidableEq, Repr

/-- How the row weight depends on the geometric edge. -/
inductive WeightDependence
  /-- One common weight vector for all edges. -/
  | common
  /-- A finite template decomposition `W_e = ∑_j α_j(e) W_j`. -/
  | finiteTemplate
  /-- Genuinely edge dependent (`W_{D,e}`). -/
  | edgeDependent
  deriving DecidableEq, Repr

/-- Exceptional sector tags. -/
inductive Gate1AException
  | sameQ | zeroFrequency | tZero | nonunit | properConductor | repeatedPrime
  | crossRolePrime | collision | principal | mixedZero | projective
  | trueLocalZero | smoothingBoundary | rankLoss | edgeDependentResidual
  | other
  deriving DecidableEq, Repr, Fintype

/-- Routing of a packet. -/
inductive PacketRoute
  | genericESharp
  | exceptional (kind : Gate1AException)
  /-- Not yet routed: this is the machine-visible open state. -/
  | unrouted
  deriving DecidableEq, Repr

/-- The target normalization a packet must return to. -/
inductive TargetNormalization
  /-- The Gate 1A / Route-A target `M L⁴ / H` (physical), `M H L⁴` normalized. -/
  | gate1A_ML4overH
  /-- The per-fibre `K D²` target. -/
  | perFibre_KD2
  /-- The global FF4 target `R M D²`. -/
  | globalFF4_RMD2
  deriving DecidableEq, Repr

/-! ## 2. The packet record -/

/-- Full identification of an actual source packet.  Every field the closure
compiler reads is present here; none is hidden in prose. -/
structure Gate1APacket where
  packetId : PacketId
  /-- Provenance: the repository file in which the object is defined. -/
  sourceFile : String
  operatorKind : Gate1AOperatorKind
  coefficientKind : CoefficientKind
  weightDependence : WeightDependence
  /-- Known multiplicity bound of analytic copies per physical row, or `none`
  when the multiplicity is not yet controlled. -/
  multiplicity : Option ℕ
  /-- The target normalization the packet must return to. -/
  target : TargetNormalization
  route : PacketRoute
  deriving DecidableEq, Repr

namespace Gate1APacket

/-- A packet is *classified* when it is routed either to the generic engine or
to a named exceptional sector. -/
def classified (p : Gate1APacket) : Bool :=
  match p.route with
  | .unrouted => false
  | _ => true

/-- A packet has *controlled multiplicity* when a numeric bound is recorded. -/
def multiplicityControlled (p : Gate1APacket) : Bool := p.multiplicity.isSome

end Gate1APacket

/-! ## 3. The census

Each entry corresponds to an object that exists in this repository.  Routes are
recorded conservatively: `unrouted` unless a proved theorem here justifies
otherwise. -/

/-- The v9.5 census of actual source packets. -/
def census : List Gate1APacket :=
  [ { packetId := .commonD2, sourceFile := "RequestProject/CenteredCRTRootNormalForm.lean",
      operatorKind := .bilinearLargeSieve, coefficientKind := .divisorBounded,
      weightDependence := .common, multiplicity := some 1,
      target := .gate1A_ML4overH, route := .genericESharp }
  , { packetId := .edgeDependentD2, sourceFile := "RequestProject/CenteredCRTRootNormalForm.lean",
      operatorKind := .bilinearLargeSieve, coefficientKind := .divisorBounded,
      weightDependence := .edgeDependent, multiplicity := none,
      target := .gate1A_ML4overH, route := .unrouted }
  , { packetId := .vaughanP1, sourceFile := "RequestProject/VaughanPacketAlgebra.lean",
      operatorKind := .bilinearLargeSieve, coefficientKind := .divisorBounded,
      weightDependence := .common, multiplicity := some 1,
      target := .gate1A_ML4overH, route := .genericESharp }
  , { packetId := .vaughanP2, sourceFile := "RequestProject/VaughanPacketAlgebra.lean",
      operatorKind := .bilinearLargeSieve, coefficientKind := .divisorBounded,
      weightDependence := .common, multiplicity := some 1,
      target := .gate1A_ML4overH, route := .genericESharp }
  , { packetId := .vaughanP3, sourceFile := "RequestProject/VaughanPacketAlgebra.lean",
      operatorKind := .bilinearLargeSieve, coefficientKind := .divisorBounded,
      weightDependence := .finiteTemplate, multiplicity := none,
      target := .gate1A_ML4overH, route := .unrouted }
  , { packetId := .routeAEdgeVariance, sourceFile := "RequestProject/NANC/FF4Interfaces.lean",
      operatorKind := .dispersionSquare, coefficientKind := .smoothEnvelope,
      multiplicity := none, weightDependence := .edgeDependent,
      target := .gate1A_ML4overH, route := .unrouted }
  , { packetId := .ff4Row, sourceFile := "RequestProject/NANC/FF4Interfaces.lean",
      operatorKind := .fourthMomentGram, coefficientKind := .divisorBounded,
      weightDependence := .common, multiplicity := some 1,
      target := .globalFF4_RMD2, route := .unrouted }
  , { packetId := .ff4MixedCovariance,
      sourceFile := "RequestProject/NANC/CDVMixedCovarianceInterface.lean",
      operatorKind := .fourthMomentGram, coefficientKind := .characterTwisted,
      weightDependence := .edgeDependent, multiplicity := none,
      target := .globalFF4_RMD2, route := .unrouted }
  , { packetId := .rowDiagonal, sourceFile := "RequestProject/NANC/FF4Interfaces.lean",
      operatorKind := .localCorrection, coefficientKind := .indicator,
      weightDependence := .common, multiplicity := some 1,
      target := .perFibre_KD2, route := .exceptional .principal }
  , { packetId := .samePrimeSector, sourceFile := "RequestProject/NANC/FF4Interfaces.lean",
      operatorKind := .localCorrection, coefficientKind := .indicator,
      weightDependence := .common, multiplicity := some 1,
      target := .perFibre_KD2, route := .exceptional .repeatedPrime }
  , { packetId := .singleFrequencyCorrection, sourceFile := "RequestProject/NANC/FF4Interfaces.lean",
      operatorKind := .localCorrection, coefficientKind := .indicator,
      weightDependence := .common, multiplicity := some 1,
      target := .perFibre_KD2, route := .exceptional .zeroFrequency }
  , { packetId := .k0R9FixedCell, sourceFile := "RequestProject/HighP3Status.lean",
      operatorKind := .dispersionSquare, coefficientKind := .indicator,
      weightDependence := .common, multiplicity := none,
      target := .gate1A_ML4overH, route := .unrouted }
  , { packetId := .k0R10FixedCell, sourceFile := "RequestProject/HighP3Status.lean",
      operatorKind := .dispersionSquare, coefficientKind := .indicator,
      weightDependence := .common, multiplicity := none,
      target := .gate1A_ML4overH, route := .unrouted }
  , { packetId := .r9RepeatedPrimeSparseMass, sourceFile := "RequestProject/HighP3Status.lean",
      operatorKind := .localCorrection, coefficientKind := .indicator,
      weightDependence := .common, multiplicity := some 1,
      target := .gate1A_ML4overH, route := .exceptional .repeatedPrime }
  , { packetId := .det2FullFace,
      sourceFile := "RequestProject/NANC/Gate1BDet2/FullFaceFixedPacket.lean",
      operatorKind := .bilinearLargeSieve, coefficientKind := .characterTwisted,
      weightDependence := .common, multiplicity := some 1,
      target := .gate1A_ML4overH, route := .exceptional .properConductor }
  , { packetId := .w4Salie, sourceFile := "RequestProject/NANC/W4Frontier/Salie.lean",
      operatorKind := .localCorrection, coefficientKind := .characterTwisted,
      weightDependence := .common, multiplicity := none,
      target := .perFibre_KD2, route := .unrouted }
  , { packetId := .w4SignedMeanValue,
      sourceFile := "RequestProject/NANC/W4Frontier/CurrentFrontier.lean",
      operatorKind := .dispersionSquare, coefficientKind := .divisorBounded,
      weightDependence := .common, multiplicity := none,
      target := .perFibre_KD2, route := .unrouted }
  , { packetId := .prop44Residual, sourceFile := "RequestProject/NANC/D4/Prop44PacketRouting.lean",
      operatorKind := .bilinearLargeSieve, coefficientKind := .divisorBounded,
      weightDependence := .common, multiplicity := none,
      target := .gate1A_ML4overH, route := .unrouted }
  , { packetId := .zeroProjective,
      sourceFile := "RequestProject/NANC/Gate1A/SafeExtensions/ProjectiveSourceInterfaces.lean",
      operatorKind := .projectiveCrossedConvolution, coefficientKind := .indicator,
      weightDependence := .common, multiplicity := some 1,
      target := .gate1A_ML4overH, route := .exceptional .projective }
  ]

/-- The unrouted packets of the census. -/
def unroutedPackets : List Gate1APacket := census.filter fun p => ! p.classified

/-- The packets whose analytic multiplicity is not yet controlled. -/
def uncontrolledMultiplicity : List Gate1APacket :=
  census.filter fun p => ! p.multiplicityControlled

/-! ## 4. Machine-visible census facts -/

/-- Every census entry is distinct: no two source objects were merged. -/
theorem census_nodup : census.Pairwise (· ≠ ·) := by decide

/-- The census is not fully routed. -/
theorem census_not_all_classified : unroutedPackets ≠ [] := by decide

/-- **First unclassified packet.**  The head of the unrouted list is the
edge-dependent `W_{D,e}` D2 packet. -/
theorem firstUnclassified_is_edgeDependentD2 :
    (unroutedPackets.head?).map Gate1APacket.packetId = some PacketId.edgeDependentD2 := by
  decide

/-- The first unclassified packet is genuinely edge dependent, and its
multiplicity is not controlled. -/
theorem firstUnclassified_weightDependence :
    (unroutedPackets.head?).map Gate1APacket.weightDependence
      = some WeightDependence.edgeDependent ∧
    (unroutedPackets.head?).bind Gate1APacket.multiplicity = none := by
  decide

/-- Its target normalization is the Gate 1A target `M L⁴ / H`. -/
theorem firstUnclassified_target :
    (unroutedPackets.head?).map Gate1APacket.target
      = some TargetNormalization.gate1A_ML4overH := by
  decide

/-- At least one census packet still has uncontrolled multiplicity. -/
theorem multiplicity_not_fully_controlled : uncontrolledMultiplicity ≠ [] := by decide

/-- Several *distinct* high-P3 operators remain unrouted: they are not all
duplicates of one generic `E♯` operator. -/
theorem multiple_highP3_operators_unrouted :
    3 ≤ unroutedPackets.length := by decide

end TwinPrimeProject.NANC.Gate1A.V95
