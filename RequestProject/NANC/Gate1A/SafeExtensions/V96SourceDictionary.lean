/-
# NANC Gate 1A v9.6 — actual source inhabitance of the v9.5 certificate types

This file does two things, and keeps them strictly apart.

## A. Vacuity audit of the existing certificate types

Three of the v9.5 types turn out to carry *no* analytic content by themselves,
because the object they are supposed to describe is a free field of the
structure rather than a fixed external datum:

* `SourceExactPacketDictionary` has `actualSource` as a **field**, so it is
  inhabited for every element of every normed space
  (`sourceDictionary_inhabited_for_every_source`).  Its content lies entirely in
  *pinning* `actualSource` to an independently defined source
  (`PinsSource`).
* `GenericBPPBound` has `normalizedEnergy` as a **field**, so it has a vacuous
  inhabitant (`trivialGenericBPPBound`), and an inhabitant says nothing about
  any other energy functional (`genericBPP_says_nothing_about_other_energy`).
* `ESharpAdapter` is inhabited **exactly** when the packet bound already holds
  (`esharpAdapter_nonempty_iff`): the adapter is a repackaging of the estimate,
  not a source of it.

These are audit facts, not defects to be hidden: they say where the analytic
input must enter.

## B. A genuinely pinned actual-source dictionary

The one Gate 1A source object in this repository that is a *defined operator*
with a defined target functional is

    TwinPrimeProject.CenteredCRTRoot.CommonD2Data.edgeSum
    (RequestProject/CenteredCRTRootNormalForm.lean).

For it we construct, from the actual definition:

* `commonD2Dictionary` — a `SourceExactPacketDictionary` whose `actualSource` is
  literally the edge-sum vector `e ↦ ∑_{a,h} coeff a h · phase e a h`, with one
  packet per `(a, h)` pair, true coefficient `coeff a h`, and one analytic copy;
  the coverage identity `coversActualSource` is proved, not assumed
  (`commonD2Dictionary_pins`, `commonD2_source_partition`);
* `commonD2Multiplicity` — a `PacketMultiplicityCertificate` with exact
  multiplicity `1`;
* `commonD2Exhaustiveness` / `commonD2Closure` — an `AllMExhaustiveness` and a
  `Gate1AAllMClosureCertificate` **conditional on an explicit per-packet bound
  hypothesis**, with the honest record that the resulting final target is the
  triangle-inequality target `#packets · T`
  (`commonD2Closure_finalTarget_is_trivial`).  No cancellation and no
  `X^{o(1)}` saving is claimed or produced.

Nothing here upgrades a provisional item, and no analytic axiom is introduced.
-/
import Mathlib
import RequestProject.CenteredCRTRootNormalForm
import RequestProject.NANC.Gate1A.SafeExtensions.V95Closure
import RequestProject.NANC.Gate1A.SafeExtensions.V95Multiplicity

namespace TwinPrimeProject.NANC.Gate1A.V96

open Finset
open TwinPrimeProject.CenteredCRTRoot
open TwinPrimeProject.NANC.Gate1A.V95

/-! ## A. Vacuity audit -/

section Vacuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The dictionary type does not pin the source.**  For every element `S` of
every normed space there is a `SourceExactPacketDictionary` whose
`actualSource` is `S`.  Inhabiting the type is therefore *not* evidence of a
census; the evidence is the pinning equation below. -/
theorem sourceDictionary_inhabited_for_every_source (S : E) (T : ℝ) :
    ∃ Dct : SourceExactPacketDictionary (Fin 1) E, Dct.actualSource = S ∧ Dct.target = T := by
  refine ⟨{ coefficient := fun _ => 1
          , basePacket := fun _ => S
          , copies := fun _ => 1
          , actualSource := S
          , coversActualSource := by simp
          , target := T }, rfl, rfl⟩

/-- A dictionary **pins** an externally defined source when its `actualSource`
field is literally that source. -/
def PinsSource {Packet : Type*} [Fintype Packet]
    (Dct : SourceExactPacketDictionary Packet E) (S : E) : Prop :=
  Dct.actualSource = S

/-- The vacuous generic-engine inhabitant: `normalizedEnergy` is a free field,
so an inhabitant of `GenericBPPBound` exists with no analytic input at all. -/
def trivialGenericBPPBound : GenericBPPBound where
  normalizedEnergy := fun _ => 0
  genericTarget := 0
  bound := fun _ => le_refl 0

/-- `GenericBPPBound` is inhabited without any analytic theorem. -/
theorem genericBPPBound_vacuously_inhabited : Nonempty GenericBPPBound :=
  ⟨trivialGenericBPPBound⟩

/-- **An inhabitant of `GenericBPPBound` bounds only its own functional.**
There is an energy functional and an `E♯` source that the vacuous inhabitant
does not control, so the presence of a `GenericBPPBound` field in a closure
certificate is not an analytic input for the actual Gate 1A energy. -/
theorem genericBPP_says_nothing_about_other_energy :
    ∃ (G : GenericBPPBound) (f : ESharpSource → ℝ) (S : ESharpSource),
      ¬ f S ≤ G.genericTarget := by
  refine ⟨trivialGenericBPPBound, fun _ => 1,
    { Row := Fin 0, row := fun i => absurd i.2 (by simp), coeff := fun _ => 0 }, ?_⟩
  norm_num [trivialGenericBPPBound]

variable {Packet : Type*} [Fintype Packet] [DecidableEq Packet]

omit [NormedSpace ℂ E] [Fintype Packet] [DecidableEq Packet] in
/-- **The `E♯` adapter is exactly the packet bound.**  For a non-negative
generic target, an adapter for a packet exists iff the packet already satisfies
the bound.  The adapter therefore repackages an estimate; it never creates
one. -/
theorem esharpAdapter_nonempty_iff (contribution : Packet → E) (T : ℝ) (hT : 0 ≤ T)
    (p : Packet) :
    Nonempty (ESharpAdapter contribution T p) ↔ ‖contribution p‖ ≤ T := by
  constructor
  · rintro ⟨A⟩; exact A.packetBound hT
  · intro h
    exact ⟨{ relabelCost := 1
           , relabelCost_nonneg := zero_le_one
           , multiplierBound := 1
           , multiplierBound_nonneg := zero_le_one
           , sourceNormPreserved := by simpa using h
           , targetPreserved := by norm_num }⟩

end Vacuity

/-! ## B. The actual common-coefficient D2 source -/

open scoped Classical

variable (d : CommonD2Data)

/-- The actual source vector of a `CommonD2Data`: the family of edge sums. -/
noncomputable def commonD2Source : d.Edge → ℂ := fun e => d.edgeSum e

/-- **The source-exact packet dictionary of the actual common D2 source.**
One packet per `(pair, harmonic)`, coefficient the literal source coefficient,
base packet the literal phase vector, exactly one analytic copy, and
`actualSource` pinned to `commonD2Source`. -/
noncomputable def commonD2Dictionary (target : ℝ) :
    SourceExactPacketDictionary (d.Pair × d.Harm) (d.Edge → ℂ) where
  coefficient := fun p => d.coeff p.1 p.2
  basePacket := fun p => fun e => d.phase e p.1 p.2
  copies := fun _ => 1
  actualSource := commonD2Source d
  coversActualSource := by
    funext e
    simp [commonD2Source, CommonD2Data.edgeSum, Fintype.sum_prod_type, Finset.sum_apply]
  target := target

/-- The dictionary is **pinned** to the actual source definition. -/
theorem commonD2Dictionary_pins (target : ℝ) :
    PinsSource (commonD2Dictionary d target) (commonD2Source d) := rfl

/-- The literal packet contribution is `coeff a h · phase(·, a, h)`. -/
theorem commonD2Dictionary_contribution (target : ℝ) (p : d.Pair × d.Harm) :
    (commonD2Dictionary d target).contribution p
      = fun e => d.coeff p.1 p.2 * d.phase e p.1 p.2 := by
  funext e
  simp [SourceExactPacketDictionary.contribution, commonD2Dictionary]

/-- **Exact source assembly identity for the actual source.**  The actual edge
sums are the exact sum of the packet contributions, with true coefficients and
true multiplicities. -/
theorem commonD2_source_partition (target : ℝ) :
    commonD2Source d = ∑ p, (commonD2Dictionary d target).contribution p :=
  (commonD2Dictionary d target).actualSource_eq_sum_contribution

/-- Every packet of the actual dictionary has exactly one analytic copy. -/
theorem commonD2Dictionary_copies (target : ℝ) (p : d.Pair × d.Harm) :
    (commonD2Dictionary d target).copies p = 1 := rfl

/-- **Multiplicity certificate for the actual dictionary**: the analytic
occurrences are the packets themselves, so the exact multiplicity is `1`. -/
noncomputable def commonD2Multiplicity :
    PacketMultiplicityCertificate (d.Pair × d.Harm) (d.Pair × d.Harm) where
  rowOf := id
  D := 1
  fibre_card_le := by
    intro e
    have : packetCopies (id : d.Pair × d.Harm → d.Pair × d.Harm) e = {e} := by
      ext o
      simp [mem_packetCopies]
    simp [this]

/-- The multiplicity of the actual dictionary is exactly one, not merely
bounded. -/
theorem commonD2Multiplicity_exact (e : d.Pair × d.Harm) :
    (packetCopies (commonD2Multiplicity d).rowOf e).card = 1 := by
  have : packetCopies (commonD2Multiplicity d).rowOf e = {e} := by
    ext o
    simp [mem_packetCopies, commonD2Multiplicity]
  simp [this]

/-! ### Conditional exhaustiveness and closure for the actual source

The classification of the actual packets is *not* free: it needs a per-packet
bound.  That bound is supplied here as an explicit hypothesis, never as an
axiom, and the resulting closure target is the honest triangle-inequality
target. -/

/-- **ALL-`m` exhaustiveness for the actual common D2 dictionary, conditional on
an explicit per-packet bound.** -/
noncomputable def commonD2Exhaustiveness (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ p : d.Pair × d.Harm, ‖(commonD2Dictionary d T).contribution p‖ ≤ T) :
    AllMExhaustiveness (d.Pair × d.Harm) (d.Edge → ℂ) where
  dictionary := commonD2Dictionary d T
  genericTarget := T
  genericTarget_nonneg := hT
  genericTarget_le := le_refl _
  classify := fun p =>
    Sum.inl
      { relabelCost := 1
      , relabelCost_nonneg := zero_le_one
      , multiplierBound := 1
      , multiplierBound_nonneg := zero_le_one
      , sourceNormPreserved := by simpa using hbound p
      , targetPreserved := by norm_num }

/-- **ALL-`m` closure certificate for the actual common D2 source**, conditional
on the same explicit per-packet bound.  The final target is the
triangle-inequality target `#packets · T`. -/
noncomputable def commonD2Closure (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ p : d.Pair × d.Harm, ‖(commonD2Dictionary d T).contribution p‖ ≤ T) :
    Gate1AAllMClosureCertificate (d.Pair × d.Harm) (d.Edge → ℂ) where
  exhaustiveness := commonD2Exhaustiveness d T hT hbound
  genericBPP := trivialGenericBPPBound
  finalTarget := (Fintype.card (d.Pair × d.Harm) : ℝ) * T
  assembly_arith := le_refl _

/-- The certificate compiles to a bound on the **actual** source vector. -/
theorem commonD2Closure_bound (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ p : d.Pair × d.Harm, ‖(commonD2Dictionary d T).contribution p‖ ≤ T) :
    ‖commonD2Source d‖ ≤ (Fintype.card (d.Pair × d.Harm) : ℝ) * T :=
  Gate1AAllMClosureCertificate.toTarget (commonD2Closure d T hT hbound)

/-- **Honesty record.**  The closure target produced above is exactly the
triangle-inequality target: the compiler performs no cancellation, so the
Gate 1A target `M L⁴ / H` is reached only if the supplied per-packet bound is
already of strength `target / #packets`. -/
theorem commonD2Closure_finalTarget_is_trivial (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ p : d.Pair × d.Harm, ‖(commonD2Dictionary d T).contribution p‖ ≤ T) :
    (commonD2Closure d T hT hbound).finalTarget
      = (Fintype.card (d.Pair × d.Harm) : ℝ) * T := rfl

end TwinPrimeProject.NANC.Gate1A.V96
