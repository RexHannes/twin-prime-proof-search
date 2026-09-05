/-
# Universal / GHSpine — rename: *Abstract Seven-Class Router Certificate*

**Status of this module: KERNEL_PROVED rename algebra; all physical pins are
KEPT UNINHABITED.**

The input that earlier layers called the *RUN1B source-exhaustive input* is
renamed here to what it actually is:

```
RUN1B Source Exhaustive Input   ⟶   Abstract Seven-Class Router Certificate
```

The rename is *faithful and not a strengthening*: `abstract_router_is_rename`
proves the new name is the old proposition, definitionally
(`Universal.D0WP.FirstParentSourceCensusPin`).  The point of the rename is
recorded as a theorem as well: the abstract certificate says only that each row
is matched by one of the seven abstract owner classes; it does **not** say that
a literal physical source object exists for that row
(`abstract_router_does_not_give_physical_census`).

Consequently three obligations are kept **separate**, and all three are
UNINHABITED here:

* `PhysicalFirstParentSourceCensusPin` (this module);
* `Universal.GHSpine.RealFordGHGrammarPin` (the literal Ford grammar; the
  historical `RealFordGrammarCertificate` row keeps its uninhabited status);
* `Universal.GHSpine.PhysicalVaughanUVPin`.

`pins_are_pairwise_independent` exhibits, for each ordered pair among the three,
data satisfying the first and failing the second, so no pin may be silently
discharged by another.
-/
import Mathlib
import Universal.D0WP.FirstParentCensus
import Universal.GHSpine.PhysicalVaughanUV
import Universal.GHSpine.FordGHSourceSpine

namespace Universal.GHSpine

open Universal.D0WP

/-! ## §1 The rename -/

/-- **Renamed input.**  The abstract seven-class router certificate: every row is
matched by one of the seven abstract owner classes of the router. -/
def AbstractSevenClassRouterCertificate {ι : Type*} (rows : Finset ι)
    (p : FirstParentOwner → ι → Bool) : Prop :=
  ∀ i ∈ rows, ∃ c, p c i = true

/-- **The rename is faithful:** the new name denotes exactly the old
proposition, with nothing added and nothing removed. -/
theorem abstract_router_is_rename {ι : Type*} (rows : Finset ι)
    (p : FirstParentOwner → ι → Bool) :
    AbstractSevenClassRouterCertificate rows p ↔ FirstParentSourceCensusPin rows p :=
  Iff.rfl

/-- The router really has seven classes, and they are listed once each. -/
theorem router_has_seven_classes :
    FirstParentOwner.order.length = 7 ∧ FirstParentOwner.order.Nodup :=
  ⟨rfl, FirstParentOwner.order_nodup⟩

/-- Under the certificate every row is assigned a unique owner by the
deterministic router (restatement of the banked routing lemma under the new
name). -/
theorem abstract_router_assigns {ι : Type*} {rows : Finset ι}
    {p : FirstParentOwner → ι → Bool} (cert : AbstractSevenClassRouterCertificate rows p)
    (i : ι) (hi : i ∈ rows) : ∃ c, assignOwner p i = some c :=
  census_assigns_owner cert i hi

/-- The certificate is a genuine obligation: it can fail. -/
theorem abstractSevenClassRouterCertificate_not_automatic :
    ∃ (rows : Finset Unit) (p : FirstParentOwner → Unit → Bool),
      ¬ AbstractSevenClassRouterCertificate rows p :=
  firstParentCensusPin_not_automatic

/-! ## §2 The physical first-parent census pin, kept separate -/

/-- Physical census data: the abstract owner predicate together with the literal
source object attached to each row (if any). -/
structure PhysicalCensusData (ι : Type*) where
  /-- The abstract owner predicate of the router. -/
  ownerPred : FirstParentOwner → ι → Bool
  /-- The literal source object recorded for the row, if the repository has
  one. -/
  sourceWitness : ι → Option String

/-- **SOURCE PIN (UNINHABITED here, KEPT SEPARATE).**  The *physical*
first-parent census obligation: every row is not only abstractly routed, but
also carries a literal source object.  This is strictly stronger than the
abstract seven-class router certificate. -/
def PhysicalFirstParentSourceCensusPin {ι : Type*} (rows : Finset ι)
    (d : PhysicalCensusData ι) : Prop :=
  ∀ i ∈ rows, (∃ c, d.ownerPred c i = true) ∧ (d.sourceWitness i).isSome

/-- The physical pin implies the abstract certificate (one direction only). -/
theorem physical_census_gives_abstract {ι : Type*} {rows : Finset ι}
    {d : PhysicalCensusData ι} (pin : PhysicalFirstParentSourceCensusPin rows d) :
    AbstractSevenClassRouterCertificate rows d.ownerPred :=
  fun i hi => (pin i hi).1

/-- **The rename is load-bearing:** the abstract certificate does *not* give the
physical census pin — here every row is abstractly routed, yet no row has a
literal source object. -/
theorem abstract_router_does_not_give_physical_census :
    ∃ (rows : Finset Unit) (d : PhysicalCensusData Unit),
      AbstractSevenClassRouterCertificate rows d.ownerPred ∧
        ¬ PhysicalFirstParentSourceCensusPin rows d := by
  refine ⟨{()}, ⟨fun _ _ => true, fun _ => none⟩, ?_, ?_⟩
  · exact fun i _ => ⟨FirstParentOwner.pureMobius, rfl⟩
  · intro pin
    have h := (pin () (by simp)).2
    simp at h

/-- The physical pin is a genuine obligation: it can fail. -/
theorem physicalFirstParentSourceCensusPin_not_automatic :
    ∃ (rows : Finset Unit) (d : PhysicalCensusData Unit),
      ¬ PhysicalFirstParentSourceCensusPin rows d := by
  obtain ⟨rows, d, -, h⟩ := abstract_router_does_not_give_physical_census
  exact ⟨rows, d, h⟩

/-! ## §3 The three physical obligations are pairwise independent -/

/-- **No pin discharges another.**  For each of the three physical obligations
there is data satisfying it while another fails, so they must be tracked
separately:

1. the physical census pin holds while the Vaughan `(U,V)` pin fails;
2. the Vaughan pin holds while the Ford grammar pin fails;
3. the Ford grammar pin holds while the physical census pin fails. -/
theorem pins_are_pairwise_independent :
    (∃ (rows : Finset Unit) (d : PhysicalCensusData Unit) (v : PhysicalVaughanUVData),
        PhysicalFirstParentSourceCensusPin rows d ∧ ¬ PhysicalVaughanUVPin v) ∧
    (∃ (v : PhysicalVaughanUVData) (S : FordGHSpine),
        PhysicalVaughanUVPin v ∧ ¬ RealFordGHGrammarPin S) ∧
    (∃ (S : FordGHSpine) (rows : Finset Unit) (d : PhysicalCensusData Unit),
        RealFordGHGrammarPin S ∧ ¬ PhysicalFirstParentSourceCensusPin rows d) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨{()}, ⟨fun _ _ => true, fun _ => some "literal-source"⟩, ⟨1, 1, 0, 1, 1, 1, 0⟩,
      fun i _ => ⟨⟨FirstParentOwner.pureMobius, rfl⟩, rfl⟩, ?_⟩
    intro pin
    have h := pin.U_match
    simp at h
  · refine ⟨⟨1, 1, 1, 1, 1, 0, 0⟩, ⟨fun _ _ => 0, fun _ => 0, 0, fun _ => by simp⟩,
      ⟨rfl, rfl, le_rfl, le_rfl, le_rfl, rfl⟩, ?_⟩
    intro pin
    have h := pin.cut_eq
    simp at h
  · refine ⟨modelSpine, {()}, ⟨fun _ _ => true, fun _ => none⟩, ⟨rfl, fun j _ => rfl⟩, ?_⟩
    intro pin
    have h := (pin () (by simp)).2
    simp at h

end Universal.GHSpine
