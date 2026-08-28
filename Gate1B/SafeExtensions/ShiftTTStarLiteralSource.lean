/-
# Gate 1B v13 — literal shifted TT\* source, shift-source-linked character moment
and finite SHAPE metadata

**Status: identities PROVED; the literal source certificate and the analytic
moment bound are UNINHABITED.**

Contents.

*§10 Literal source.*  `ShiftTTStarLiteralSourceCertificate` says that the
allowed multiplier tuples of a `PhysicalFourMultiplierSource` are *exactly* the
edge tuples `(Θ(B₁,B₂), Θ(B₂,B₃), Θ(B₃,B₄), Θ(B₄,B₁))` of a prescribed finite
set of four-cycles, together with injectivity of that edge map on the cycle
set.  The certificate is **non-circular**: it mentions no estimate, only the
source dictionary.  It is never inhabited for the actual TT\* source here.

*§11 Shift-source-linked moment.*  `shiftSourceLinkedCharacterMoment` is the sum
over the *cycles* (not over a Cartesian product of four free multipliers) of the
source weight against the **proved** four-cycle discriminant `fourCycleDisc`.
`shiftMult4CharacterMoment_eq_linked` proves it equals the physical moment under
the certificate.  `ShiftSourceLinkedCharacterBound` is the UNINHABITED analytic
interface.

*§12 SHAPE metadata.*  `DeterminantCharacterShape`, `MonomialCharacterShape`,
`ReciprocalMultilinearShape` are finite metadata predicates only.  We prove that
the four-cycle **determinant** has determinant shape, and — as a counterguard —
that the four-cycle **trace** does not: shape metadata may not be transported
between the two.
-/
import Gate1B.SafeExtensions.ShiftMultiplierSource

namespace Gate1B.SafeExtensions

open Finset Gate1B.SafeAlgebra

section LiteralSource

variable {R : Type*} [CommRing R] [DecidableEq R]
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The four multipliers read off the four edges of a corner four-cycle. -/
def edgeTuple (Theta : B → B → R) (b : B × B × B × B) : R × R × R × R :=
  (Theta b.1 b.2.1, Theta b.2.1 b.2.2.1, Theta b.2.2.1 b.2.2.2, Theta b.2.2.2 b.1)

/-- **LITERAL SHIFTED TT\* SOURCE CERTIFICATE (never inhabited here).**

Non-circular source dictionary: the physical multiplier tuples are exactly the
edge tuples of the prescribed corner four-cycles, and distinct cycles give
distinct tuples.  No estimate appears. -/
structure ShiftTTStarLiteralSourceCertificate (S : PhysicalFourMultiplierSource R)
    (Theta : B → B → R) (cycles : Finset (B × B × B × B)) : Prop where
  /-- SOURCE DICTIONARY — the allowed tuples are exactly the cycle edge tuples. -/
  tuples_eq : S.allowedTuples = cycles.image (edgeTuple Theta)
  /-- SOURCE DICTIONARY — the edge map is injective on the cycle set. -/
  edge_injOn : Set.InjOn (edgeTuple Theta) cycles

/-- **The shift-source-linked character moment**: a sum over the physical corner
four-cycles of the source weight against the proved four-cycle discriminant. -/
noncomputable def shiftSourceLinkedCharacterMoment (S : PhysicalFourMultiplierSource R)
    (Theta : B → B → R) (cycles : Finset (B × B × B × B)) (phi : R → ℂ) (h1 h2 h3 h4 : R) : ℂ :=
  ∑ b ∈ cycles, S.sourceWeight (edgeTuple Theta b) *
    phi (fourCycleDisc (Theta b.1 b.2.1) (Theta b.2.1 b.2.2.1) (Theta b.2.2.1 b.2.2.2)
      (Theta b.2.2.2 b.1) h1 h2 h3 h4)

omit [Fintype B] [DecidableEq B] in
/-- **Exact identity.**  Under the literal source certificate the physical
four-multiplier moment equals the shift-source-linked moment. -/
theorem shiftMult4CharacterMoment_eq_linked (S : PhysicalFourMultiplierSource R)
    (Theta : B → B → R) (cycles : Finset (B × B × B × B)) (phi : R → ℂ) (h1 h2 h3 h4 : R)
    (hcert : ShiftTTStarLiteralSourceCertificate S Theta cycles) :
    S.shiftMult4CharacterMoment phi h1 h2 h3 h4
      = shiftSourceLinkedCharacterMoment S Theta cycles phi h1 h2 h3 h4 := by
  classical
  unfold PhysicalFourMultiplierSource.shiftMult4CharacterMoment
    shiftSourceLinkedCharacterMoment
  rw [hcert.tuples_eq, Finset.sum_image hcert.edge_injOn]
  rfl

/-- **UNINHABITED ANALYTIC INTERFACE.**  A bound for the shift-source-linked
character moment.  Nothing in this bank constructs it. -/
structure ShiftSourceLinkedCharacterBound (S : PhysicalFourMultiplierSource R)
    (Theta : B → B → R) (cycles : Finset (B × B × B × B)) (phi : R → ℂ) (h1 h2 h3 h4 : R)
    (target : ℝ) : Prop where
  /-- EXTERNAL ANALYTIC INPUT — never supplied here. -/
  moment_le : ‖shiftSourceLinkedCharacterMoment S Theta cycles phi h1 h2 h3 h4‖ ≤ target

omit [Fintype B] [DecidableEq B] in
/-- **Non-vacuity guard.**  A negative target is impossible. -/
theorem shiftSourceLinkedCharacterBound_not_vacuous (S : PhysicalFourMultiplierSource R)
    (Theta : B → B → R) (cycles : Finset (B × B × B × B)) (phi : R → ℂ) (h1 h2 h3 h4 : R) :
    ¬ ShiftSourceLinkedCharacterBound S Theta cycles phi h1 h2 h3 h4 (-1) := by
  intro h
  have := h.moment_le
  have h0 := norm_nonneg (shiftSourceLinkedCharacterMoment S Theta cycles phi h1 h2 h3 h4)
  linarith

omit [Fintype B] [DecidableEq B] in
/-- Empty cycle set gives no moment (sanity identity). -/
theorem shiftSourceLinkedCharacterMoment_empty (S : PhysicalFourMultiplierSource R)
    (Theta : B → B → R) (phi : R → ℂ) (h1 h2 h3 h4 : R) :
    shiftSourceLinkedCharacterMoment S Theta ∅ phi h1 h2 h3 h4 = 0 := by
  unfold shiftSourceLinkedCharacterMoment
  rw [Finset.sum_empty]

end LiteralSource

/-! ### §12 SHAPE metadata (no certificate asserted) -/

section Shapes

variable {R : Type*} [CommRing R]

/-- **SHAPE metadata.**  A four-multiplier form has *determinant shape* if it is
the plain product of the four multipliers. -/
def DeterminantCharacterShape (F : R → R → R → R → R) : Prop :=
  ∀ a1 a2 a3 a4, F a1 a2 a3 a4 = a1 * a2 * a3 * a4

/-- **SHAPE metadata.**  A four-multiplier form has *monomial shape* if it is a
scalar multiple of a fixed monomial in the four multipliers. -/
def MonomialCharacterShape (F : R → R → R → R → R) : Prop :=
  ∃ (c : R) (e1 e2 e3 e4 : ℕ), ∀ a1 a2 a3 a4,
    F a1 a2 a3 a4 = c * a1 ^ e1 * a2 ^ e2 * a3 ^ e3 * a4 ^ e4

/-- **SHAPE metadata.**  A four-multiplier form is *reciprocal-multilinear* if it
is invariant under reversing the cyclic order of the multipliers. -/
def ReciprocalMultilinearShape (F : R → R → R → R → R) : Prop :=
  ∀ a1 a2 a3 a4, F a1 a2 a3 a4 = F a4 a3 a2 a1

/-- Determinant shape implies monomial shape. -/
theorem monomialShape_of_determinantShape {F : R → R → R → R → R}
    (h : DeterminantCharacterShape F) : MonomialCharacterShape F :=
  ⟨1, 1, 1, 1, 1, fun a1 a2 a3 a4 => by rw [h a1 a2 a3 a4]; ring⟩

/-- The four-cycle determinant has determinant shape (from the proved
`fourCycle_det`). -/
theorem fourCycle_det_determinantShape [DecidableEq R] (h1 h2 h3 h4 : R) :
    DeterminantCharacterShape
      (fun a1 a2 a3 a4 => Matrix.det (cycleMatrix a1 a2 a3 a4 h1 h2 h3 h4)) :=
  fun a1 a2 a3 a4 => fourCycle_det a1 a2 a3 a4 h1 h2 h3 h4

/-- **SHAPE COUNTERGUARD.**  The four-cycle *trace* does not have determinant
shape, so shape metadata may not be transported from the determinant to the
trace. -/
theorem fourCycle_trace_not_determinantShape :
    ¬ DeterminantCharacterShape
        (fun a1 a2 a3 a4 : ℤ => Matrix.trace (cycleMatrix a1 a2 a3 a4 0 0 0 0)) := by
  intro h
  have h1 := h 1 1 1 1
  simp only [fourCycle_trace] at h1
  norm_num at h1

end Shapes

end Gate1B.SafeExtensions
