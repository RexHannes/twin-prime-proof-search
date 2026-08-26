import RequestProject.NANC.Gate1BDet2.Gate1BExponentLedger

/-!
# Gate 1B / determinant-2 bank, Module 9: interfaces (declared, never inhabited)

Every proposition in this module is an **interface**: a named predicate that
this development neither proves nor assumes.  No `axiom` is introduced; the
interfaces are ordinary `Prop`-valued definitions, and the only theorems are
deterministic implications taking the interfaces as *hypotheses*.

Interfaces (analytic / source inputs, all open here):

* `ModulusFourierUniformity` — Davenport-type arbitrary-log Fourier uniformity
  in the modulus aspect;
* `NaturalMajorArcBound`;
* `PMS45Bound`;
* `OST45Bound`;
* `SourceExpectedTermIdentified`;
* `FixedSwitchedPacketReassembled`;
* `GlobalGate0Exhaustive`.

Target predicates: `NaturalPhysical45Bound`, `FixedSwitchedGate1BBound`.

**`Gate1BClosed`, `FullTypeIIBound` and `TwinPrimes` are declared and kept
uninhabited.**  In particular the step

  `FixedSwitchedGate1BBound → Gate1BClosed`

is *not* proved: it would need the missing Gate-0 source exhaustiveness, which
is not supplied.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. Analytic interfaces -/

/-- **EXTERNAL ANALYTIC INTERFACE.**  Davenport-type Fourier uniformity in the
modulus aspect: the modulus-Fourier quantity `S` is at most `bound`.  Not proved
here. -/
def ModulusFourierUniformity (S bound : ℝ) : Prop := |S| ≤ bound

/-- **EXTERNAL ANALYTIC INTERFACE.**  The natural major-arc bound. -/
def NaturalMajorArcBound (majorArc bound : ℝ) : Prop := |majorArc| ≤ bound

/-- **EXTERNAL ANALYTIC INTERFACE.**  The PMS45 minor-spectrum bound. -/
def PMS45Bound (minorSpectrum bound : ℝ) : Prop := |minorSpectrum| ≤ bound

/-- **EXTERNAL ANALYTIC INTERFACE.**  The OST45 bound. -/
def OST45Bound (ostQuantity bound : ℝ) : Prop := |ostQuantity| ≤ bound

/-! ## 2. Source interfaces -/

/-- **OPEN SOURCE INTERFACE.**  The source expected term has been identified,
i.e. it agrees with the banked centering term up to `tol`. -/
def SourceExpectedTermIdentified (sourceExpected centering tol : ℝ) : Prop :=
  |sourceExpected - centering| ≤ tol

/-- **OPEN SOURCE INTERFACE.**  The fixed switched packet has been reassembled:
the Gate-1B total splits exactly into the physical 4|5 quantity, the expected
term discrepancy, and a reassembly remainder controlled by `rem`. -/
def FixedSwitchedPacketReassembled
    (total physical sourceExpected centering rem : ℝ) : Prop :=
  |total - (physical + (sourceExpected - centering))| ≤ rem

/-- **OPEN SOURCE INTERFACE.**  Global Gate-0 exhaustiveness: every source cell
is covered by the direct / switched / skeleton decomposition.  Not supplied. -/
def GlobalGate0Exhaustive (uncoveredMass : ℝ) : Prop := uncoveredMass = 0

/-! ## 3. Target predicates -/

/-- The natural physical 4|5 bound. -/
def NaturalPhysical45Bound (physical bound : ℝ) : Prop := |physical| ≤ bound

/-- The fixed switched Gate-1B bound. -/
def FixedSwitchedGate1BBound (total bound : ℝ) : Prop := |total| ≤ bound

/-- **UNINHABITED.**  Gate 1B closure.  Never proved in this development. -/
def Gate1BClosed (gate1BTotal bound uncoveredMass : ℝ) : Prop :=
  |gate1BTotal| ≤ bound ∧ uncoveredMass = 0

/-- **UNINHABITED.**  The full Type II bound. -/
def FullTypeIIBound (typeIISum X delta : ℝ) : Prop := |typeIISum| ≤ X ^ (1 - delta)

/-- **UNINHABITED.**  The twin prime conjecture.  Stated only so that the
dependency ledger can name it; nothing in this project proves it. -/
def TwinPrimes : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-! ## 4. Deterministic implications -/

/-- **Physical 4|5 assembly.**  If the physical quantity splits exactly as
minor spectrum plus major arc, and both are controlled by their interfaces, the
natural physical bound follows with the sum of the two bounds.  Neither premise
is proved here. -/
theorem naturalPhysical45_of_pms45_of_majorArc
    {physical minorSpectrum majorArc b₁ b₂ : ℝ}
    (hsplit : physical = minorSpectrum + majorArc)
    (hpms : PMS45Bound minorSpectrum b₁)
    (hmaj : NaturalMajorArcBound majorArc b₂) :
    NaturalPhysical45Bound physical (b₁ + b₂) := by
  unfold NaturalPhysical45Bound PMS45Bound NaturalMajorArcBound at *
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add hpms hmaj)

/-- **Fixed switched Gate-1B assembly.**  Given the physical bound, the source
expected-term identification and the packet reassembly, the fixed switched
Gate-1B bound follows with the sum of the three tolerances.  This is a pure
triangle-inequality transfer; it proves none of its premises. -/
theorem fixedSwitchedGate1B_of_interfaces
    {total physical sourceExpected centering b tol rem : ℝ}
    (hphys : NaturalPhysical45Bound physical b)
    (hsrc : SourceExpectedTermIdentified sourceExpected centering tol)
    (hpkt : FixedSwitchedPacketReassembled total physical sourceExpected centering rem) :
    FixedSwitchedGate1BBound total (b + tol + rem) := by
  unfold FixedSwitchedGate1BBound NaturalPhysical45Bound
    SourceExpectedTermIdentified FixedSwitchedPacketReassembled at *
  have h1 : |total| ≤ |total - (physical + (sourceExpected - centering))|
      + |physical + (sourceExpected - centering)| := by
    have := abs_add_le (total - (physical + (sourceExpected - centering)))
      (physical + (sourceExpected - centering))
    simpa using this
  have h2 : |physical + (sourceExpected - centering)| ≤ b + tol :=
    le_trans (abs_add_le _ _) (add_le_add hphys hsrc)
  linarith

/-- Variant: the PMS45 minor-spectrum interface may itself be supplied by the
modulus-Fourier uniformity interface applied to the same quantity. -/
theorem pms45_of_modulusFourierUniformity {S bound : ℝ}
    (h : ModulusFourierUniformity S bound) : PMS45Bound S bound := h

/-! ## 5. Guards -/

/-- **Guard.**  The interfaces are not automatically true. -/
theorem pms45_not_automatic : ¬ PMS45Bound 1 0 := by
  unfold PMS45Bound; norm_num

/-- **Guard.**  Nor are they false: they hold for suitable data, so they are
genuine open inputs. -/
theorem pms45_satisfiable : PMS45Bound 1 1 := by
  unfold PMS45Bound; norm_num

/-- **Guard.**  A fixed switched Gate-1B bound alone does not deliver Gate-1B
closure: closure additionally requires the Gate-0 exhaustiveness datum
`uncoveredMass = 0`, which this development does not supply.  Formally, there
are data satisfying `FixedSwitchedGate1BBound` and failing `Gate1BClosed`. -/
theorem gate1BClosed_needs_gate0 :
    FixedSwitchedGate1BBound 0 1 ∧ ¬ Gate1BClosed 0 1 1 := by
  constructor
  · unfold FixedSwitchedGate1BBound; norm_num
  · unfold Gate1BClosed; norm_num

/-- **Guard.**  Gate-1B closure, full Type II and twin primes are *not* proved
here: the present module contains no theorem whose conclusion is one of them
without hypotheses.  This is recorded by the (provable) statement that the
closure predicate is a genuine conjunction, i.e. it is not implied by the bound
component alone. -/
theorem closure_not_implied_by_bound_alone :
    ∃ t b m : ℝ, |t| ≤ b ∧ ¬ Gate1BClosed t b m :=
  ⟨0, 1, 1, by norm_num, by unfold Gate1BClosed; norm_num⟩

end Gate1BDet2
end TwinPrimeProject
