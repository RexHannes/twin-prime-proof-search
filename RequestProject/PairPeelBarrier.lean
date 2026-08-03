import Mathlib
import RequestProject.AbstractPeelSemantics
import RequestProject.Elementary

/-!
# Reciprocal-pair peel barrier

This file is deliberately separate from `AbstractPeelSemantics`.  The latter
acts on signed integer-weight lists.  Here the objects are *sets of distinct
positive integer denominators*.  No definitional identification is made.

An abstract equation can have repeated or zero weights, while a reciprocal
pair consists of finsets of positive denominators.  Consequently validity of
an abstract equation alone does not imply set-level realizability.
-/

open scoped BigOperators
open Finset

noncomputable section

/-- An integer-weight equation.  Lists are used because an abstract peel can
retain multiplicity; positivity and absence of duplicates are not built in. -/
structure SignedWeightEquation where
  positive : List ℕ
  negative : List ℕ

/-- Validity in the abstract integer-weight domain. -/
def SignedWeightEquation.Valid (E : SignedWeightEquation) : Prop :=
  E.positive.sum = E.negative.sum

/-- Convert a `PeelState` to the corresponding two signed weight lists. -/
def PeelState.weightEquation (s : PeelState) : SignedWeightEquation where
  positive := (s.weights.zip s.signs).filterMap fun (w, sign) =>
    if sign then some w else none
  negative := (s.weights.zip s.signs).filterMap fun (w, sign) =>
    if sign then none else some w

/-- The pair-level domain: two disjoint finite sets of positive denominators
with equal reciprocal sum. -/
structure ReciprocalPair where
  P : Finset ℕ+
  Q : Finset ℕ+
  disjoint : Disjoint P Q
  equal_sum : recipSum P = recipSum Q

/-- The sum of the (ordinary integer) denominators on both sides. -/
def ReciprocalPair.denominatorMass (X : ReciprocalPair) : ℕ :=
  ∑ q ∈ X.P, (q : ℕ) + ∑ q ∈ X.Q, (q : ℕ)

/-- Honest realization relation.  `L` is a positive common denominator;
the two abstract weight lists are, up to permutation, exactly `L/q` on the
corresponding denominator sets.  Thus multiplicities are retained and cannot
silently be converted to sethood. -/
def ReciprocalPairRealizesEquation
    (P Q : Finset ℕ+) (E : SignedWeightEquation) : Prop :=
  Disjoint P Q ∧ recipSum P = recipSum Q ∧
  ∃ L : ℕ+,
    (∀ q ∈ P, (q : ℕ) ∣ (L : ℕ)) ∧
    (∀ q ∈ Q, (q : ℕ) ∣ (L : ℕ)) ∧
    E.positive.Perm (P.toList.map fun q => intWeight L q) ∧
    E.negative.Perm (Q.toList.map fun q => intWeight L q)

/-
Clearing denominators makes every honestly realized equation valid.
-/
theorem realizesEquation_implies_weightEquationValid
    {P Q : Finset ℕ+} {E : SignedWeightEquation}
    (h : ReciprocalPairRealizesEquation P Q E) : E.Valid := by
  obtain ⟨h_disjoint, h_recip, L, hL⟩ := h;
  convert clearing_denominators ( P ∪ Q ) L _ P Q _ _;
  · grind +locals;
  · grind;
  · exact Finset.subset_union_left;
  · exact Finset.subset_union_right

/-- A reciprocal pair is primitive when its only equal-sum subpairs are the
empty subpair and the entire pair. -/
def ReciprocalPair.IsPrimitive (X : ReciprocalPair) : Prop :=
  ∀ A B, A ⊆ X.P → B ⊆ X.Q → recipSum A = recipSum B →
    (A = ∅ ∧ B = ∅) ∨ (A = X.P ∧ B = X.Q)

/-- Pair-level subset removal.  It is defined only from an actual matching
subpair; it is not an abstract weight merge. -/
def ReciprocalPair.removeMatching (X : ReciprocalPair)
    (A B : Finset ℕ+) (hA : A ⊆ X.P) (hB : B ⊆ X.Q)
    (hAB : recipSum A = recipSum B) : ReciprocalPair where
  P := X.P \ A
  Q := X.Q \ B
  disjoint := X.disjoint.mono sdiff_subset sdiff_subset
  equal_sum := by
    simp only [recipSum]
    rw [sum_sdiff_eq_sub hA, sum_sdiff_eq_sub hB]
    change recipSum X.P - recipSum A = recipSum X.Q - recipSum B
    rw [X.equal_sum, hAB]

/-- Identity-or-total-collapse barrier: on a primitive pair, a matching
subpair is either empty or the whole pair. -/
theorem primitive_matching_subpair_empty_or_total
    (X : ReciprocalPair) (hprim : X.IsPrimitive)
    (A B : Finset ℕ+) (hA : A ⊆ X.P) (hB : B ⊆ X.Q)
    (hAB : recipSum A = recipSum B) :
    (A = ∅ ∧ B = ∅) ∨ (A = X.P ∧ B = X.Q) := by
  exact hprim A B hA hB hAB

/-- In the total branch, pair-level removal collapses both sides. -/
theorem removeMatching_total_collapse
    (X : ReciprocalPair) (A B : Finset ℕ+)
    (hA : A ⊆ X.P) (hB : B ⊆ X.Q) (hAB : recipSum A = recipSum B)
    (hAt : A = X.P) (hBt : B = X.Q) :
    (X.removeMatching A B hA hB hAB).P = ∅ ∧
    (X.removeMatching A B hA hB hAB).Q = ∅ := by
  subst A; subst B; simp [ReciprocalPair.removeMatching]

/-
Exact mass identity for pair-level removal.
-/
theorem denominatorMass_removeMatching
    (X : ReciprocalPair) (A B : Finset ℕ+)
    (hA : A ⊆ X.P) (hB : B ⊆ X.Q) (hAB : recipSum A = recipSum B) :
    X.denominatorMass =
      (X.removeMatching A B hA hB hAB).denominatorMass +
      (∑ q ∈ A, (q : ℕ) + ∑ q ∈ B, (q : ℕ)) := by
  unfold ReciprocalPair.denominatorMass ReciprocalPair.removeMatching;
  rw [ ← Finset.sum_sdiff hA, ← Finset.sum_sdiff hB ] ; ring;

/-- Realizability of a canonical step from a specified reciprocal pair.  This
is intentionally an existential set-level condition, not a consequence of
abstract validity. -/
def CanonicalStepRealizableFrom (P Q : Finset ℕ+) (s s' : PeelState) : Prop :=
  ReciprocalPairRealizesEquation P Q s.weightEquation ∧
  ∃ P' Q' : Finset ℕ+,
    ReciprocalPairRealizesEquation P' Q' s'.weightEquation

/-- Repeated weights are a genuine sethood warning: list multiplicity cannot
be forgotten when passing to finite sets. -/
def DuplicateWeightObstruction (s : PeelState) : Prop := ¬s.weights.Nodup

/-- Zero weights cannot be represented as `L/q` for positive `L,q`. -/
def NonPositiveWeightObstruction (s : PeelState) : Prop := 0 ∈ s.weights

/-- The residual obstruction after the two directly checkable failures.  This
name is intentionally neutral: proving it is a controlled component split
requires additional arithmetic and SCC structure absent from abstract peel
validity. -/
def ResidualRealizationObstruction
    (P Q : Finset ℕ+) (s s' : PeelState) : Prop :=
  ReciprocalPairRealizesEquation P Q s.weightEquation ∧
  ¬ CanonicalStepRealizableFrom P Q s s' ∧
  ¬ DuplicateWeightObstruction s' ∧
  ¬ NonPositiveWeightObstruction s'

/-
Strongest unconditional audit theorem currently justified: a canonical
abstract step is realizable, or it has a duplicate/zero obstruction, or the
remaining realizability problem is explicitly isolated.  It does *not* label
the residual case as loss of primitivity, SCC compression, or component split
without a proof of one of those stronger facts.
-/
theorem canonicalPeel_realization_or_obstruction
    (P Q : Finset ℕ+) (s : PeelState) (p : PeelPrime)
    (hreal : ReciprocalPairRealizesEquation P Q s.weightEquation) :
    CanonicalStepRealizableFrom P Q s (peelOnceCanonical s p) ∨
    DuplicateWeightObstruction (peelOnceCanonical s p) ∨
    NonPositiveWeightObstruction (peelOnceCanonical s p) ∨
    ResidualRealizationObstruction P Q s (peelOnceCanonical s p) := by
  grind +locals

/-- The exact (signed) mass comparison available for any two realized
pairs.  It contains no contraction until arithmetic data relates the scales. -/
def pairMassChange (X X' : ReciprocalPair) : ℤ :=
  (X.denominatorMass : ℤ) - X'.denominatorMass

/-- Exact affine identity for every pair-level transformation. -/
theorem denominatorMass_exact_comparison (X X' : ReciprocalPair) :
    (X.denominatorMass : ℤ) = X'.denominatorMass + pairMassChange X X' := by
  simp [pairMassChange]

/-- Candidate recurrence interface.  It quantifies over a specified relation
between input and output pairs; unlike equation validity alone, that relation
must carry the local scale and branching data. -/
def PairDenominatorPeelRecurrence
    (Step : ReciprocalPair → ReciprocalPair → Prop) (A : ℕ) (rho : ℚ) : Prop :=
  0 ≤ rho ∧ rho < 1 ∧
  ∀ X X' : ReciprocalPair, Step X X' →
    (X.denominatorMass : ℚ) ≤ A + rho * X'.denominatorMass

/-
The classical identity `1/2 = 1/3 + 1/6`, dilated by any positive `k`.
It witnesses the scale freedom that an abstract weight equation forgets.
-/
def dilationPair (k : ℕ+) : ReciprocalPair where
  P := {2 * k}
  Q := {3 * k, 6 * k}
  disjoint := by
    simp only [Finset.disjoint_singleton_left, Finset.mem_insert,
      Finset.mem_singleton]
    intro h
    rcases h with h | h
    · exact absurd (congrArg (fun x : ℕ+ => (x : ℕ)) h) (by simp)
    · exact absurd (congrArg (fun x : ℕ+ => (x : ℕ)) h) (by simp)
  equal_sum := by
    unfold recipSum; simp +decide; ring;

/-- The fixed abstract equation realized by every member of `dilationPair`. -/
def dilationEquation : SignedWeightEquation where
  positive := [3]
  negative := [2, 1]

/-
Every dilation realizes exactly the same abstract cleared equation (take
common denominator `6k`).
-/
theorem dilationPair_realizes (k : ℕ+) :
    ReciprocalPairRealizesEquation (dilationPair k).P (dilationPair k).Q
      dilationEquation := by
  refine' ⟨ _, _, _ ⟩;
  · exact dilationPair k |>.disjoint;
  · unfold dilationPair; simp +decide [ recipSum ] ; ring;
  · refine' ⟨ 6 * k, _, _, _, _ ⟩ <;> simp +decide [ dilationPair ];
    · exact ⟨ 3, by ring ⟩;
    · exact ⟨ 2, by ring ⟩;
    · unfold intWeight; simp +decide [ show ( 6 * k : ℕ ) = 2 * k * 3 by ring ] ;
    · rcases h : ( { 3 * k, 6 * k } : Finset ℕ+ ).toList with _ | ⟨ a, _ | ⟨ b, _ | h ⟩ ⟩ ; simp_all +decide;
      · replace h := congr_arg List.length h ; simp_all +decide;
      · replace h := congr_arg List.toFinset h; rw [ Finset.ext_iff ] at h; have := h ( 3 * k ) ; have := h ( 6 * k ) ; simp_all +decide ;
        cases this <;> cases ‹3 * k = a ∨ 3 * k = b› <;> subst_vars <;> simp_all +decide [intWeight];
        · norm_num [ show ( 6 * k : ℕ ) = 3 * k * 2 by ring, Nat.mul_div_mul_left ];
          exact List.Perm.swap ..;
        · rw [ show ( 6 * k : ℕ ) = 3 * k * 2 by ring, Nat.mul_div_cancel_left _ ( by positivity ) ] ; simp +decide;
      · replace h := congr_arg List.length h ; simp_all +decide

/-- Dilation makes denominator mass grow linearly while preserving the same
cleared weights `[3] = [2,1]`. -/
theorem dilationPair_mass (k : ℕ+) :
    (dilationPair k).denominatorMass = 11 * (k : ℕ) := by
  unfold dilationPair
  simp +decide [ReciprocalPair.denominatorMass]
  ring

/-- With the abstract equation held fixed, the ratio of pair masses can be
arbitrarily large. -/
theorem dilationPair_mass_unbounded (n : ℕ) :
    (dilationPair ⟨n + 1, Nat.succ_pos n⟩).denominatorMass >
      n * (dilationPair 1).denominatorMass := by
  rw [dilationPair_mass, dilationPair_mass]
  simp
  omega

/-!
There is therefore no recurrence theorem from equation validity alone.
Replacing every denominator `q` and clearing denominator `L` by `kq` and `kL`
leaves every weight `L/q` unchanged, whereas `dilationPair_mass` shows linear
mass growth.  A contraction theorem must normalize scale or relate the input
and output clearing denominators.  Accordingly, this file does not assert a
`PairDenominatorPeelRecurrence` instance.
-/

end