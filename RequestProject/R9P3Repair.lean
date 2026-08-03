import Mathlib
import RequestProject.Status

/-!
# Source-independent r=9 packet arithmetic

Only finite combinatorics and rational exponent arithmetic are banked here.
No prime-distribution estimate is asserted.
-/

namespace HighP3

/-- The nine labelled slots of the clean ordered box. -/
abbrev R9Slot := Fin 9

/-- Membership in a clean ordered box, retaining all nine labels. -/
def InOrderedBox {α : Type*} (box : R9Slot → Finset α) (x : R9Slot → α) : Prop :=
  ∀ i, x i ∈ box i

/-- Projection to the first three labelled slots. -/
def firstThree {α : Type*} (x : R9Slot → α) : Fin 3 → α :=
  fun i => x ⟨i, by omega⟩

/-- Projection to the last six labelled slots. -/
def lastSix {α : Type*} (x : R9Slot → α) : Fin 6 → α :=
  fun i => x ⟨i + 3, by omega⟩

/-- Equality of both labelled blocks implies equality of the original tuple. -/
theorem R9_THREE_PLUS_SIX_BLOCK_IDENTITY {α : Type*} (x y : R9Slot → α)
    (h3 : firstThree x = firstThree y) (h6 : lastSix x = lastSix y) : x = y := by
  funext i
  fin_cases i
  · simpa [firstThree] using congrFun h3 (0 : Fin 3)
  · simpa [firstThree] using congrFun h3 (1 : Fin 3)
  · simpa [firstThree] using congrFun h3 (2 : Fin 3)
  · simpa [lastSix] using congrFun h6 (0 : Fin 6)
  · simpa [lastSix] using congrFun h6 (1 : Fin 6)
  · simpa [lastSix] using congrFun h6 (2 : Fin 6)
  · simpa [lastSix] using congrFun h6 (3 : Fin 6)
  · simpa [lastSix] using congrFun h6 (4 : Fin 6)
  · simpa [lastSix] using congrFun h6 (5 : Fin 6)

/-- The clean ordered-box representation is unique because its slots remain
labelled; this is deliberately not an asymptotic prime-count assertion. -/
theorem R9_ORDERED_BOX_UNIQUE_REPRESENTATION {α : Type*} (x y : R9Slot → α)
    (h : ∀ i, x i = y i) : x = y := by
  funext i
  exact h i

/-- The previously audited hostile equal-factor value for `r=9`. -/
theorem R9_H_VALUE_EQUALS_70 : Nat.choose 8 4 = 70 := by
  decide

section Exponents

variable (eta : ℚ)

/-- Exponent of `q₁=uℓ`. -/
theorem R9_REPAIRED_PACKET_Q1_EXPONENT :
    (1 / 18 - 2 * eta) + (5 / 18 + eta) = 1 / 3 - eta := by ring

/-- Exponent of `q₂=s`. -/
theorem R9_REPAIRED_PACKET_Q2_EXPONENT :
    (1 / 4 - 4 * eta) = 1 / 4 - 4 * eta := rfl

/-- Exponent of `q₃=v`. -/
theorem R9_REPAIRED_PACKET_Q3_EXPONENT :
    (1 / 24 - 4 * eta) = 1 / 24 - 4 * eta := rfl

/-- Total exponent of the proposed modulus grouping. -/
theorem R9_REPAIRED_PACKET_TOTAL_EXPONENT :
    (1 / 3 - eta) + (1 / 4 - 4 * eta) + (1 / 24 - 4 * eta) =
      5 / 8 - 9 * eta := by ring

/-- Exact positivity range for all four proposed factor lengths. -/
theorem R9_REPAIRED_PACKET_NONEMPTY_RELATIONS :
    0 < 5 / 18 + eta ∧ 0 < 1 / 18 - 2 * eta ∧
        0 < 1 / 24 - 4 * eta ∧ 0 < 1 / 4 - 4 * eta ↔
      -(5 / 18) < eta ∧ eta < 1 / 96 := by
  norm_num
  constructor <;> rintro h
  · constructor <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · rcases h with ⟨hl, hu⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end Exponents

/-- Finite enumeration of positive ordered partitions of nine slots. -/
def r9PositiveOrderedPartitions : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 9).product ((Finset.Icc 1 9).product (Finset.Icc 1 9)) |>.filter
    (fun t => t.1 + t.2.1 + t.2.2 = 9)

/-- The reported optimal ordered partition is at least a member of the exact
finite census.  The source-dependent objective function is intentionally not
invented in the absence of the mandatory audit report. -/
theorem R9_PROP_6_3_REPORTED_OPTIMIZER_IN_CENSUS :
    (4, 2, 3) ∈ r9PositiveOrderedPartitions := by
  decide

end HighP3
