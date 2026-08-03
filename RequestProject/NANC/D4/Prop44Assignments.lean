import Mathlib

namespace NANC.D4

inductive Prop44Slot | one | two | three
  deriving DecidableEq, Fintype, Repr

@[simp] theorem Prop44Slot.one_ne_two : Prop44Slot.one ≠ Prop44Slot.two := by decide
@[simp] theorem Prop44Slot.one_ne_three : Prop44Slot.one ≠ Prop44Slot.three := by decide
@[simp] theorem Prop44Slot.two_ne_one : Prop44Slot.two ≠ Prop44Slot.one := by decide
@[simp] theorem Prop44Slot.two_ne_three : Prop44Slot.two ≠ Prop44Slot.three := by decide
@[simp] theorem Prop44Slot.three_ne_one : Prop44Slot.three ≠ Prop44Slot.one := by decide
@[simp] theorem Prop44Slot.three_ne_two : Prop44Slot.three ≠ Prop44Slot.two := by decide

structure AtomicAssignment where
  uSlot : Prop44Slot
  vSlot : Prop44Slot
  lSlot : Prop44Slot
  deriving DecidableEq, Fintype, Repr

def slotExponent (A : AtomicAssignment) (slot : Prop44Slot)
    (u v l : ℚ) : ℚ :=
  (if A.uSlot = slot then u else 0) +
  (if A.vSlot = slot then v else 0) +
  (if A.lSlot = slot then l else 0)

def massExponent (j : Fin 8) : ℚ := (j.val + 1 : ℕ) / 9

def AssignmentPasses (ε : ℚ) (j : Fin 8) (A : AtomicAssignment)
    (u v l : ℚ) : Prop :=
  let τ := massExponent j
  let a₁ := slotExponent A .one u v l
  let a₂ := slotExponent A .two u v l
  let a₃ := slotExponent A .three u v l
  a₁ ≤ τ - ε ∧
  2 * τ + a₂ + 2 * a₃ ≤ 1 - 15 * ε ∧
  2 * τ + 5 * a₂ + 2 * a₃ ≤ 2 - 40 * ε

def HighP3Atomic (η u v l : ℚ) : Prop :=
  0 ≤ u ∧ 0 ≤ v ∧ (5/18 : ℚ) - η/2 ≤ u+v ∧
  (5/18 : ℚ) - η/2 ≤ l ∧ u+v+l ≤ 1

end NANC.D4
