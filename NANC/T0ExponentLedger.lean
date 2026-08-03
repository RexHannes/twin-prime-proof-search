import Mathlib

namespace NANC

/-- The normalized secondary phase has exponent `-1`. -/
theorem t0_secondary_phase_unit_size (a b : ℚ) :
    (a + 2 * b - 2 / 3) - (1 / 3 + a + 2 * b) = -1 := by ring

/-- Exact margin identity and its `3/4` lower bound. -/
theorem t0_secondary_phase_margin (a b : ℚ) (hab : a + b ≤ 5 / 8) :
    (2 / 3 + 2 * b) - (2 * a + 4 * b - 4 / 3) = 2 - 2 * a - 2 * b ∧
      3 / 4 ≤ 2 - 2 * a - 2 * b := by
  constructor
  · ring
  · linarith

theorem t0_margin_j0 (a b : ℚ) (hab : a + b ≤ 5 / 8) :
    (2 / 3 + 2 * b) - (2 * a + 4 * b - 2 / 3) = 4 / 3 - 2 * a - 2 * b ∧
      1 / 12 ≤ (2 / 3 + 2 * b) - (2 * a + 4 * b - 2 / 3) := by
  constructor <;> linarith

theorem t0_margin_j1 (a b : ℚ) (hab : a + b ≤ 5 / 8) :
    (2 / 3 + 2 * b) - (2 * a + 4 * b - 13 / 18) = 25 / 18 - 2 * a - 2 * b ∧
      5 / 36 ≤ (2 / 3 + 2 * b) - (2 * a + 4 * b - 13 / 18) := by
  constructor <;> linarith

theorem t0_margin_j2 (a b : ℚ)
    (ha : 5 / 18 ≤ a) (hsum : a + b ≤ 5 / 8) :
    (2 / 3 + 2 * b) - (3 / 2 * a + 4 * b - 5 / 9) =
        11 / 9 - 3 / 2 * a - 2 * b ∧
      1 / 9 ≤ (2 / 3 + 2 * b) - (3 / 2 * a + 4 * b - 5 / 9) := by
  constructor
  · ring
  · linarith

theorem t0_margin_j2_value_at_5_16 :
    (11 / 9 : ℚ) - 3 / 2 * (5 / 16) - 2 * (5 / 16) = 37 / 288 := by
  norm_num

def t0Delta3 (a b : ℚ) : ℚ :=
  if b ≤ 1 / 3 then 5 / 6 - 3 / 2 * a - b else 7 / 6 - 3 / 2 * a - 2 * b

theorem t0_margin_j3_piecewise (a b : ℚ) :
    (b ≤ 1 / 3 → t0Delta3 a b = 5 / 6 - 3 / 2 * a - b) ∧
    (1 / 3 ≤ b → t0Delta3 a b = 7 / 6 - 3 / 2 * a - 2 * b) := by
  constructor
  · intro hb
    unfold t0Delta3
    simp only [if_pos hb]
  · intro hb
    unfold t0Delta3
    split_ifs with h
    · have heq : b = 1 / 3 := le_antisymm h hb
      rw [heq]
      ring
    · rfl

theorem t0_margin_j3_global (a b : ℚ)
    (ha : 5 / 18 ≤ a) (hab : a ≤ b) (hsum : a + b ≤ 5 / 8) :
    5 / 96 ≤ t0Delta3 a b := by
  unfold t0Delta3
  split_ifs with hb
  · linarith
  · have hb' : 1 / 3 ≤ b := le_of_not_ge hb
    linarith

theorem t0_collision_margin (a b : ℚ) (hab : a ≤ b) (hsum : a + b ≤ 5 / 8) :
    (2 / 3 + 2 * b) - (2 * a + 3 * b - 1 / 3) = 1 - 2 * a - b ∧
      1 / 16 ≤ 1 - 2 * a - b := by
  constructor
  · ring
  · linarith

end NANC
