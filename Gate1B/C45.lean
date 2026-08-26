/-
# Gate 1B safe algebra bank — §4–§6: the C45 defect.

Given two physical shell equations

  `q₁ ℓ₁ − u v₁ = 2`,   `q₂ ℓ₂ − u v₂ = 2`,

the **C45 defect** is

  `D := ℓ₁ ℓ₂ (q₁ − q₂) + 2 (ℓ₁ − ℓ₂)`.

This file proves the master integer identity `D = u (v₁ ℓ₂ − v₂ ℓ₁)`, the exact
divisibility equivalence `u ∣ (v₁ ℓ₂ − v₂ ℓ₁) ↔ u² ∣ D` (for `u ≠ 0`), and the
zero-defect diagonal lemma with an **explicit** size hypothesis.  No asymptotics
are hidden anywhere: every inequality used is an assumption of the statement.
-/
import Mathlib

namespace Gate1B

/-- The C45 defect `D = ℓ₁ ℓ₂ (q₁ − q₂) + 2 (ℓ₁ − ℓ₂)`. -/
def C45defect (q1 q2 l1 l2 : ℤ) : ℤ := l1 * l2 * (q1 - q2) + 2 * (l1 - l2)

/-! ## §4 (C45-ID): master integer identity -/

/-- **(C45-ID)** On two shells with the same `u`,
`D = u (v₁ ℓ₂ − v₂ ℓ₁)` exactly. -/
theorem c45_identity {q1 q2 l1 l2 u v1 v2 : ℤ}
    (h1 : q1 * l1 - u * v1 = 2) (h2 : q2 * l2 - u * v2 = 2) :
    C45defect q1 q2 l1 l2 = u * (v1 * l2 - v2 * l1) := by
  unfold C45defect
  linear_combination l2 * h1 - l1 * h2

/-! ## §5 (C45): same fibre ⇔ prime-square collision -/

/-- **(C45), forward direction.**  If `u ∣ v₁ ℓ₂ − v₂ ℓ₁` then `u² ∣ D`. -/
theorem c45_sq_dvd_of_dvd {q1 q2 l1 l2 u v1 v2 : ℤ}
    (h1 : q1 * l1 - u * v1 = 2) (h2 : q2 * l2 - u * v2 = 2)
    (hdvd : u ∣ (v1 * l2 - v2 * l1)) :
    u ^ 2 ∣ C45defect q1 q2 l1 l2 := by
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  rw [c45_identity h1 h2, hk]
  ring

/-- **(C45), converse direction.**  If `u ≠ 0` and `u² ∣ D` then
`u ∣ v₁ ℓ₂ − v₂ ℓ₁`. -/
theorem dvd_of_c45_sq_dvd {q1 q2 l1 l2 u v1 v2 : ℤ} (hu : u ≠ 0)
    (h1 : q1 * l1 - u * v1 = 2) (h2 : q2 * l2 - u * v2 = 2)
    (hsq : u ^ 2 ∣ C45defect q1 q2 l1 l2) :
    u ∣ (v1 * l2 - v2 * l1) := by
  obtain ⟨k, hk⟩ := hsq
  refine ⟨k, ?_⟩
  have h : u * (v1 * l2 - v2 * l1) = u * (u * k) := by
    rw [← c45_identity h1 h2, hk]; ring
  exact mul_left_cancel₀ hu h

/-- **(C45) as an exact equivalence** (for `u ≠ 0`). -/
theorem c45_dvd_iff {q1 q2 l1 l2 u v1 v2 : ℤ} (hu : u ≠ 0)
    (h1 : q1 * l1 - u * v1 = 2) (h2 : q2 * l2 - u * v2 = 2) :
    u ∣ (v1 * l2 - v2 * l1) ↔ u ^ 2 ∣ C45defect q1 q2 l1 l2 :=
  ⟨c45_sq_dvd_of_dvd h1 h2, dvd_of_c45_sq_dvd hu h1 h2⟩

/-- Guard: the hypothesis `u ≠ 0` in the converse is load-bearing.  With
`u = 0` the shells still hold, `u² ∣ D` holds, but `u ∤ v₁ ℓ₂ − v₂ ℓ₁`. -/
theorem c45_converse_needs_u_ne_zero :
    ∃ q1 q2 l1 l2 u v1 v2 : ℤ,
      q1 * l1 - u * v1 = 2 ∧ q2 * l2 - u * v2 = 2 ∧
      u ^ 2 ∣ C45defect q1 q2 l1 l2 ∧ ¬ (u ∣ (v1 * l2 - v2 * l1)) := by
  refine ⟨1, 2, 2, 1, 0, 1, 0, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [C45defect]
  · norm_num

/-! ## §6 Zero-defect / diagonal lemma -/

/-- Zero defect with equal `ℓ`'s forces equal `q`'s (no size hypothesis is
needed in this branch). -/
theorem q_eq_of_defect_zero_of_l_eq {q1 q2 l1 l2 : ℤ} (hl1 : 0 < l1) (hl2 : 0 < l2)
    (hl : l1 = l2) (hD : C45defect q1 q2 l1 l2 = 0) : q1 = q2 := by
  subst hl
  unfold C45defect at hD
  have hpos : 0 < l1 * l1 := mul_pos hl1 hl1
  have h : l1 * l1 * (q1 - q2) = 0 := by linarith
  have := mul_eq_zero.mp h
  rcases this with h' | h'
  · exact absurd h' (by positivity)
  · linarith

/-- **(ZD)** Zero-defect diagonal lemma.  Under positivity and the *explicit*
size hypothesis `2 |ℓ₁ − ℓ₂| < ℓ₁ ℓ₂`, a vanishing C45 defect forces the pairs
to coincide: `(q₁, ℓ₁) = (q₂, ℓ₂)`. -/
theorem zero_defect_diagonal {q1 q2 l1 l2 : ℤ} (hl1 : 0 < l1) (hl2 : 0 < l2)
    (hzd : 2 * |l1 - l2| < l1 * l2) (hD : C45defect q1 q2 l1 l2 = 0) :
    q1 = q2 ∧ l1 = l2 := by
  unfold C45defect at hD
  have hpos : 0 < l1 * l2 := mul_pos hl1 hl2
  have hq : q1 = q2 := by
    by_contra hne
    have h1' : 1 ≤ |q1 - q2| := Int.one_le_abs (sub_ne_zero.mpr hne)
    have habs : l1 * l2 * |q1 - q2| = 2 * |l1 - l2| := by
      have he : l1 * l2 * (q1 - q2) = -(2 * (l1 - l2)) := by linarith
      calc l1 * l2 * |q1 - q2| = |l1 * l2 * (q1 - q2)| := by
            rw [abs_mul, abs_of_pos hpos]
        _ = |2 * (l1 - l2)| := by rw [he, abs_neg]
        _ = 2 * |l1 - l2| := by rw [abs_mul]; norm_num
    nlinarith [habs, h1', hpos]
  subst hq
  exact ⟨rfl, by linarith⟩

/-- Guard: the size hypothesis `(ZD-HYP)` is load-bearing.  Without it there are
positive integer data with `D = 0` and `(q₁, ℓ₁) ≠ (q₂, ℓ₂)`. -/
theorem zero_defect_needs_size_hypothesis :
    ∃ q1 q2 l1 l2 : ℤ, 0 < l1 ∧ 0 < l2 ∧ C45defect q1 q2 l1 l2 = 0 ∧
      ¬ (2 * |l1 - l2| < l1 * l2) ∧ (q1, l1) ≠ (q2, l2) := by
  refine ⟨1, 0, 1, 2, by norm_num, by norm_num, by norm_num [C45defect], by norm_num, ?_⟩
  simp

end Gate1B
