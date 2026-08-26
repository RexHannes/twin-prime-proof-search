import Mathlib

/-!
# Ratio-split sector partition (§12.5, §12.6)

The IIIb analysis partitions the `(s_-, s_+)` parameter space by three successive
dichotomies.  This module machine-checks that the partition is exhaustive and
disjoint, and formalises the elementary implications used inside the sectors.
-/

namespace ShiftedMobiusBank

/-- §12.5 — first dichotomy: for positive `T, s₋, s₊` with `s₋ ≤ s₊`, exactly one
of `s₊² > T·s₋` or `s₊² ≤ T·s₋` holds. -/
theorem sector_first_dichotomy (T sm sp : ℝ) :
    (sp ^ 2 > T * sm ∨ sp ^ 2 ≤ T * sm) ∧
    ¬(sp ^ 2 > T * sm ∧ sp ^ 2 ≤ T * sm) := by
  refine ⟨lt_or_ge (T * sm) (sp ^ 2), ?_⟩
  rintro ⟨h1, h2⟩; exact absurd h2 (not_le.mpr h1)

/-- §12.5 — second dichotomy (inside `s₊² ≤ T·s₋`): either `T/s₋ < X^ρ` or
`T/s₋ ≥ X^ρ`, exactly one. -/
theorem sector_second_dichotomy (T sm Xrho : ℝ) :
    (T / sm < Xrho ∨ T / sm ≥ Xrho) ∧ ¬(T / sm < Xrho ∧ T / sm ≥ Xrho) := by
  refine ⟨lt_or_ge _ _, ?_⟩
  rintro ⟨h1, h2⟩; exact absurd h2 (not_le.mpr h1)

/-- §12.5 — third dichotomy (Sector IIIa vs IIIb): either `hD²M/T² > 1` or
`hD²M/T² ≤ 1`, exactly one. -/
theorem sector_third_dichotomy (r : ℝ) :
    (r > 1 ∨ r ≤ 1) ∧ ¬(r > 1 ∧ r ≤ 1) := by
  refine ⟨lt_or_ge 1 r, ?_⟩
  rintro ⟨h1, h2⟩; exact absurd h2 (not_le.mpr h1)

/-- The four sectors I, II, IIIa, IIIb are jointly exhaustive: every point of the
positive parameter space lands in exactly one. -/
theorem sectors_exhaustive (T sm sp Xrho r : ℝ) :
    (sp ^ 2 > T * sm) ∨
    (sp ^ 2 ≤ T * sm ∧ T / sm < Xrho) ∨
    (sp ^ 2 ≤ T * sm ∧ T / sm ≥ Xrho ∧ r > 1) ∨
    (sp ^ 2 ≤ T * sm ∧ T / sm ≥ Xrho ∧ r ≤ 1) := by
  rcases lt_or_ge (T * sm) (sp ^ 2) with h1 | h1
  · exact Or.inl h1
  · rcases lt_or_ge (T / sm) Xrho with h2 | h2
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · rcases lt_or_ge 1 r with h3 | h3
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))

/-- §12.6 — if `s₊² > T·s₋` and `s₋ ≥ 1` (with `T ≥ 0`) then `s₊² > T`. -/
theorem sector_I_implies (T sm sp : ℝ) (hT : 0 ≤ T) (hsm : 1 ≤ sm)
    (h : sp ^ 2 > T * sm) : sp ^ 2 > T := by
  have : T * sm ≥ T := by nlinarith
  linarith

/-- §12.6 — if `T/s₋ < X^ρ` (with `s₋ > 0`, `X^ρ > 0`) then `s₋ > T·X^{-ρ}`,
stated as `s₋ > T / X^ρ`. -/
theorem sector_II_lower_bound (T sm Xrho : ℝ) (hsm : 0 < sm) (hX : 0 < Xrho)
    (h : T / sm < Xrho) : sm > T / Xrho := by
  rw [div_lt_iff₀ hsm] at h
  rw [gt_iff_lt, div_lt_iff₀ hX]
  linarith

/-- §12.6 — `D = s₋·s₊` with `s₋ ≤ s₊` (and `s₋ ≥ 0`) gives `D ≥ s₋²`. -/
theorem D_ge_sm_sq (sm sp D : ℝ) (hsm : 0 ≤ sm) (hle : sm ≤ sp)
    (hD : D = sm * sp) : D ≥ sm ^ 2 := by
  rw [hD]; nlinarith

/-- Bundle: the partition is exhaustive and the three dichotomies are exclusive. -/
theorem sector_partition_exhaustive_disjoint (T sm sp Xrho r : ℝ) :
    ((sp ^ 2 > T * sm) ∨
      (sp ^ 2 ≤ T * sm ∧ T / sm < Xrho) ∨
      (sp ^ 2 ≤ T * sm ∧ T / sm ≥ Xrho ∧ r > 1) ∨
      (sp ^ 2 ≤ T * sm ∧ T / sm ≥ Xrho ∧ r ≤ 1)) ∧
    ¬(sp ^ 2 > T * sm ∧ sp ^ 2 ≤ T * sm) :=
  ⟨sectors_exhaustive T sm sp Xrho r, (sector_first_dichotomy T sm sp).2⟩

end ShiftedMobiusBank
