import Mathlib

namespace Gate1B.Gold50

/-- Gold 5.0 roughness exponent. -/
def roughnessExponent : ℚ := 21 / 100

/-- Detector polynomial for semiprime parameter `t`. -/
def detector (t : ℝ) : ℝ := (1 - 2 * t) ^ 2

/-- Expanded detector identity used in the signed algebra. -/
theorem detector_expand (t : ℝ) : detector t = 1 - 4 * t * (1 - t) := by
  unfold detector
  ring

/-- The physical source profile ingredients, with the fixed shift `+2` kept explicit in `rhoX`. -/
structure SourceProfile where
  psiX : ℕ → ℝ
  muSq : ℕ → ℝ
  rough : ℕ → ℝ
  lambdaShift : ℕ → ℝ

/-- Gold 5.0 physical source weight at integer `n`. -/
def rhoX (profile : SourceProfile) (n : ℕ) : ℝ :=
  profile.psiX n * profile.muSq n * profile.rough n * profile.lambdaShift (n + 2)

/-- Squarefree-type support assumption for a finite range. -/
def squarefreeSupportOn (s : Finset ℕ) (profile : SourceProfile) : Prop :=
  ∀ n ∈ s, profile.muSq n = 0 ∨ profile.muSq n = 1

/-- Rough-support assumption for a finite range. -/
def roughSupportOn (s : Finset ℕ) (profile : SourceProfile) : Prop :=
  ∀ n ∈ s, profile.rough n = 0 ∨ profile.rough n = 1

end Gate1B.Gold50
