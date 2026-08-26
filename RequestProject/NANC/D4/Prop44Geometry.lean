import Mathlib

namespace TwinPrimeProject.NANC.D4

/-- Only the three rational exponent inequalities from Proposition 4.4.
This does not encode roughness, Siegel--Walfisz, support, coefficient bounds,
or applicability of the source theorem. -/
def Prop44ExponentConditions (ε n s₁ s₂ s₃ : ℚ) : Prop :=
  s₁ ≤ n - ε ∧
  2 * n + s₂ + 2 * s₃ ≤ 1 - 15 * ε ∧
  2 * n + 5 * s₂ + 2 * s₃ ≤ 2 - 40 * ε

/-- Ordered exponent triples of total mass `1/3`. -/
def OrderedP3Exponents (s₁ s₂ s₃ : ℚ) : Prop :=
  0 ≤ s₃ ∧ s₃ ≤ s₂ ∧ s₂ ≤ s₁ ∧ s₁ + s₂ + s₃ = (1 : ℚ) / 3

theorem prop44_endpoint_middle_identity {s₁ s₂ s₃ : ℚ}
    (hsum : s₁ + s₂ + s₃ = (1 : ℚ) / 3) :
    2 * ((1 : ℚ) / 3) + s₂ + 2 * s₃ = 1 - (s₁ - s₃) := by
  linarith

theorem prop44_endpoint_middle_iff_gap {ε s₁ s₂ s₃ : ℚ}
    (hsum : s₁ + s₂ + s₃ = (1 : ℚ) / 3) :
    2 * ((1 : ℚ) / 3) + s₂ + 2 * s₃ ≤ 1 - 15 * ε ↔
      15 * ε ≤ s₁ - s₃ := by
  rw [prop44_endpoint_middle_identity hsum]
  constructor <;> intro h <;> linarith

theorem ordered_p3_s₂_le_one_sixth {s₁ s₂ s₃ : ℚ}
    (hord : OrderedP3Exponents s₁ s₂ s₃) : s₂ ≤ (1 : ℚ) / 6 := by
  rcases hord with ⟨hs3, hs32, hs21, hsum⟩
  linarith

theorem ordered_p3_five_s₂_add_two_s₃_le_five_sixths {s₁ s₂ s₃ : ℚ}
    (hord : OrderedP3Exponents s₁ s₂ s₃) :
    5 * s₂ + 2 * s₃ ≤ (5 : ℚ) / 6 := by
  have hm := ordered_p3_s₂_le_one_sixth hord
  rcases hord with ⟨_, hs32, hs21, hsum⟩
  linarith

theorem ordered_p3_endpoint_third_condition {ε s₁ s₂ s₃ : ℚ}
    (hord : OrderedP3Exponents s₁ s₂ s₃)
    (hε : ε ≤ (1 : ℚ) / 80) :
    2 * ((1 : ℚ) / 3) + 5 * s₂ + 2 * s₃ ≤ 2 - 40 * ε := by
  have h := ordered_p3_five_s₂_add_two_s₃_le_five_sixths hord
  linarith

theorem p3_endpoint_first_condition_iff {ε s₁ s₂ s₃ : ℚ}
    (hsum : s₁ + s₂ + s₃ = (1 : ℚ) / 3) :
    s₁ ≤ (1 : ℚ) / 3 - ε ↔ ε ≤ s₂ + s₃ := by
  constructor <;> intro h <;> linarith

/-- Ordered endpoint sufficiency: the gap gives the middle inequality, the
first budget is separate, and ordering plus `ε ≤ 1/80` gives the third. -/
theorem ordered_p3_endpoint_prop44_of_gap {ε s₁ s₂ s₃ : ℚ}
    (hord : OrderedP3Exponents s₁ s₂ s₃)
    (hεnonneg : 0 ≤ ε) (hεsmall : ε ≤ (1 : ℚ) / 80)
    (hfirst : ε ≤ s₂ + s₃) (hgap : 15 * ε ≤ s₁ - s₃) :
    Prop44ExponentConditions ε ((1 : ℚ) / 3) s₁ s₂ s₃ := by
  rcases hord with ⟨hs3, hs32, hs21, hsum⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (p3_endpoint_first_condition_iff hsum).2 hfirst
  · exact (prop44_endpoint_middle_iff_gap hsum).2 hgap
  · exact ordered_p3_endpoint_third_condition ⟨hs3, hs32, hs21, hsum⟩ hεsmall

theorem balanced_p3_endpoint_fails {ε : ℚ} (hε : 0 < ε) :
    ¬ Prop44ExponentConditions ε ((1 : ℚ) / 3)
      ((1 : ℚ) / 9) ((1 : ℚ) / 9) ((1 : ℚ) / 9) := by
  intro h
  rcases h with ⟨_, hm, _⟩
  norm_num at hm
  linarith

theorem balanced_p3_interior_prop44_iff {ε δ : ℚ} :
    Prop44ExponentConditions ε ((1 : ℚ) / 3 - δ)
      ((1 : ℚ) / 9) ((1 : ℚ) / 9) ((1 : ℚ) / 9) ↔
    δ + ε ≤ (2 : ℚ) / 9 ∧ 15 * ε ≤ 2 * δ ∧
      40 * ε ≤ (5 : ℚ) / 9 + 2 * δ := by
  unfold Prop44ExponentConditions
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩

theorem balanced_p3_interior_prop44_of_shortening {ε δ : ℚ}
    (hεnonneg : 0 ≤ ε) (hδnonneg : 0 ≤ δ)
    (hshort : 15 * ε ≤ 2 * δ)
    (hfirst : δ + ε ≤ (2 : ℚ) / 9)
    (hεsmall : ε ≤ (1 : ℚ) / 72) :
    Prop44ExponentConditions ε ((1 : ℚ) / 3 - δ)
      ((1 : ℚ) / 9) ((1 : ℚ) / 9) ((1 : ℚ) / 9) := by
  apply balanced_p3_interior_prop44_iff.mpr
  refine ⟨hfirst, hshort, ?_⟩
  linarith

end TwinPrimeProject.NANC.D4
