import Gate1B.Gold50.PhysicalSource

namespace Gate1B.Gold50

open scoped BigOperators

/-- Explicit finite signed sector total. -/
noncomputable def Jsigned (P1 P2 P3 P4 : Finset ℕ) (ρ : ℕ → ℝ) : ℝ :=
  (∑ n ∈ P1, ρ n) - (∑ n ∈ P2, ρ n) - (∑ n ∈ P3, ρ n) - (∑ n ∈ P4, ρ n)

/-- Sector mass. -/
noncomputable def Qsector (P : Finset ℕ) (ρ : ℕ → ℝ) : ℝ :=
  ∑ n ∈ P, ρ n

/-- Four-sector Möbius sum, written with each sector explicit. -/
noncomputable def M0split (P1 P2 P3 P4 : Finset ℕ) (ρ μ : ℕ → ℝ) : ℝ :=
  (∑ n ∈ P1, ρ n * μ n) + (∑ n ∈ P2, ρ n * μ n) +
    (∑ n ∈ P3, ρ n * μ n) + (∑ n ∈ P4, ρ n * μ n)

/-- Weighted detector sum on sector `P2`. -/
noncomputable def detectorMass (P2 : Finset ℕ) (ρ : ℕ → ℝ) (t : ℕ → ℝ) : ℝ :=
  ∑ n ∈ P2, ρ n * (4 * t n * (1 - t n))

/-- Literal sign decomposition `J = Q₁ - Q₂ - Q₃ - Q₄`. -/
theorem jsigned_eq_sector_masses
    (P1 P2 P3 P4 : Finset ℕ) (ρ : ℕ → ℝ) :
    Jsigned P1 P2 P3 P4 ρ
      = Qsector P1 ρ - Qsector P2 ρ - Qsector P3 ρ - Qsector P4 ρ := by
  simp [Jsigned, Qsector]

/-- Source-exact finite signed identity with explicit sector hypotheses. -/
theorem jsigned_eq_m0_detector_sub_2q3
    (P1 P2 P3 P4 : Finset ℕ)
    (ρ μ : ℕ → ℝ) (t : ℕ → ℝ)
    (hμ1 : ∀ n ∈ P1, μ n = -1)
    (hμ2 : ∀ n ∈ P2, μ n = 1 + 4 * t n * (1 - t n))
    (hμ3 : ∀ n ∈ P3, μ n = -1)
    (hμ4 : ∀ n ∈ P4, μ n = 1) :
    Jsigned P1 P2 P3 P4 ρ
      = -M0split P1 P2 P3 P4 ρ μ + detectorMass P2 ρ t - 2 * Qsector P3 ρ := by
  have hP1 : (∑ n ∈ P1, ρ n * μ n) = -(∑ n ∈ P1, ρ n) := by
    simp [hμ1]
  have hP2 : (∑ n ∈ P2, ρ n * μ n) = (∑ n ∈ P2, ρ n) + detectorMass P2 ρ t := by
    unfold detectorMass
    calc
      (∑ n ∈ P2, ρ n * μ n) = ∑ n ∈ P2, (ρ n + ρ n * (4 * t n * (1 - t n))) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [hμ2 n hn]
        ring
      _ = (∑ n ∈ P2, ρ n) + ∑ n ∈ P2, ρ n * (4 * t n * (1 - t n)) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ n ∈ P2, ρ n) + detectorMass P2 ρ t := by rfl
  have hP3 : (∑ n ∈ P3, ρ n * μ n) = -(∑ n ∈ P3, ρ n) := by
    simp [hμ3]
  have hP4 : (∑ n ∈ P4, ρ n * μ n) = ∑ n ∈ P4, ρ n := by
    simp [hμ4]
  unfold Jsigned M0split Qsector
  rw [hP1, hP2, hP3, hP4]
  ring

end Gate1B.Gold50
