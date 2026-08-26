import RequestProject.NANC.HFMVGate1B.HFMVComplementaryDivisor

/-!
# HFMV Gate 1B, Module 2: the determinant identity and its converse

Two incidences sharing the same `u`,

  `u v₁ + 2 = d₁ p₁ l₁`,   `u v₂ + 2 = d₂ p₂ l₂`,

satisfy the exact determinant identity

  `v₂ (d₁ p₁ l₁) - v₁ (d₂ p₂ l₂) = 2 (v₂ - v₁)`.

Everything is over `ℤ` (no `Nat` subtraction).  The converse is proved with the
explicit reconstruction `u = (d₁ p₁ l₁ - 2)/v₁ = (d₂ p₂ l₂ - 2)/v₂` and the
divisibility hypothesis that makes those quotients exact.
-/

namespace TwinPrimeProject
namespace HFMVGate1B

/-! ## 1. The determinant identity -/

/-- **HFMV determinant identity.**  Exact, no error term, fixed shift `2`. -/
theorem det_identity {u v₁ v₂ d₁ p₁ l₁ d₂ p₂ l₂ : ℤ}
    (h₁ : Incidence u v₁ d₁ p₁ l₁) (h₂ : Incidence u v₂ d₂ p₂ l₂) :
    v₂ * (d₁ * p₁ * l₁) - v₁ * (d₂ * p₂ * l₂) = 2 * (v₂ - v₁) := by
  unfold Incidence at h₁ h₂
  rw [← h₁, ← h₂]; ring

/-- Equivalent centred form of the determinant identity:
`v₂ (d₁ p₁ l₁ - 2) = v₁ (d₂ p₂ l₂ - 2)`. -/
theorem det_identity_centered {u v₁ v₂ d₁ p₁ l₁ d₂ p₂ l₂ : ℤ}
    (h₁ : Incidence u v₁ d₁ p₁ l₁) (h₂ : Incidence u v₂ d₂ p₂ l₂) :
    v₂ * (d₁ * p₁ * l₁ - 2) = v₁ * (d₂ * p₂ * l₂ - 2) := by
  have := det_identity h₁ h₂
  linarith

/-! ## 2. The converse -/

/-- **Converse of the determinant identity (abstract form).**  Write
`K₁ = d₁ p₁ l₁`, `K₂ = d₂ p₂ l₂`.  If the determinant relation holds, `v₁ ≠ 0`
and `v₁ ∣ K₁ - 2`, then the common `u` exists and equals `(K₁ - 2)/v₁`. -/
theorem det_converse_abstract {v₁ v₂ K₁ K₂ : ℤ} (hv₁ : v₁ ≠ 0)
    (hdvd : v₁ ∣ K₁ - 2) (hdet : v₂ * K₁ - v₁ * K₂ = 2 * (v₂ - v₁)) :
    ∃ u : ℤ, u * v₁ + 2 = K₁ ∧ u * v₂ + 2 = K₂ ∧ u = (K₁ - 2) / v₁ := by
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, by linarith [hu], ?_, ?_⟩
  · -- from `v₂ (K₁ - 2) = v₁ (K₂ - 2)` and `K₁ - 2 = v₁ u`
    have hcent : v₂ * (K₁ - 2) = v₁ * (K₂ - 2) := by linarith
    have : v₁ * (u * v₂) = v₁ * (K₂ - 2) := by
      rw [← hcent, hu]; ring
    have := mul_left_cancel₀ hv₁ this
    linarith
  · have : K₁ - 2 = v₁ * u := hu
    rw [this, Int.mul_ediv_cancel_left _ hv₁]

/-- **Converse of the determinant identity, source-native form.**  Under the
determinant relation, `v₁ ≠ 0`, `v₂ ≠ 0` and the exactness hypothesis
`v₁ ∣ d₁ p₁ l₁ - 2`, there is a common `u` producing both incidences, and it is
given by both quotients

  `u = (d₁ p₁ l₁ - 2)/v₁ = (d₂ p₂ l₂ - 2)/v₂`. -/
theorem det_converse {v₁ v₂ d₁ p₁ l₁ d₂ p₂ l₂ : ℤ} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hdvd : v₁ ∣ d₁ * p₁ * l₁ - 2)
    (hdet : v₂ * (d₁ * p₁ * l₁) - v₁ * (d₂ * p₂ * l₂) = 2 * (v₂ - v₁)) :
    ∃ u : ℤ, Incidence u v₁ d₁ p₁ l₁ ∧ Incidence u v₂ d₂ p₂ l₂ ∧
      u = (d₁ * p₁ * l₁ - 2) / v₁ ∧ u = (d₂ * p₂ * l₂ - 2) / v₂ := by
  obtain ⟨u, h1, h2, h3⟩ := det_converse_abstract hv₁ hdvd hdet
  refine ⟨u, by unfold Incidence; linarith, by unfold Incidence; linarith, h3, ?_⟩
  have : d₂ * p₂ * l₂ - 2 = v₂ * u := by linarith
  rw [this, Int.mul_ediv_cancel_left _ hv₂]

/-- Positivity variant: with positive data the reconstructed `u` is positive. -/
theorem det_converse_pos {v₁ d₁ p₁ l₁ u : ℤ} (hv₁ : 0 < v₁)
    (hK : 2 < d₁ * p₁ * l₁) (h : Incidence u v₁ d₁ p₁ l₁) : 0 < u := by
  unfold Incidence at h
  nlinarith

end HFMVGate1B
end TwinPrimeProject
