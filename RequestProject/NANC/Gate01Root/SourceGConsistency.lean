import RequestProject.NANC.Gate01Root.PPDInterfaces

/-!
# Gate01Root: SOURCE-G consistency (quarantine module)

**PROVISIONAL / AWAITING INDEPENDENT AUDIT.**

Only exact algebraic identities are banked here:

* `rootCovariance_exact_decomposition` : the covariance of two root phases splits
  exactly into a `(q₁ q₂ m)`-phase plus the rational factor
  `(α/m)(h₂/(p₂q₂) - h₁/(p₁q₁))`;
* `rootCovariance_second_factor` : that rational factor has numerator
  `-N' = h₂p₁q₁ - h₁p₂q₂` over `p₁q₁p₂q₂`;
* `sourceN_eq_neg_rootN` : the source sign convention is the negative of the
  root convention.

The statements

```text
ROOT MATRIX EQUALS SOURCE-G
ARCH FACTOR IS NEGLIGIBLE
```

are **not** banked: they appear only as the uninhabited interfaces
`RootMatrixMatchesSourceG` and `ArchFactorNegligible`.
-/

namespace RouteAFibreFrame
namespace Gate01Root

/-- The root-convention cross numerator `N' = h₁ p₂ q₂ - h₂ p₁ q₁`. -/
def rootN (h₁ h₂ p₁ p₂ q₁ q₂ : ℚ) : ℚ := h₁ * p₂ * q₂ - h₂ * p₁ * q₁

/-- The source-convention cross numerator `N_source = h₂ p₁ q₁ - h₁ p₂ q₂`. -/
def sourceN (h₁ h₂ p₁ p₂ q₁ q₂ : ℚ) : ℚ := h₂ * p₁ * q₁ - h₁ * p₂ * q₂

/-- **Sign relation** `N_source = -N'`. -/
theorem sourceN_eq_neg_rootN (h₁ h₂ p₁ p₂ q₁ q₂ : ℚ) :
    sourceN h₁ h₂ p₁ p₂ q₁ q₂ = -rootN h₁ h₂ p₁ p₂ q₁ q₂ := by
  unfold sourceN rootN; ring

/-- **Exact covariance decomposition of two root phases.** -/
theorem rootCovariance_exact_decomposition
    {h₁ h₂ k alpha u₁ u₂ p₁ p₂ q₁ q₂ m J₁ J₂ : ℚ}
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0) (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) (hm : m ≠ 0)
    (hJ₁ : m * J₁ = 2 * k * p₁ * u₁ - alpha)
    (hJ₂ : m * J₂ = 2 * k * p₂ * u₂ - alpha) :
    h₁ * J₁ / (p₁ * q₁) - h₂ * J₂ / (p₂ * q₂)
      = 2 * k * (h₁ * u₁ * q₂ - h₂ * u₂ * q₁) / (q₁ * q₂ * m)
        + (alpha / m) * (h₂ / (p₂ * q₂) - h₁ / (p₁ * q₁)) := by
  have e1 : J₁ = (2 * k * p₁ * u₁ - alpha) / m := by field_simp; linarith [hJ₁]
  have e2 : J₂ = (2 * k * p₂ * u₂ - alpha) / m := by field_simp; linarith [hJ₂]
  rw [e1, e2]
  field_simp
  ring

/-- **The second factor's numerator** is `-N' = N_source`. -/
theorem rootCovariance_second_factor {h₁ h₂ p₁ p₂ q₁ q₂ : ℚ}
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0) (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) :
    h₂ / (p₂ * q₂) - h₁ / (p₁ * q₁)
      = sourceN h₁ h₂ p₁ p₂ q₁ q₂ / (p₁ * q₁ * p₂ * q₂) := by
  unfold sourceN
  field_simp

/-! ## Interfaces (never inhabited here) -/

/-- Interface: the archimedean weight is real and even. -/
def WeightRealEven (w : ℝ → ℂ) : Prop :=
  (∀ t, (w t).im = 0) ∧ (∀ t, w (-t) = w t)

/-- Interface: the archimedean factor is negligible at level `eps`.
**Not constructed anywhere.** -/
def ArchFactorNegligible (arch : ℝ → ℂ) (eps : ℝ) : Prop := ∀ t, ‖arch t‖ ≤ eps

/-- Interface: the root matrix coincides with the source-G matrix.
**Not constructed anywhere.** -/
def RootMatrixMatchesSourceG {E P : Type*} (Broot Bsource : E → P → ℂ) : Prop :=
  ∀ e p, Broot e p = Bsource e p

end Gate01Root
end RouteAFibreFrame
