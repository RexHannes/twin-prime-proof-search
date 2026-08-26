/-
# NANC Gate 1A v9.4 — smooth `r`-source envelope

The common source coefficient is **not** `r`-independent.  The corrected route
carries a *smooth envelope*

    c X r  =  B X · F X (r / R),

with `B` an `r`-free amplitude and `F` a profile evaluated at the normalized
ratio `r / R`.  This file banks the finite algebra of that shape:

* the factorization is a structure field, never a theorem about the actual
  source;
* the `r`-dependence is genuine (countermodel);
* a Lipschitz profile gives an exact finite modulus-of-continuity bound.

All analytic facts about the actual source (smoothness, derivative size,
support) remain certificate fields — they are hypotheses, not theorems.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

/-- A **smooth `r`-source envelope**: the source coefficient factors as an
`r`-free amplitude times a profile evaluated at `r / R`. -/
structure SmoothRSourceEnvelope where
  /-- The normalizing scale. -/
  R : ℝ
  hR : 0 < R
  /-- The `r`-free amplitude. -/
  B : ℝ → ℝ
  /-- The profile, as a function of the scaling variable `X` and the ratio. -/
  F : ℝ → ℝ → ℝ
  /-- The source coefficient. -/
  c : ℝ → ℝ → ℝ
  /-- The envelope factorization. -/
  factor : ∀ X r, c X r = B X * F X (r / R)

namespace SmoothRSourceEnvelope

variable (E : SmoothRSourceEnvelope)

/-- Any `r`-dependence of the coefficient is `r`-dependence of the profile. -/
theorem profile_of_coeff_ne {X r₁ r₂ : ℝ} (h : E.c X r₁ ≠ E.c X r₂) :
    E.F X (r₁ / E.R) ≠ E.F X (r₂ / E.R) := by
  intro hF
  exact h (by rw [E.factor, E.factor, hF])

/-- **Modulus of continuity.**  A Lipschitz profile yields an exact finite
bound on the variation of the source coefficient in `r`. -/
theorem coeff_lipschitz {X : ℝ} {K : ℝ}
    (hF : ∀ t s : ℝ, |E.F X t - E.F X s| ≤ K * |t - s|) (r₁ r₂ : ℝ) :
    |E.c X r₁ - E.c X r₂| ≤ |E.B X| * K * |r₁ - r₂| / E.R := by
  have hR := E.hR
  rw [E.factor, E.factor, ← mul_sub, abs_mul]
  have h1 : |E.F X (r₁ / E.R) - E.F X (r₂ / E.R)| ≤ K * |r₁ / E.R - r₂ / E.R| := hF _ _
  have h2 : |r₁ / E.R - r₂ / E.R| = |r₁ - r₂| / E.R := by
    rw [div_sub_div_same, abs_div, abs_of_pos hR]
  rw [h2] at h1
  calc |E.B X| * |E.F X (r₁ / E.R) - E.F X (r₂ / E.R)|
      ≤ |E.B X| * (K * (|r₁ - r₂| / E.R)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |E.B X| * K * |r₁ - r₂| / E.R := by ring

end SmoothRSourceEnvelope

/-- **The common source is not `r`-independent.**  There is a smooth envelope
whose coefficient genuinely varies with `r`; hence no step may treat the common
source as a fixed `r`-free constant. -/
theorem commonSource_not_rIndependent :
    ∃ E : SmoothRSourceEnvelope, ∃ X r₁ r₂ : ℝ, E.c X r₁ ≠ E.c X r₂ := by
  refine ⟨{ R := 1, hR := one_pos, B := fun _ => 1, F := fun _ t => t,
            c := fun _ r => r, factor := by intro X r; simp }, 0, 0, 1, ?_⟩
  norm_num

/-- The analytic data about the actual source, kept strictly as an interface:
smoothness, derivative size and support are *hypotheses*, never theorems. -/
structure SmoothEnvelopeCertificate where
  envelope : SmoothRSourceEnvelope
  /-- Lipschitz constant of the profile (analytic input). -/
  K : ℝ
  hK : 0 ≤ K
  lipschitz : ∀ X t s : ℝ, |envelope.F X t - envelope.F X s| ≤ K * |t - s|
  /-- Amplitude bound (analytic input). -/
  Bbound : ℝ
  hBbound : ∀ X, |envelope.B X| ≤ Bbound

/-- The certificate yields a uniform finite variation bound. -/
theorem SmoothEnvelopeCertificate.variation_bound (C : SmoothEnvelopeCertificate)
    (X r₁ r₂ : ℝ) :
    |C.envelope.c X r₁ - C.envelope.c X r₂| ≤ C.Bbound * C.K * |r₁ - r₂| / C.envelope.R := by
  refine (C.envelope.coeff_lipschitz (fun t s => C.lipschitz X t s) r₁ r₂).trans ?_
  have hR := C.envelope.hR
  have hxy : |C.envelope.B X| * C.K * |r₁ - r₂| ≤ C.Bbound * C.K * |r₁ - r₂| :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (C.hBbound X) C.hK) (abs_nonneg _)
  gcongr

end TwinPrimeProject.NANC.Gate1A.V94
