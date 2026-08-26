/-
# Gate 1B safe extension — the HFMV mixed-face scope guard (SOURCE FIREWALL)

The already banked exact centering identity

    ρ_{d p}(N) = ρ_d(N) ρ_p(N) + ρ_d(N)/p + ρ_p(N)/d      (coprime `d, p > 0`)

is `TwinPrimeProject.Gate01Consolidation.rho_mul_coprime`; it is *reused*, not
re-proved.  Here it is lifted through arbitrary finite weights and finite sums
into the exact three-term decomposition

    RawCentered = MixedFace + UnaryD + UnaryP.

**Firewall.**  `MixedFace` is only one of the three terms.  The final
counterexample in this file shows that identifying `MixedFace` with the whole
raw centered source is *false* already for a single pair `(d, p) = (2, 3)`, so
no later step may silently drop the unary faces.

Nothing analytic is claimed: the weights are arbitrary, the sums are finite, and
no size estimate for any of the three faces appears.
-/
import RequestProject.NANC.Gate01Consolidation.CRTCentering

namespace Gate1B.SafeExtensions

open Finset TwinPrimeProject.Gate01Consolidation

/-- The raw centered source over a finite `d`-set and `p`-set with arbitrary
weights: `∑_{d,p} w(d,p) ρ_{dp}(N)`. -/
noncomputable def RawCentered (D P : Finset ℕ) (w : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ p ∈ P, w d p * rho (d * p) N

/-- The mixed (genuinely bilinear) face `∑_{d,p} w(d,p) ρ_d(N) ρ_p(N)`. -/
noncomputable def MixedFace (D P : Finset ℕ) (w : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ p ∈ P, w d p * (rho d N * rho p N)

/-- The unary `d`-face `∑_{d,p} w(d,p) ρ_d(N)/p`. -/
noncomputable def UnaryD (D P : Finset ℕ) (w : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ p ∈ P, w d p * (rho d N / p)

/-- The unary `p`-face `∑_{d,p} w(d,p) ρ_p(N)/d`. -/
noncomputable def UnaryP (D P : Finset ℕ) (w : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ p ∈ P, w d p * (rho p N / d)

/-- **Weighted centered face decomposition (pointwise form).**  The banked exact
identity, multiplied by an arbitrary weight. -/
theorem weightedCenteredFaceDecomposition {d p : ℕ} (hd : 0 < d) (hp : 0 < p)
    (h : Nat.Coprime d p) (N : ℕ) (c : ℝ) :
    c * rho (d * p) N = c * (rho d N * rho p N) + c * (rho d N / p) + c * (rho p N / d) := by
  rw [rho_mul_coprime hd hp h N]
  ring

/-- **Exact three-term source decomposition.**  Under the exact coprimality and
positivity hypotheses, the raw centered source is the sum of the mixed face and
the two unary faces — no error term, no analytic input. -/
theorem rawCentered_eq_mixed_add_unaryD_add_unaryP (D P : Finset ℕ) (w : ℕ → ℕ → ℝ)
    (N : ℕ) (hD : ∀ d ∈ D, 0 < d) (hP : ∀ p ∈ P, 0 < p)
    (hcop : ∀ d ∈ D, ∀ p ∈ P, Nat.Coprime d p) :
    RawCentered D P w N = MixedFace D P w N + UnaryD D P w N + UnaryP D P w N := by
  unfold RawCentered MixedFace UnaryD UnaryP
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hdD => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hpP => ?_
  exact weightedCenteredFaceDecomposition (hD d hdD) (hP p hpP) (hcop d hdD p hpP) N (w d p)

/-- **SOURCE-SCOPE FIREWALL (counterexample).**  The mixed face is *not* the raw
centered source: for `D = {2}`, `P = {3}`, unit weights and `N = 1` the raw
source is `-1/6` while the mixed face is `+1/6`.  Hence any later step that
replaces the raw shell by the mixed face without carrying the two unary faces is
wrong. -/
theorem mixedFace_ne_raw_without_unary_hypotheses :
    RawCentered {2} {3} (fun _ _ => 1) 1 ≠ MixedFace {2} {3} (fun _ _ => 1) 1 := by
  have h1 : RawCentered {2} {3} (fun _ _ => 1) 1 = -(1/6 : ℝ) := by
    simp [RawCentered, rho]
    norm_num
  have h2 : MixedFace {2} {3} (fun _ _ => 1) 1 = (1/6 : ℝ) := by
    simp [MixedFace, rho]
    norm_num
  rw [h1, h2]
  norm_num

end Gate1B.SafeExtensions
