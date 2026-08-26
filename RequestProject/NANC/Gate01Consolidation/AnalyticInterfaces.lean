import RequestProject.NANC.Gate01Consolidation.ESeparation
import RequestProject.NANC.Gate01Consolidation.PrimeCovariance
import RequestProject.NANC.Gate01Consolidation.DirectGaussReassembly
import RequestProject.NANC.Gate01Consolidation.ExponentThresholds

/-!
# Analytic interfaces (never inhabited) and conditional implications

Every proposition in this module is an **explicit interface**: a named,
parametrised proposition that this development never proves and never
instantiates.  Following the convention already used elsewhere in the project,
interfaces are definite propositions (not structures with a free `Prop` field,
which would be trivially inhabitable).

Interfaces created here:

* `SwitchedCenteredMixedCovarianceBound` — the switched centered mixed
  covariance estimate for `ρ_d(mn+2) ρ_p(mn+2)` at `d p = X^{13/18}`;
* `R9FourFiveDispersionBound` — the `q`-averaged `4|5` dispersion estimate;
* `DirectPhysicalPhaseBound` — the bound for the direct physical phase
  `e_c(2kN · ((m+kr)p₁p₂)⁻¹)`.

Everything proved below is a *conditional* implication: each theorem takes the
interfaces as hypotheses, and every such name contains `conditional` or
`of_interfaces`.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-! ## The finite objects the interfaces speak about -/

/-- The finite `4|5` dispersion object: a `q`-averaged, main-term-subtracted
bilinear sum over `u v ≡ −2 (mod q)`.  This is a *definition*, not an estimate. -/
noncomputable def fourFiveDispersion (Qset Uset Vset : Finset ℕ)
    (xi a b : ℕ → ℝ) (MT : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Qset, xi q *
    ((∑ u ∈ Uset, ∑ v ∈ Vset, if q ∣ u * v + 2 then a u * b v else 0) - MT q)

/-- The finite double-centered mixed covariance object attached to a window `S`
and a pair of moduli `(d, p)`. -/
noncomputable def switchedMixedCovariance (S : Finset ℕ) (d p : ℕ)
    (m : ℕ) : ℝ :=
  ∑ n ∈ S, rho d (m * n + 2) * rho p (m * n + 2)

/-! ## Explicit interfaces (never inhabited) -/

/-- **EXPLICIT INTERFACE / OPEN ANALYTIC.**  The switched centered mixed
covariance bound at the endpoint `d p = X^{13/18}`.  The exponent hypothesis is
recorded as an explicit premise; no inhabitant is ever produced. -/
def SwitchedCenteredMixedCovarianceBound (S : Finset ℕ) (d p m : ℕ)
    (bound : ℝ) : Prop :=
  |switchedMixedCovariance S d p m| ≤ bound

/-- **EXPLICIT INTERFACE / OPEN ANALYTIC.**  The `q`-averaged `4|5` dispersion
estimate at `q ∼ X^{13/18}`, `u ∼ X^{4/9}`, `v ∼ X^{5/9}`. -/
def R9FourFiveDispersionBound (Qset Uset Vset : Finset ℕ) (xi a b MT : ℕ → ℝ)
    (bound : ℝ) : Prop :=
  |fourFiveDispersion Qset Uset Vset xi a b MT| ≤ bound

/-- **EXPLICIT INTERFACE / OPEN ANALYTIC.**  The direct physical-phase bound for
`e_c(2kN · ((m+kr)p₁p₂)⁻¹)` summed over the direct family. -/
def DirectPhysicalPhaseBound {ι : Type*} (F : Finset ι) (phase : ι → ℂ)
    (bound : ℝ) : Prop :=
  ‖∑ i ∈ F, phase i‖ ≤ bound

/-! ## Conditional implications -/

/-- **Conditional.**  E-separation converts a bound on the nonzero-frequency
term together with a bound on the zero mode into a bound on the centered
progression mass.  The analytic input is entirely in the first hypothesis; the
identity alone gives nothing. -/
theorem centered_progression_bound_of_interfaces {q : ℕ} (hq : 0 < q)
    (S : Finset ℕ) (c : ℕ → ℂ) (E : ℂ) {b₀ b₁ : ℝ}
    (hzero : ‖fullSum S c / (q : ℂ) - E‖ ≤ b₀)
    (hnz : ‖nonzeroFreqTerm S q c‖ ≤ b₁) :
    ‖congrSum S q c - E‖ ≤ b₀ + b₁ := by
  rw [esep2 hq S c E]
  exact le_trans (norm_add_le _ _) (add_le_add hzero hnz)

/-- **Conditional.**  The `4|5` fixed-cell switched closure: the regrouped
target is controlled once (i) the `q`-averaged dispersion interface is granted,
(ii) the exact coefficient routing identity is supplied, and (iii) the zero mode
is controlled.  Every analytically unproved premise is explicit. -/
theorem fourFive_fixedCell_closure_conditional
    {Qset Uset Vset : Finset ℕ} {xi a b MT : ℕ → ℝ} {target zeroMode : ℝ}
    {b₁ b₂ : ℝ}
    (hrouting : target = fourFiveDispersion Qset Uset Vset xi a b MT + zeroMode)
    (hdisp : R9FourFiveDispersionBound Qset Uset Vset xi a b MT b₁)
    (hzero : |zeroMode| ≤ b₂) :
    |target| ≤ b₁ + b₂ := by
  rw [hrouting]
  exact le_trans (abs_add_le _ _) (add_le_add hdisp hzero)

/-- **Conditional.**  The direct-family target follows from the direct physical
phase bound only when the source normalisation and all coefficient/prefactor
data are supplied explicitly (here: the normalisation identity and the
prefactor bound). -/
theorem direct_family_target_conditional {ι : Type*} {F : Finset ι}
    {phase : ι → ℂ} {target : ℂ} {prefactor : ℝ} {bound : ℝ}
    (hnorm : target = (prefactor : ℂ) * ∑ i ∈ F, phase i)
    (hpre : 0 ≤ prefactor)
    (hphase : DirectPhysicalPhaseBound F phase bound) :
    ‖target‖ ≤ prefactor * bound := by
  rw [hnorm, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpre]
  exact mul_le_mul_of_nonneg_left hphase hpre

/-- **Conditional.**  The prime-centered second moment is controlled exactly
when the off-diagonal of the covariance kernel is: the identity P2MOM is finite
algebra, the bound is not. -/
theorem prime_second_moment_bound_of_interfaces {ι : Type*} (I : Finset ι)
    (P : Finset ℕ) (A : ι → ℂ) (Y : ι → ℕ) {bound : ℝ}
    (hker : ‖∑ i ∈ I, ∑ j ∈ I, A i * (starRingEnd ℂ) (A j)
      * (covKernel P (Y i) (Y j) : ℂ)‖ ≤ bound) :
    ‖∑ p ∈ P, (Complex.normSq (centeredForm I A Y p) : ℂ)‖ ≤ bound := by
  rw [sum_normSq_centeredForm_norm I P A Y]
  exact hker

end Gate01Consolidation
end TwinPrimeProject
