/-
# NANC Gate 1A v9.1 — the combined `A₁* W A₂` finite operator inequality

Pure finite functional analysis.  With

* `A₁`, `A₂` weighted root-analysis maps into the common root space `ZMod n`,
  with fibre `beta`-square-mass bounds `C₁`, `C₂`;
* `W` the finite cyclic defect operator with Fourier multiplier bound `CW`,

the bilinear form `⟨A₁ f, W (A₂ g)⟩` obeys

    |⟨A₁ f, W (A₂ g)⟩|  ≤  sqrt (C₁·C₂) · CW · ‖f‖₂ · ‖g‖₂.

`RootDefectSourceFactorization` is an **interface structure**: it carries the
*hypothesis* that a hard parent form factors as `A₁* W A₂`.  No inhabitant is
constructed for any actual Gate source in this repository, so

    ROOTDEFECT-SOURCE-FACTOR1A : INTERFACE OPEN.
-/
import RequestProject.NANC.Gate1A.SafeExtensions.WeightedRootDefect
import RequestProject.NANC.Gate1A.SafeExtensions.DefectMultiplier

namespace TwinPrimeProject.NANC.Gate1A.V91

open Finset

/-- The finite `ℓ²` norm. -/
noncomputable def l2norm {ι : Type*} [Fintype ι] (f : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖f i‖ ^ 2)

theorem l2norm_nonneg {ι : Type*} [Fintype ι] (f : ι → ℂ) : 0 ≤ l2norm f :=
  Real.sqrt_nonneg _

theorem l2norm_sq {ι : Type*} [Fintype ι] (f : ι → ℂ) : l2norm f ^ 2 = ∑ i, ‖f i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)

/-- Square-bound to norm-bound. -/
theorem l2norm_le_of_sq_le {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ℂ) (g : κ → ℂ)
    (K : ℝ) (hK : 0 ≤ K) (h : ∑ i, ‖g i‖ ^ 2 ≤ K ^ 2 * ∑ i, ‖f i‖ ^ 2) :
    l2norm g ≤ K * l2norm f := by
  unfold l2norm
  calc Real.sqrt (∑ i, ‖g i‖ ^ 2)
      ≤ Real.sqrt (K ^ 2 * ∑ i, ‖f i‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = K * Real.sqrt (∑ i, ‖f i‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]

/-- Finite Cauchy–Schwarz for the pairing `⟨a, b⟩ = ∑ conj (a z) * b z`. -/
theorem abs_inner_le_l2 {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, (starRingEnd ℂ) (a i) * b i‖ ≤ l2norm a * l2norm b := by
  have hcs := Gate1B.SafeExtensions.physicalOuterCauchy (Finset.univ : Finset ι)
    (fun i => (starRingEnd ℂ) (a i)) b
  have hconj : ∑ i, ‖(starRingEnd ℂ) (a i)‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    exact Finset.sum_congr rfl fun i _ => by rw [RCLike.norm_conj]
  rw [hconj] at hcs
  have hsq : ‖∑ i, (starRingEnd ℂ) (a i) * b i‖ ^ 2 ≤ (l2norm a * l2norm b) ^ 2 := by
    rw [mul_pow, l2norm_sq, l2norm_sq]
    exact hcs
  have hnn : 0 ≤ l2norm a * l2norm b := mul_nonneg (l2norm_nonneg a) (l2norm_nonneg b)
  calc ‖∑ i, (starRingEnd ℂ) (a i) * b i‖
      = Real.sqrt (‖∑ i, (starRingEnd ℂ) (a i) * b i‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((l2norm a * l2norm b) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = l2norm a * l2norm b := Real.sqrt_sq hnn

/-- Operator bound for the weighted root analysis in `ℓ²` form. -/
theorem rootAnalysis_l2_le {ι Root : Type*} [Fintype ι] [Fintype Root] [DecidableEq Root]
    (rho : ι → Root) (beta f : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hfib : ∀ z, fibreMass rho beta z ≤ C) :
    l2norm (rootAnalysis rho beta f) ≤ Real.sqrt C * l2norm f := by
  refine l2norm_le_of_sq_le f _ _ (Real.sqrt_nonneg C) ?_
  rw [Real.sq_sqrt hC]
  exact weightedRootAnalysis_of_fibreBound rho beta f C hfib

/-- Operator bound for the defect multiplier in `ℓ²` form. -/
theorem defectOp_l2_le {n : ℕ} [NeZero n] (w g : ZMod n → ℂ) (CW : ℝ) (hCW : 0 ≤ CW)
    (hw : FourierMultiplierBound w CW) :
    l2norm (defectOp w g) ≤ CW * l2norm g :=
  l2norm_le_of_sq_le g _ _ hCW (defectOp_of_multiplierBound w g CW hCW hw)

/-- **Combined root-defect bilinear bound** (the Lean-safe abstract content of
`A₁* W A₂`). -/
theorem rootDefect_bilinear_bound {n : ℕ} [NeZero n] {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂]
    (rho₁ : ι₁ → ZMod n) (beta₁ : ι₁ → ℂ) (rho₂ : ι₂ → ZMod n) (beta₂ : ι₂ → ℂ)
    (w : ZMod n → ℂ) (f : ι₁ → ℂ) (g : ι₂ → ℂ)
    (C₁ C₂ CW : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCW : 0 ≤ CW)
    (hfib₁ : ∀ z, fibreMass rho₁ beta₁ z ≤ C₁)
    (hfib₂ : ∀ z, fibreMass rho₂ beta₂ z ≤ C₂)
    (hw : FourierMultiplierBound w CW) :
    ‖∑ z : ZMod n, (starRingEnd ℂ) (rootAnalysis rho₁ beta₁ f z)
        * defectOp w (rootAnalysis rho₂ beta₂ g) z‖
      ≤ Real.sqrt (C₁ * C₂) * CW * l2norm f * l2norm g := by
  have h1 : l2norm (rootAnalysis rho₁ beta₁ f) ≤ Real.sqrt C₁ * l2norm f :=
    rootAnalysis_l2_le rho₁ beta₁ f C₁ hC₁ hfib₁
  have h2 : l2norm (rootAnalysis rho₂ beta₂ g) ≤ Real.sqrt C₂ * l2norm g :=
    rootAnalysis_l2_le rho₂ beta₂ g C₂ hC₂ hfib₂
  have h3 : l2norm (defectOp w (rootAnalysis rho₂ beta₂ g)) ≤ CW * (Real.sqrt C₂ * l2norm g) :=
    (defectOp_l2_le w _ CW hCW hw).trans (mul_le_mul_of_nonneg_left h2 hCW)
  have hpair := abs_inner_le_l2 (rootAnalysis rho₁ beta₁ f)
    (defectOp w (rootAnalysis rho₂ beta₂ g))
  refine hpair.trans ?_
  have hmul : l2norm (rootAnalysis rho₁ beta₁ f)
      * l2norm (defectOp w (rootAnalysis rho₂ beta₂ g))
      ≤ (Real.sqrt C₁ * l2norm f) * (CW * (Real.sqrt C₂ * l2norm g)) := by
    exact mul_le_mul h1 h3 (l2norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (l2norm_nonneg _))
  refine hmul.trans_eq ?_
  rw [Real.sqrt_mul hC₁]
  ring

/-! ## Source factorization interface (no inhabitant is constructed) -/

/-- **Interface structure.**  A witness that a hard parent bilinear form is
*exactly* an `A₁* W A₂` root-defect form.  Constructing an inhabitant for the
actual Gate source would require the literal authoritative source coefficient in
Lean; none is constructed here. -/
structure RootDefectSourceFactorization (n : ℕ) [NeZero n] where
  /-- Left state space. -/
  State₁ : Type
  /-- Right state space. -/
  State₂ : Type
  [fin₁ : Fintype State₁]
  [fin₂ : Fintype State₂]
  /-- Left root map. -/
  rho₁ : State₁ → ZMod n
  /-- Right root map. -/
  rho₂ : State₂ → ZMod n
  /-- Left analysis weights. -/
  beta₁ : State₁ → ℂ
  /-- Right analysis weights. -/
  beta₂ : State₂ → ℂ
  /-- Defect translation weight. -/
  w : ZMod n → ℂ
  /-- The hard parent bilinear form. -/
  hardParent : (State₁ → ℂ) → (State₂ → ℂ) → ℂ
  /-- The factorization hypothesis. -/
  factorization : ∀ f g, hardParent f g =
    ∑ z : ZMod n, (starRingEnd ℂ) (@rootAnalysis State₁ (ZMod n) fin₁ _ rho₁ beta₁ f z)
      * defectOp w (@rootAnalysis State₂ (ZMod n) fin₂ _ rho₂ beta₂ g) z

attribute [instance] RootDefectSourceFactorization.fin₁ RootDefectSourceFactorization.fin₂

/-- **Hard-parent bound from the factorization interface.**  A factorization,
fibre-mass bounds and a Fourier multiplier bound give the hard-parent estimate. -/
theorem RootDefectSourceFactorization.bound {n : ℕ} [NeZero n]
    (S : RootDefectSourceFactorization n) (f : S.State₁ → ℂ) (g : S.State₂ → ℂ)
    (C₁ C₂ CW : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCW : 0 ≤ CW)
    (hfib₁ : ∀ z, fibreMass S.rho₁ S.beta₁ z ≤ C₁)
    (hfib₂ : ∀ z, fibreMass S.rho₂ S.beta₂ z ≤ C₂)
    (hw : FourierMultiplierBound S.w CW) :
    ‖S.hardParent f g‖ ≤ Real.sqrt (C₁ * C₂) * CW * l2norm f * l2norm g := by
  rw [S.factorization f g]
  exact rootDefect_bilinear_bound S.rho₁ S.beta₁ S.rho₂ S.beta₂ S.w f g C₁ C₂ CW
    hC₁ hC₂ hCW hfib₁ hfib₂ hw

end TwinPrimeProject.NANC.Gate1A.V91
