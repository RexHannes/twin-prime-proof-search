/-
# Gate1B / R11 / Frontier : the unmodified-row compiler

The replacement architecture at the exact/algebraic level.  The original arithmetic values
`d_i^0 = w_i · D_i` are kept; **no synthetic value is inserted at a target-zero position**.

* `CardinalInterpolation` is a generic cardinal-interpolation object: centres `z_u`, width `h`,
  kernel `psi`, with the hypotheses `psi 0 = 1`, `psi` vanishing at the other centres, and pairwise
  disjoint interpolation cells.  Injectivity of the centres is *derived* from disjointness.
* `interpolant_sample` is the exact sample recovery `H (z_u) = d_i^0 (u)`.
* `interpolant_eq_sum_support` shows that positions carrying the value `0` contribute nothing:
  the compiler never inserts synthetic mass.
* The Fourier-transform statement is an **explicit interface** (`FourierInterface`), a bundle of
  theorem hypotheses — not an axiom.  `interpolant_transform` is the conditional finite-sum
  transform identity derived from it.
* `§ width scaling`: the exact scale identities `θ = L^{−m}`, `h_i = θ k_i /(C Y)` and
  `T₁ = P θ^{−1} L³ = P L^{m+3}`, plus the invariance of the product
  (row energy) × (Mellin height).

**Firewall.**  Nothing here asserts an arithmetic saving.  The last theorem shows that the scale
identity alone leaves `T₁` unbounded, so "narrow interpolation" by itself creates no cancellation,
and the arbitrary-log analytic estimate is *not* formalised as a theorem.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

namespace Gate1B.R11.Frontier

open Finset

noncomputable section

/-! ## 1. The cardinal interpolation object -/

/-- A generic cardinal-interpolation object on an index type `ι`. -/
structure CardinalInterpolation (ι : Type*) where
  /-- Interpolation centres. -/
  z : ι → ℝ
  /-- Interpolation width. -/
  h : ℝ
  /-- The width is positive. -/
  h_pos : 0 < h
  /-- Interpolation kernel. -/
  psi : ℝ → ℂ
  /-- Normalisation at the centre. -/
  psi_zero : psi 0 = 1
  /-- The kernel vanishes at every other centre. -/
  psi_vanish : ∀ u v : ι, u ≠ v → psi ((z u - z v) / h) = 0
  /-- The interpolation cells. -/
  cell : ι → Set ℝ
  /-- Each centre lies in its own cell. -/
  mem_cell : ∀ u : ι, z u ∈ cell u
  /-- The cells are pairwise disjoint. -/
  cell_disjoint : Pairwise (Function.onFun Disjoint cell)

variable {ι : Type*}

/-- **Disjoint supports force distinct centres.** -/
theorem CardinalInterpolation.z_injective (C : CardinalInterpolation ι) :
    Function.Injective C.z := by
  intro u v huv
  by_contra hne
  have hdisj := C.cell_disjoint hne
  have h1 : C.z u ∈ C.cell u := C.mem_cell u
  have h2 : C.z u ∈ C.cell v := huv ▸ C.mem_cell v
  exact (Set.disjoint_left.mp hdisj h1) h2

/-- The interpolant of the *unmodified* row data `d` on the finite index set `S`. -/
def interpolant (C : CardinalInterpolation ι) (S : Finset ι) (d : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ u ∈ S, d u * C.psi ((x - C.z u) / C.h)

/-- **EXACT SAMPLE RECOVERY** `H (z_u) = d u`. -/
theorem interpolant_sample (C : CardinalInterpolation ι) (S : Finset ι) (d : ι → ℂ) {u : ι}
    (hu : u ∈ S) : interpolant C S d (C.z u) = d u := by
  rw [interpolant, Finset.sum_eq_single u]
  · rw [sub_self, zero_div, C.psi_zero, mul_one]
  · intro v _ hv
    rw [C.psi_vanish u v (Ne.symm hv), mul_zero]
  · intro h; exact absurd hu h

/-- **NO SYNTHETIC VALUES.**  Only the positions carrying a nonzero original value contribute:
the compiler inserts nothing where the row value is `0`. -/
theorem interpolant_eq_sum_support (C : CardinalInterpolation ι) (S : Finset ι) (d : ι → ℂ)
    (x : ℝ) : interpolant C S d x = ∑ u ∈ S.filter (fun u => d u ≠ 0),
      d u * C.psi ((x - C.z u) / C.h) := by
  rw [interpolant, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : d u = 0 <;> simp [h]

/-- In particular the interpolant of the zero row is zero. -/
theorem interpolant_of_zero (C : CardinalInterpolation ι) (S : Finset ι) (d : ι → ℂ)
    (hd : ∀ u ∈ S, d u = 0) (x : ℝ) : interpolant C S d x = 0 :=
  Finset.sum_eq_zero fun u hu => by rw [hd u hu, zero_mul]

/-- The compiled row values `d_i^0 = w_i · D_i` (product-fibre weight times the row kernel);
no other data enter the interpolant. -/
def compiledRow (w D : ι → ℂ) (u : ι) : ℂ := w u * D u

/-- Sample recovery for the compiled row: the interpolant reproduces `w_i D_i` exactly. -/
theorem interpolant_compiledRow (C : CardinalInterpolation ι) (S : Finset ι) (w D : ι → ℂ)
    {u : ι} (hu : u ∈ S) :
    interpolant C S (compiledRow w D) (C.z u) = w u * D u :=
  interpolant_sample C S (compiledRow w D) hu

/-! ## 2. The Fourier-transform interface (hypotheses, not axioms) -/

/-- An **interface** for the transform of the interpolation kernel: a transform operator, its
linearity over finite sums, and the transform of a single shifted kernel.  These are theorem
hypotheses supplied by the caller; nothing is postulated. -/
structure FourierInterface (ι : Type*) (C : CardinalInterpolation ι) where
  /-- The transform operator. -/
  FT : (ℝ → ℂ) → ℝ → ℂ
  /-- The transform of the unshifted kernel. -/
  psiHat : ℝ → ℂ
  /-- Linearity of the transform over finite sums with complex coefficients. -/
  FT_sum : ∀ (S : Finset ι) (c : ι → ℂ) (g : ι → ℝ → ℂ) (t : ℝ),
    FT (fun x => ∑ u ∈ S, c u * g u x) t = ∑ u ∈ S, c u * FT (g u) t
  /-- The transform of a single shifted kernel. -/
  FT_kernel : ∀ (z0 t : ℝ),
    FT (fun x => C.psi ((x - z0) / C.h)) t
      = (C.h : ℂ) * psiHat (C.h * t) * Complex.exp (-(2 * Real.pi * Complex.I) * (z0 * t))

/-- **CONDITIONAL TRANSFORM IDENTITY.**  Given the interface, the transform of the interpolant is
the kernel transform times the exact finite exponential sum of the *original* row values. -/
theorem interpolant_transform (C : CardinalInterpolation ι) (F : FourierInterface ι C)
    (S : Finset ι) (d : ι → ℂ) (t : ℝ) :
    F.FT (interpolant C S d) t
      = (C.h : ℂ) * F.psiHat (C.h * t) *
          ∑ u ∈ S, d u * Complex.exp (-(2 * Real.pi * Complex.I) * (C.z u * t)) := by
  rw [show interpolant C S d = fun x => ∑ u ∈ S, d u * C.psi ((x - C.z u) / C.h) from rfl,
    F.FT_sum S d (fun u x => C.psi ((x - C.z u) / C.h)) t]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [F.FT_kernel (C.z u) t]
  ring

/-! ## 3. Width-scaling algebra -/

/-- The declared width identity `h_i = θ k_i /(C Y)`. -/
def widthOf (theta k Cc Y : ℝ) : ℝ := theta * k / (Cc * Y)

/-- Halving `θ` halves every interpolation width: the scaling is exactly linear. -/
theorem widthOf_scale (theta k Cc Y lam : ℝ) :
    widthOf (lam * theta) k Cc Y = lam * widthOf theta k Cc Y := by
  unfold widthOf; ring

/-- **THE SCALE IDENTITY** `T₁ = P θ^{-1} L³ = P L^{m+3}` for `θ = L^{−m}`, `L > 0`. -/
theorem mellin_height_scale {L P m theta T1 : ℝ} (hL : 0 < L)
    (htheta : theta = L ^ (-m)) (hT1 : T1 = P * theta⁻¹ * L ^ (3 : ℝ)) :
    T1 = P * L ^ (m + 3) := by
  have hinv : theta⁻¹ = L ^ m := by
    rw [htheta, Real.rpow_neg hL.le, inv_inv]
  rw [hT1, hinv, mul_assoc, ← Real.rpow_add hL]

/-- The row-energy / Mellin-height trade-off is exactly a trade-off: narrowing by `θ` divides the
interpolation energy by `θ^{-1}` and multiplies the Mellin height by `θ^{-1}`, leaving the product
**invariant**. -/
theorem energy_height_product_invariant (E0 H0 theta : ℝ) (hne : theta ≠ 0) :
    (theta * E0) * (theta⁻¹ * H0) = E0 * H0 := by
  field_simp

/-! ## 4. Firewall: the scale identity is not an analytic saving -/

/-- **NARROW INTERPOLATION CREATES NO ARITHMETIC SAVING.**  The scale identity alone leaves the
Mellin height `T₁` unbounded: for every bound `B` there are admissible scale data with `T₁ > B`.
Hence no estimate may be read off from the scaling algebra. -/
theorem narrow_interpolation_no_free_saving (B : ℝ) :
    ∃ L P m theta T1 : ℝ, 0 < L ∧ 0 ≤ m ∧ theta = L ^ (-m) ∧
      T1 = P * theta⁻¹ * L ^ (3 : ℝ) ∧ T1 = P * L ^ (m + 3) ∧ B < T1 := by
  refine ⟨Real.exp 1, 1, max B 0, (Real.exp 1) ^ (-(max B 0)),
    1 * ((Real.exp 1) ^ (-(max B 0)))⁻¹ * (Real.exp 1) ^ (3 : ℝ),
    Real.exp_pos 1, le_max_right _ _, rfl, rfl, ?_, ?_⟩
  · exact mellin_height_scale (Real.exp_pos 1) rfl rfl
  · rw [mellin_height_scale (L := Real.exp 1) (P := 1) (m := max B 0) (Real.exp_pos 1) rfl rfl,
      one_mul, Real.exp_one_rpow]
    have h1 : max B 0 + 3 + 1 ≤ Real.exp (max B 0 + 3) := Real.add_one_le_exp _
    have h2 : B ≤ max B 0 := le_max_left _ _
    linarith

end

end Gate1B.R11.Frontier
