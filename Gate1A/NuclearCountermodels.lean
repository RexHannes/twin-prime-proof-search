/-
# Gate-1A: two mandatory nuclear-scale countermodels (A5 and A10)

**A5 — `uniform_row_smoothness_not_nuclear_transport`.**
Uniform row-wise smoothness (every row a unit `ℓ²` vector with entries of
modulus `≤ 1`, i.e. a common envelope) does **not** bound the nuclear
`ℓ¹` mass of any rank-one decomposition.  The identity matrix on `Fin s`
has perfectly uniform rows, yet every decomposition
`A i j = ∑_λ α_λ u_λ(i) v_λ(j)` with `ℓ²`-normalised factors obeys
`∑_λ |α_λ| ≥ s`.

**A10 — `scalar_l1_mass_not_operator_norm`.**
Scalar `ℓ¹` mass is not the operator norm: the identity and the
single-row matrix on `Fin s` have the *same* `ℓ¹` entry mass `s`, while
their `ℓ²→ℓ²` operator norms are `1` and `√s`.

Both are finite, fully kernel-checked constructions.
-/
import Mathlib

namespace Gate1A

namespace NuclearCountermodels

open Finset Matrix

/-! ### A5: uniform row smoothness does not bound nuclear mass -/

/-- Cauchy–Schwarz for `ℓ²`-normalised complex vectors:
`|∑_i u_i v_i| ≤ 1`. -/
theorem abs_inner_le_one {s : ℕ} (u v : Fin s → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 ≤ 1) (hv : ∑ i, ‖v i‖ ^ 2 ≤ 1) :
    ‖∑ i, u i * v i‖ ≤ 1 := by
  have h1 : ‖∑ i, u i * v i‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => norm_mul _ _
  have h2 : (∑ i, ‖u i‖ * ‖v i‖) ^ 2
      ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hnn : (0 : ℝ) ≤ ∑ i, ‖u i‖ * ‖v i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hA : (0 : ℝ) ≤ ∑ i, ‖u i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ 1 := by
    refine h2.trans ?_
    calc (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hv hA
      _ ≤ 1 := by simpa using hu
  refine h1.trans ?_
  nlinarith [hnn, h3]

/-- **`uniform_row_smoothness_not_nuclear_transport`** (A5).

The identity matrix on `Fin s` has completely uniform rows — every entry has
modulus `≤ 1` and every row is a unit `ℓ²` vector — and yet **every**
rank-one decomposition with `ℓ²`-normalised factors costs nuclear `ℓ¹` mass
at least `s`.

Hence uniform row-wise smoothness (a common envelope) is *not* a nuclear
transport bound. -/
theorem uniform_row_smoothness_not_nuclear_transport (s : ℕ) :
    ∃ A : Matrix (Fin s) (Fin s) ℂ,
      (∀ i j, ‖A i j‖ ≤ 1) ∧
      (∀ i, ∑ j, ‖A i j‖ ^ 2 = 1) ∧
      (∀ (r : ℕ) (alpha : Fin r → ℂ) (u v : Fin r → Fin s → ℂ),
        (∀ l, ∑ i, ‖u l i‖ ^ 2 ≤ 1) → (∀ l, ∑ j, ‖v l j‖ ^ 2 ≤ 1) →
        (∀ i j, A i j = ∑ l, alpha l * u l i * v l j) →
        (s : ℝ) ≤ ∑ l, ‖alpha l‖) := by
  classical
  refine ⟨(1 : Matrix (Fin s) (Fin s) ℂ), ?_, ?_, ?_⟩
  · intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · intro i
    simp [Matrix.one_apply, apply_ite (norm : ℂ → ℝ), Finset.sum_ite_eq]
  · intro r alpha u v hu hv hdec
    -- compute the trace two ways
    have htr : ((s : ℕ) : ℂ) = ∑ l, alpha l * ∑ i, u l i * v l i := by
      have h1 : ∑ i, (1 : Matrix (Fin s) (Fin s) ℂ) i i = ((s : ℕ) : ℂ) := by
        simp
      rw [← h1]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ univ) => hdec i i)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hbound : ‖∑ l, alpha l * ∑ i, u l i * v l i‖ ≤ ∑ l, ‖alpha l‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [norm_mul]
      calc ‖alpha l‖ * ‖∑ i, u l i * v l i‖ ≤ ‖alpha l‖ * 1 :=
            mul_le_mul_of_nonneg_left (abs_inner_le_one _ _ (hu l) (hv l))
              (norm_nonneg _)
        _ = ‖alpha l‖ := mul_one _
    have : ((s : ℕ) : ℝ) = ‖((s : ℕ) : ℂ)‖ := by simp
    rw [this, htr]
    exact hbound

/-! ### A10: scalar `ℓ¹` mass is not the operator norm -/

/-- The scalar `ℓ¹` entry mass of a finite complex matrix. -/
noncomputable def l1mass {s : ℕ} (A : Matrix (Fin s) (Fin s) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖

/-- The single-row matrix: every entry of row `0` is `1`, all other rows
vanish. -/
def singleRow (s : ℕ) [NeZero s] : Matrix (Fin s) (Fin s) ℂ :=
  fun i _ => if i = 0 then 1 else 0

/-- **`scalar_l1_mass_not_operator_norm`** (A10).

The identity and the single-row matrix on `Fin s` have *the same* scalar
`ℓ¹` entry mass, namely `s`, but their `ℓ²` operator norms differ by the
factor `√s`: the identity is an isometry, while the single-row matrix
amplifies the all-ones vector's energy by exactly `s`.

Hence an `ℓ¹` nuclear/scalar mass bound may **not** be identified with an
operator-norm bound. -/
theorem scalar_l1_mass_not_operator_norm (s : ℕ) [NeZero s] :
    l1mass (1 : Matrix (Fin s) (Fin s) ℂ) = s ∧
    l1mass (singleRow s) = s ∧
    (∀ x : Fin s → ℂ,
      ∑ i, ‖((1 : Matrix (Fin s) (Fin s) ℂ) *ᵥ x) i‖ ^ 2 = ∑ j, ‖x j‖ ^ 2) ∧
    (∑ i, ‖(singleRow s *ᵥ (fun _ => 1)) i‖ ^ 2
      = (s : ℝ) * ∑ _j : Fin s, ‖(1 : ℂ)‖ ^ 2) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [l1mass, Matrix.one_apply, apply_ite (norm : ℂ → ℝ), Finset.sum_ite_eq]
  · simp [l1mass, singleRow, apply_ite (norm : ℂ → ℝ), Finset.sum_ite_eq']
  · intro x
    simp
  · have hval : ∀ i : Fin s,
        (singleRow s *ᵥ (fun _ => (1 : ℂ))) i = if i = 0 then (s : ℂ) else 0 := by
      intro i
      by_cases h : i = 0 <;>
        simp [singleRow, Matrix.mulVec, dotProduct, h]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ univ) => by rw [hval i])]
    simp [apply_ite (norm : ℂ → ℝ), Finset.sum_ite_eq', sq]

end NuclearCountermodels

end Gate1A
