/-
# Universal safe algebra — quadratic / sesquilinear homogeneity, and the
  absence of a free positive energy floor

Everything in this file is exact finite algebra over a normed / inner-product
scalar setting.  There is no asymptotic statement, no `X^o(1)`, and no analytic
input of any kind.

Contents.

* `quadraticEnergy`  —  `Energy(c) = ∑ i, ‖c i‖^2` over a `Finset`.
* `quadraticEnergy_smul`  —  `Energy(λ • c) = ‖λ‖^2 * Energy(c)`.
* `sesquilinear_same_smul`  —  `⟪λ • x, λ • y⟫ = ‖λ‖^2 * ⟪x, y⟫` for a complex
  inner product space.
* `zeroEnergy_counterexample`  —  the energy of the zero family vanishes even
  though the index family is nonempty.
* `noPositiveUniformEnergyFloor`  —  **the permanent lesson**: an upper bound
  `Energy ≤ C * card` never implies a lower bound `Energy ≥ c * card` for
  arbitrary coefficient families.

Nothing here mentions Gate 1B; the Gate-labelled consequences live in
`Gate1B/SafeExtensions/C2FloorGuard.lean`.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

/-- Quadratic energy of a finite coefficient family: `∑ i ∈ s, ‖c i‖ ^ 2`. -/
def quadraticEnergy {ι : Type*} {E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (c : ι → E) : ℝ :=
  ∑ i ∈ s, ‖c i‖ ^ 2

theorem quadraticEnergy_nonneg {ι : Type*} {E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (c : ι → E) : 0 ≤ quadraticEnergy s c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Exact quadratic homogeneity.**  Scaling every coefficient by `lam`
multiplies the energy by exactly `‖lam‖ ^ 2`. -/
theorem quadraticEnergy_smul {ι : Type*} {𝕜 E : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s : Finset ι) (lam : 𝕜) (c : ι → E) :
    quadraticEnergy s (fun i => lam • c i) = ‖lam‖ ^ 2 * quadraticEnergy s c := by
  unfold quadraticEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_smul, mul_pow]

/-- **Exact sesquilinear homogeneity.**  For a complex inner product space,
`⟪lam • x, lam • y⟫ = ‖lam‖ ^ 2 * ⟪x, y⟫`. -/
theorem sesquilinear_same_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (lam : ℂ) (x y : H) :
    (inner ℂ (lam • x) (lam • y) : ℂ) = (‖lam‖ : ℂ) ^ 2 * inner ℂ x y := by
  have hlam : (starRingEnd ℂ) lam * lam = (‖lam‖ : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    push_cast [Complex.normSq_eq_norm_sq]
    ring
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, hlam]

/-- The bilinear finite-sum version: a finite sesquilinear form built from a
kernel is exactly `‖lam‖ ^ 2`-homogeneous under simultaneous scaling. -/
theorem finiteSesquilinearForm_smul {ι : Type*} (s : Finset ι) (K : ι → ι → ℂ)
    (lam : ℂ) (x y : ι → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, K i j * (starRingEnd ℂ) (lam • x i) * (lam • y j))
      = (‖lam‖ : ℂ) ^ 2 * ∑ i ∈ s, ∑ j ∈ s, K i j * (starRingEnd ℂ) (x i) * y j := by
  have hlam : (starRingEnd ℂ) lam * lam = (‖lam‖ : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    push_cast [Complex.normSq_eq_norm_sq]
    ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul, map_mul]
  rw [← hlam]
  ring

/-- **No free lower floor, step 1.**  The zero family has zero energy on an
arbitrary index set. -/
theorem zeroEnergy_counterexample {ι : Type*} (s : Finset ι) :
    quadraticEnergy s (fun _ => (0 : ℂ)) = 0 := by
  simp [quadraticEnergy]

/-- **No free lower floor, step 2 (the permanent lesson).**  There is no
positive constant `c` for which every finite coefficient family satisfies
`Energy ≥ c * card`.  In particular an upper bound of the shape
`Energy ≤ C * Q` carries *no* information towards `Energy ≥ c * Q`. -/
theorem noPositiveUniformEnergyFloor :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (a : Fin n → ℂ),
        c * (n : ℝ) ≤ quadraticEnergy (Finset.univ : Finset (Fin n)) a := by
  rintro ⟨c, hc, h⟩
  have h1 := h 1 (fun _ => (0 : ℂ))
  rw [zeroEnergy_counterexample] at h1
  simp at h1
  exact absurd h1 (not_le.mpr hc)

/-- The same statement in "ambient family size `Q`" form: an upper bound
`Energy ≤ C * Q` is compatible with `Energy = 0` and `Q > 0`. -/
theorem upperBound_does_not_give_lowerBound (C : ℝ) (hC : 0 ≤ C) (Q : ℝ) (hQ : 0 < Q) :
    ∃ a : Fin 1 → ℂ,
      quadraticEnergy (Finset.univ : Finset (Fin 1)) a ≤ C * Q ∧
      quadraticEnergy (Finset.univ : Finset (Fin 1)) a = 0 := by
  refine ⟨fun _ => 0, ?_, zeroEnergy_counterexample _⟩
  rw [zeroEnergy_counterexample]
  exact mul_nonneg hC hQ.le

end Universal.SafeAlgebra
