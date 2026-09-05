/-
# Gate1B / Hilbert-HMRD : operator stability under tensoring with a Hilbert space

For a finite scalar matrix `T : J → I → ℂ` and a finite-dimensional complex inner-product
space `H`, the `ℓ²`-operator bound of `T` transfers verbatim to `T ⊗ id_H` acting on
`H`-valued vectors, and conversely (as soon as `H ≠ 0`).  Hence the two best constants
coincide: `‖T ⊗ id_H‖ = ‖T‖`.

The direction actually needed downstream is the transfer `scalar ⇒ Hilbert-valued`; the
converse is obtained by testing on a fixed unit vector of `H`.

Purely finite linear algebra; no analytic input.
-/
import Mathlib

namespace Gate1B.HilbertHMRD

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The scalar `ℓ²` operator bound `‖T x‖₂ ≤ C ‖x‖₂`, in squared form. -/
def ScalarL2Bound (T : J → I → ℂ) (C : ℝ) : Prop :=
  ∀ x : I → ℂ, ∑ j, ‖∑ i, T j i * x i‖ ^ 2 ≤ C ^ 2 * ∑ i, ‖x i‖ ^ 2

/-- The `H`-valued (`T ⊗ id_H`) operator bound, in squared form. -/
def HilbertL2Bound (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : J → I → ℂ) (C : ℝ) : Prop :=
  ∀ X : I → H, ∑ j, ‖∑ i, T j i • X i‖ ^ 2 ≤ C ^ 2 * ∑ i, ‖X i‖ ^ 2

/-- Parseval in an orthonormal basis of a finite-dimensional space. -/
theorem norm_sq_eq_sum_repr [FiniteDimensional ℂ H] (v : H) :
    ‖v‖ ^ 2 = ∑ k, ‖(stdOrthonormalBasis ℂ H).repr v k‖ ^ 2 := by
  rw [← (stdOrthonormalBasis ℂ H).repr.norm_map v, EuclideanSpace.norm_eq,
    Real.sq_sqrt (by positivity)]

/-- **Tensor stability, the direction used in applications.**  A scalar `ℓ²` bound for `T`
transfers to `H`-valued vectors with the *same* constant. -/
theorem hilbertL2Bound_of_scalarL2Bound [FiniteDimensional ℂ H] (T : J → I → ℂ) (C : ℝ)
    (hT : ScalarL2Bound T C) : HilbertL2Bound H T C := by
  intro X
  set b := stdOrthonormalBasis ℂ H with hb
  have hrepr : ∀ j, ‖∑ i, T j i • X i‖ ^ 2 = ∑ k, ‖∑ i, T j i * b.repr (X i) k‖ ^ 2 := by
    intro j
    rw [norm_sq_eq_sum_repr]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [map_sum]
    simp [hb]
  have hX : ∀ i, ‖X i‖ ^ 2 = ∑ k, ‖b.repr (X i) k‖ ^ 2 := fun i => norm_sq_eq_sum_repr (X i)
  calc ∑ j, ‖∑ i, T j i • X i‖ ^ 2
      = ∑ j, ∑ k, ‖∑ i, T j i * b.repr (X i) k‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => hrepr j
    _ = ∑ k, ∑ j, ‖∑ i, T j i * b.repr (X i) k‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ k, C ^ 2 * ∑ i, ‖b.repr (X i) k‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => hT (fun i => b.repr (X i) k)
    _ = C ^ 2 * ∑ i, ∑ k, ‖b.repr (X i) k‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = C ^ 2 * ∑ i, ‖X i‖ ^ 2 := by
        rw [Finset.sum_congr rfl fun i _ => (hX i).symm]

/-- **The converse direction.**  Testing on a fixed unit vector of `H` recovers the scalar
bound from the `H`-valued one. -/
theorem scalarL2Bound_of_hilbertL2Bound (T : J → I → ℂ) (C : ℝ) (e : H) (he : ‖e‖ = 1)
    (hH : HilbertL2Bound H T C) : ScalarL2Bound T C := by
  intro x
  have hspec := hH (fun i => x i • e)
  have hj : ∀ j, ‖∑ i, T j i • (x i • e)‖ ^ 2 = ‖∑ i, T j i * x i‖ ^ 2 := by
    intro j
    have : ∑ i, T j i • (x i • e) = (∑ i, T j i * x i) • e := by
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
    rw [this, norm_smul, he, mul_one]
  have hi : ∀ i, ‖x i • e‖ ^ 2 = ‖x i‖ ^ 2 := by
    intro i
    rw [norm_smul, he, mul_one]
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_congr rfl fun i _ => hi i] at hspec
  exact hspec

/-- **`‖T ⊗ id_H‖ = ‖T‖` (operator stability).**  For a nonzero finite-dimensional `H`, a
constant bounds the `H`-valued operator exactly when it bounds the scalar one; hence the two
operators have the same set of admissible bounds, and therefore the same operator norm. -/
theorem operatorNorm_tensor_identity_hilbert [FiniteDimensional ℂ H] (T : J → I → ℂ) (C : ℝ)
    (e : H) (he : ‖e‖ = 1) : HilbertL2Bound H T C ↔ ScalarL2Bound T C :=
  ⟨fun h => scalarL2Bound_of_hilbertL2Bound T C e he h,
    fun h => hilbertL2Bound_of_scalarL2Bound T C h⟩

end

end Gate1B.HilbertHMRD
