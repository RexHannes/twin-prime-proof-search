/-
# Gate1B / R11 : the SL₂ Bruhat factorisation of the matched determinant matrix

Let `M = !![A, k; d, B]` have determinant `A·B − k·d = −2` (the matched determinant at the
fixed shift `2`).  Over a ring in which `−2` and `d` are invertible — for instance `ZMod c`
with `c` odd and `d` a unit — put `λ = (−2)⁻¹` and

```
g = diag(λ, 1) · M = !![λA, λk; d, B].
```

We kernel-prove:

* `det g = 1`;
* the Bruhat factorisation, **exactly as claimed**, with no sign or order correction:

```
g = U(λ A d⁻¹) · D(d⁻¹) · S · U(B d⁻¹),
```

where `U(x) = !![1,x;0,1]`, `D(u) = !![u,0;0,u⁻¹]`, `S = !![0,−1;1,0]`.

The statement is proved over an arbitrary commutative ring with the inverses supplied as
explicit data (`lam * (-2) = 1`, `d * dinv = 1`), and then instantiated in `ZMod c`.
-/
import Mathlib

namespace Gate1B.R11

open Matrix

variable {R : Type*} [CommRing R]

/-! ## 1. The Bruhat generators -/

/-- The upper unipotent generator `U(x) = !![1,x;0,1]`. -/
def bruhatU (x : R) : Matrix (Fin 2) (Fin 2) R := !![1, x; 0, 1]

/-- The diagonal generator `D(u) = !![u,0;0,u⁻¹]`, with the inverse supplied explicitly. -/
def bruhatD (u uinv : R) : Matrix (Fin 2) (Fin 2) R := !![u, 0; 0, uinv]

/-- The Weyl generator `S = !![0,−1;1,0]`. -/
def bruhatS : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]

/-- The matched determinant matrix `M = !![A,k;d,B]`. -/
def detMatrix (A k d B : R) : Matrix (Fin 2) (Fin 2) R := !![A, k; d, B]

/-- The rescaled matrix `g = diag(λ,1) · M`. -/
def rescaled (lam A k d B : R) : Matrix (Fin 2) (Fin 2) R := !![lam * A, lam * k; d, B]

/-! ## 2. `g = diag(λ,1)·M` and `det g = 1` -/

/-- `g` really is `diag(λ,1)·M`. -/
theorem rescaled_eq_diag_mul (lam A k d B : R) :
    rescaled lam A k d B = bruhatD lam 1 * detMatrix A k d B := by
  simp only [rescaled, bruhatD, detMatrix, Matrix.mul_fin_two]
  norm_num

/-- `det M = A·B − k·d`. -/
theorem det_detMatrix (A k d B : R) : (detMatrix A k d B).det = A * B - k * d := by
  simp [detMatrix, Matrix.det_fin_two_of]

/-- **`det g = 1`.**  With `A·B − k·d = −2` and `λ·(−2) = 1`. -/
theorem det_rescaled_eq_one {A B k d lam : R} (hdet : A * B - k * d = -2)
    (hlam : lam * (-2) = 1) : (rescaled lam A k d B).det = 1 := by
  simp only [rescaled, Matrix.det_fin_two_of]
  linear_combination lam * hdet + hlam

/-! ## 3. The Bruhat factorisation -/

/-- **SL₂ Bruhat factorisation (kernel-proved, as claimed).**

`!![λA, λk; d, B] = U(λ A d⁻¹) · D(d⁻¹) · S · U(B d⁻¹)`,

given `A·B − k·d = −2`, `λ·(−2) = 1` and `d·d⁻¹ = 1`.  The matrix multiplication confirms
the claimed order and signs exactly; no repair was needed. -/
theorem bruhat_factorisation {A B k d lam dinv : R} (hdet : A * B - k * d = -2)
    (hlam : lam * (-2) = 1) (hdinv : d * dinv = 1) :
    rescaled lam A k d B
      = bruhatU (lam * A * dinv) * bruhatD dinv d * bruhatS * bruhatU (B * dinv) := by
  have hkey : lam * A * B = lam * k * d + 1 := by linear_combination lam * hdet + hlam
  simp only [rescaled, bruhatU, bruhatD, bruhatS, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-(lam * A)) * hdinv
  · linear_combination (-(d * dinv ^ 2)) * hkey + (-(lam * k * (1 + d * dinv)) - dinv) * hdinv
  · linear_combination (-B) * hdinv

/-! ## 4. Instantiation modulo an odd `c` -/

/-- For odd `c`, the element `-2` is invertible in `ZMod c`. -/
theorem exists_inv_neg_two {c : ℕ} (hc : Odd c) : ∃ lam : ZMod c, lam * (-2 : ZMod c) = 1 := by
  have hcop : Nat.Coprime 2 c := by
    unfold Nat.Coprime
    rw [Nat.gcd_comm, Nat.gcd_rec]
    simpa using hc
  have h2 : IsUnit ((2 : ℕ) : ZMod c) := (ZMod.isUnit_iff_coprime 2 c).2 hcop
  have hneg : IsUnit (-2 : ZMod c) := by
    have : ((2 : ℕ) : ZMod c) = (2 : ZMod c) := by push_cast; ring
    rw [this] at h2
    exact h2.neg
  obtain ⟨w, hw⟩ := hneg
  exact ⟨(w⁻¹ : (ZMod c)ˣ), by rw [← hw]; simp⟩

/-- **Bruhat factorisation modulo an odd `c`.**  If `c` is odd and `d` is invertible modulo
`c`, then the matched determinant matrix rescaled by `λ = (−2)⁻¹` lies in `SL₂` modulo `c`
and factors as claimed. -/
theorem bruhat_factorisation_zmod {c : ℕ} (hc : Odd c) {A B k d : ZMod c}
    (hdet : A * B - k * d = -2) (hd : IsUnit d) :
    ∃ lam dinv : ZMod c,
      lam * (-2 : ZMod c) = 1 ∧ d * dinv = 1 ∧
        (rescaled lam A k d B).det = 1 ∧
        rescaled lam A k d B
          = bruhatU (lam * A * dinv) * bruhatD dinv d * bruhatS * bruhatU (B * dinv) := by
  obtain ⟨lam, hlam⟩ := exists_inv_neg_two hc
  obtain ⟨w, hw⟩ := hd
  refine ⟨lam, ((w⁻¹ : (ZMod c)ˣ) : ZMod c), hlam, ?_, ?_, ?_⟩
  · rw [← hw]; simp
  · exact det_rescaled_eq_one hdet hlam
  · exact bruhat_factorisation hdet hlam (by rw [← hw]; simp)

end Gate1B.R11
