/-
# Gate 1B v8.3 — generic shell regroup (exact integer arithmetic)

**Status: PROVED_ALGEBRAIC.**

A generic determinant shell with `m` model coordinates,

    C * x₁ * … * x_m - q * ℓ = -2,

is reassociated by selecting two coordinates `x, y` for completion and
absorbing the remaining `m - 2` model coordinates into

    B = C * ∏ (other model coordinates).

The reassociation is an exact equivalence of integer equations.  No analytic
weight, no Kloosterman estimate, no completion bound is asserted here.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- **Generic two-model shell regroup.**  Selecting two model coordinates
`x ≠ y` from the model index set `s` and absorbing the rest into
`B = C * ∏_{i ∈ s \ {x,y}} f i` is an exact equivalence of shells. -/
theorem shell_regroup_twoModels {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ)
    (x y : ι) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (C q ell : ℤ) :
    (C * ∏ i ∈ s, f i) - q * ell = -2 ↔
      ((C * ∏ i ∈ (s.erase x).erase y, f i) * f x * f y) - q * ell = -2 := by
  have hy' : y ∈ s.erase x := Finset.mem_erase.2 ⟨(Ne.symm hxy), hy⟩
  have h1 : f y * ∏ i ∈ (s.erase x).erase y, f i = ∏ i ∈ s.erase x, f i :=
    Finset.mul_prod_erase _ _ hy'
  have h2 : f x * ∏ i ∈ s.erase x, f i = ∏ i ∈ s, f i :=
    Finset.mul_prod_erase _ _ hx
  have hprod : ∏ i ∈ s, f i = f x * f y * ∏ i ∈ (s.erase x).erase y, f i := by
    rw [← h2, ← h1]; ring
  rw [hprod]
  constructor <;> intro h <;> linear_combination h

/-- Order five: four model coordinates, two absorbed into `B`. -/
theorem shell_regroup_order5 (C x1 x2 x3 x4 q ell : ℤ) :
    C * x1 * x2 * x3 * x4 - q * ell = -2 ↔ (C * x1 * x2) * x3 * x4 - q * ell = -2 := by
  constructor <;> intro h <;> linear_combination h

/-- Order six: three model coordinates, one absorbed into `B`. -/
theorem shell_regroup_order6 (C x1 x2 x3 q ell : ℤ) :
    C * x1 * x2 * x3 - q * ell = -2 ↔ (C * x1) * x2 * x3 - q * ell = -2 := by
  constructor <;> intro h <;> linear_combination h

/-- Order seven: two model coordinates, none absorbed (`B = C`). -/
theorem shell_regroup_order7 (C x1 x2 q ell : ℤ) :
    C * x1 * x2 - q * ell = -2 ↔ C * x1 * x2 - q * ell = -2 := Iff.rfl

/-- The regrouped coefficient of a shell is itself a legal shell coefficient:
the shell equation only sees the product. -/
theorem shell_regroup_coeff_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ)
    (x y : ι) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (C : ℤ) :
    C * ∏ i ∈ s, f i = (C * ∏ i ∈ (s.erase x).erase y, f i) * f x * f y := by
  have hy' : y ∈ s.erase x := Finset.mem_erase.2 ⟨(Ne.symm hxy), hy⟩
  have h1 : f y * ∏ i ∈ (s.erase x).erase y, f i = ∏ i ∈ s.erase x, f i :=
    Finset.mul_prod_erase _ _ hy'
  have h2 : f x * ∏ i ∈ s.erase x, f i = ∏ i ∈ s, f i :=
    Finset.mul_prod_erase _ _ hx
  rw [← h2, ← h1]; ring

end Gate1B.SafeAlgebra
