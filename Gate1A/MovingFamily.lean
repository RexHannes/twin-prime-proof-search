/-
# Gate-1A: the moving-family energy inequality (Section 9)

Hilbert-valued (complex), finite, kernel-checked.

Given a finite family `P` of "moving moduli", a finite index set `X`, a
Hilbert-space-valued vector `v p x`, and for each `p` a local fibre map
`π p : X → Ξ p`, the collision energy

```
E = ∑_p ∑_ξ ‖ ∑_{x : π p x = ξ} v p x ‖²
```

is bounded by the diagonal mass plus `D · (∑_x A x)²`, where `A` is any
pointwise envelope of the amplitudes and `D` bounds the number of family
members at which a fixed distinct pair collides.

The hypothesis `0 ≤ D` is genuinely needed (a singleton `X` gives no
off-diagonal pairs, so a negative `D` would falsify the statement).
-/
import Mathlib

namespace Gate1A

open Finset

section MovingFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Expansion/estimate for the square norm of a finite sum in an inner product
space: diagonal mass plus the absolute off-diagonal. -/
theorem norm_sum_sq_le_diag_add_offdiag {X : Type*} [DecidableEq X]
    (s : Finset X) (f : X → E) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤
      (∑ x ∈ s, ‖f x‖ ^ 2) + ∑ x ∈ s, ∑ y ∈ s.erase x, ‖f x‖ * ‖f y‖ := by
  have hexp : ‖∑ x ∈ s, f x‖ ^ 2
      = ∑ x ∈ s, ∑ y ∈ s, RCLike.re (inner ℂ (f x) (f y)) := by
    rw [← @inner_self_eq_norm_sq ℂ, sum_inner]
    simp_rw [inner_sum, map_sum]
  rw [hexp, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro x hx
  rw [← Finset.add_sum_erase _ _ hx]
  refine add_le_add (le_of_eq (inner_self_eq_norm_sq (𝕜 := ℂ) (f x))) ?_
  refine Finset.sum_le_sum fun y _ => ?_
  exact le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)

variable {P X : Type*} [Fintype P] [Fintype X] [DecidableEq X]
variable {Xi : P → Type*} [∀ p, DecidableEq (Xi p)] [∀ p, Fintype (Xi p)]

/-- The collision energy of a moving family. -/
noncomputable def collisionEnergy (v : ∀ _ : P, X → E) (pr : ∀ p, X → Xi p) : ℝ :=
  ∑ p : P, ∑ xi : Xi p, ‖∑ x ∈ univ.filter (fun x => pr p x = xi), v p x‖ ^ 2

omit [Fintype P] in
/-- One-`p` slice of the collision energy. -/
theorem fibre_energy_le (p : P) (v : ∀ _ : P, X → E) (pr : ∀ p, X → Xi p)
    (A : X → ℝ) (hA : ∀ q x, ‖v q x‖ ≤ A x) (hA0 : ∀ x, 0 ≤ A x) :
    (∑ xi : Xi p, ‖∑ x ∈ univ.filter (fun x => pr p x = xi), v p x‖ ^ 2) ≤
      (∑ x : X, ‖v p x‖ ^ 2) +
        ∑ x : X, ∑ y ∈ univ.erase x,
          (if pr p y = pr p x then A x * A y else 0) := by
  classical
  have step1 : (∑ xi : Xi p, ‖∑ x ∈ univ.filter (fun x => pr p x = xi), v p x‖ ^ 2)
      ≤ ∑ xi : Xi p,
          ((∑ x ∈ univ.filter (fun x => pr p x = xi), ‖v p x‖ ^ 2) +
            ∑ x ∈ univ.filter (fun x => pr p x = xi),
              ∑ y ∈ (univ.filter (fun x => pr p x = xi)).erase x, ‖v p x‖ * ‖v p y‖) :=
    Finset.sum_le_sum fun xi _ => norm_sum_sq_le_diag_add_offdiag _ _
  refine step1.trans ?_
  rw [Finset.sum_add_distrib]
  gcongr
  · exact le_of_eq (Finset.sum_fiberwise univ (fun x => pr p x) (fun x => ‖v p x‖ ^ 2))
  · rw [← Finset.sum_fiberwise univ (fun x => pr p x)
        (fun x => ∑ y ∈ univ.erase x, (if pr p y = pr p x then A x * A y else 0))]
    refine Finset.sum_le_sum fun xi _ => Finset.sum_le_sum fun x hx => ?_
    have hxi : pr p x = xi := (Finset.mem_filter.mp hx).2
    subst hxi
    have hset : (univ.filter (fun y => pr p y = pr p x)).erase x
        = (univ.erase x).filter (fun y => pr p y = pr p x) := by
      ext y
      simp [Finset.mem_erase, Finset.mem_filter, and_comm]
    rw [hset, Finset.sum_filter]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases h : pr p y = pr p x
    · simp only [h, if_true]
      exact mul_le_mul (hA p x) (hA p y) (norm_nonneg _) (hA0 x)
    · simp [h]

/-- **Moving-family energy inequality.**

If every distinct pair `x ≠ y` collides for at most `D` members of the family,
then the total collision energy is bounded by the diagonal mass plus
`D · (∑ A)²`. -/
theorem moving_family_energy_le
    (v : ∀ _ : P, X → E) (pr : ∀ p, X → Xi p) (A : X → ℝ) (D : ℝ)
    (hA : ∀ p x, ‖v p x‖ ≤ A x) (hA0 : ∀ x, 0 ≤ A x) (hD0 : 0 ≤ D)
    (hD : ∀ x y : X, x ≠ y →
      ((univ.filter (fun p : P => pr p x = pr p y)).card : ℝ) ≤ D) :
    collisionEnergy v pr ≤
      (∑ p : P, ∑ x : X, ‖v p x‖ ^ 2) + D * (∑ x : X, A x) ^ 2 := by
  classical
  have step : collisionEnergy v pr ≤
      (∑ p : P, ∑ x : X, ‖v p x‖ ^ 2) +
        ∑ p : P, ∑ x : X, ∑ y ∈ univ.erase x,
          (if pr p y = pr p x then A x * A y else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => fibre_energy_le p v pr A hA hA0
  refine step.trans ?_
  gcongr
  rw [Finset.sum_comm]
  calc
    ∑ x : X, ∑ p : P, ∑ y ∈ univ.erase x,
        (if pr p y = pr p x then A x * A y else 0)
        = ∑ x : X, ∑ y ∈ univ.erase x,
            ((univ.filter (fun p : P => pr p y = pr p x)).card : ℝ) * (A x * A y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x : X, ∑ y ∈ univ.erase x, D * (A x * A y) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y hy => ?_
          have hne : y ≠ x := (Finset.mem_erase.mp hy).1
          exact mul_le_mul_of_nonneg_right (hD y x hne)
            (mul_nonneg (hA0 x) (hA0 y))
    _ ≤ ∑ x : X, ∑ y : X, D * (A x * A y) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) fun y _ _ => ?_
          exact mul_nonneg hD0 (mul_nonneg (hA0 x) (hA0 y))
    _ = D * (∑ x : X, A x) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]

/-- `T_abs`: the conservative ℓ¹ ("absolute") scale of a moving family. -/
noncomputable def TAbs (v : ∀ _ : P, X → E) : ℝ := ∑ p : P, (∑ x : X, ‖v p x‖) ^ 2

/-- The off-diagonal coherence numerator of a moving family relative to an
envelope `A`. -/
noncomputable def coherenceNumerator (A : X → ℝ) : ℝ := (∑ x : X, A x) ^ 2

/-- The off-diagonal part of the collision energy is at most
`D · coherenceNumerator`. -/
theorem offdiag_energy_le_D_mul_coherence
    (v : ∀ _ : P, X → E) (pr : ∀ p, X → Xi p) (A : X → ℝ) (D : ℝ)
    (hA : ∀ p x, ‖v p x‖ ≤ A x) (hA0 : ∀ x, 0 ≤ A x) (hD0 : 0 ≤ D)
    (hD : ∀ x y : X, x ≠ y →
      ((univ.filter (fun p : P => pr p x = pr p y)).card : ℝ) ≤ D) :
    collisionEnergy v pr - (∑ p : P, ∑ x : X, ‖v p x‖ ^ 2)
      ≤ D * coherenceNumerator A := by
  have := moving_family_energy_le v pr A D hA hA0 hD0 hD
  simp only [coherenceNumerator]
  linarith

end MovingFamily

end Gate1A
