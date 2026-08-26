/-
# NANC Gate 1A v9 — the (N, Delta) linear map and its ℓ² pushforward

For fixed `q1, q2, ell1, ell2` define

    detMap (h1,h2) = (h1*q2 − h2*q1, ell1*h1 − ell2*h2).

* `detMap_injective_of_crossDet_ne_zero` — injective over ℤ² as soon as
  `q1*ell1 − q2*ell2 ≠ 0`.
* `injectivePushforward_l2` — for an injective map on a finite support, the
  ℓ²-mass of the pushforward equals the ℓ²-mass of the source.
* `nDelta_pushforward_l2` — the specialisation to `detMap`.

**FIREWALL.**  This is the finite-safe version of the `(N,Delta)` energy step.
No `H`-bound and no analytic input is inserted: any such bound must enter as an
explicit theorem hypothesis elsewhere.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

open Finset

/-- The `(N, Delta)` map on `ℤ²` for frozen `q1, q2, ell1, ell2`. -/
def detMap (q1 q2 ell1 ell2 : ℤ) (h : ℤ × ℤ) : ℤ × ℤ :=
  (h.1 * q2 - h.2 * q1, ell1 * h.1 - ell2 * h.2)

/-- **Injectivity of the determinant map.** -/
theorem detMap_injective_of_crossDet_ne_zero {q1 q2 ell1 ell2 : ℤ}
    (hdet : q1 * ell1 - q2 * ell2 ≠ 0) :
    Function.Injective (detMap q1 q2 ell1 ell2) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [detMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : (a1 - b1) * q2 - (a2 - b2) * q1 = 0 := by linarith
  have e2 : ell1 * (a1 - b1) - ell2 * (a2 - b2) = 0 := by linarith
  have hu1 : (q1 * ell1 - q2 * ell2) * (a1 - b1) = 0 := by linear_combination q1 * e2 - ell2 * e1
  have hu2 : (q1 * ell1 - q2 * ell2) * (a2 - b2) = 0 := by linear_combination q2 * e2 - ell1 * e1
  have h1' : a1 = b1 := by
    have := (mul_eq_zero.mp hu1).resolve_left hdet
    linarith
  have h2' : a2 = b2 := by
    have := (mul_eq_zero.mp hu2).resolve_left hdet
    linarith
  simp [h1', h2']

/-- **Injective pushforward preserves ℓ²-mass.**  For a map injective on the
finite support `S`, each fibre over the image is a single point, so the squared
masses agree term by term. -/
theorem injectivePushforward_l2 {ι kappa : Type*} [DecidableEq ι] [DecidableEq kappa]
    (S : Finset ι) (w : ι → ℂ) (f : ι → kappa) (hf : Set.InjOn f S) :
    ∑ t ∈ S.image f, ‖∑ x ∈ S.filter (fun x => f x = t), w x‖ ^ 2
      = ∑ x ∈ S, ‖w x‖ ^ 2 := by
  rw [Finset.sum_image (fun a ha b hb hab => hf ha hb hab)]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hfib : S.filter (fun y => f y = f x) = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, hfy⟩; exact hf hy hx hfy
    · rintro rfl; exact ⟨hx, rfl⟩
  rw [hfib, Finset.sum_singleton]

/-- **`(N,Delta)` pushforward.**  Under the nonvanishing cross determinant, the
ℓ²-mass of the `(N,Delta)`-indexed sums equals the ℓ²-mass of the `(h1,h2)`
weights. -/
theorem nDelta_pushforward_l2 {q1 q2 ell1 ell2 : ℤ}
    (hdet : q1 * ell1 - q2 * ell2 ≠ 0)
    (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ → ℂ) :
    ∑ t ∈ S.image (detMap q1 q2 ell1 ell2),
        ‖∑ x ∈ S.filter (fun x => detMap q1 q2 ell1 ell2 x = t), w x‖ ^ 2
      = ∑ x ∈ S, ‖w x‖ ^ 2 :=
  injectivePushforward_l2 S w _
    ((detMap_injective_of_crossDet_ne_zero hdet).injOn)

end TwinPrimeProject.NANC.Gate1A.V9
