/-
# Gate 1B v8.2 — 2-adic finite source router

Elementary congruence arithmetic: if `u` and `v` are odd and `q` is even, the
shell congruence `u v ≡ −2 (mod q)` has no solution.

**This says the physical count is empty.**  It does *not* say `E(q) = 0` for
even `q`; that remains SOURCE OPEN and is recorded as such in the interfaces.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- **Two-adic emptiness modulo 2.**  An odd product is never `≡ −2 (mod 2)`
in the sense that `2 ∤ (u v + 2)`. -/
theorem odd_mul_add_two_not_even {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    ¬ (2 : ℤ) ∣ (u * v + 2) := by
  intro h
  have hodd : Odd (u * v) := hu.mul hv
  have h2 : (2 : ℤ) ∣ u * v := (dvd_add_right (dvd_refl 2)).mp (by simpa [add_comm] using h)
  rcases hodd with ⟨k, hk⟩
  omega

/-- **The physical 2-adic guard.**  With `u`, `v` odd and `q` even, the shell
congruence `u v ≡ −2 (mod q)` is impossible. -/
theorem odd_mul_not_congr_neg_two_mod_even {u v q : ℤ} (hu : Odd u) (hv : Odd v)
    (hq : (2 : ℤ) ∣ q) : ¬ (q ∣ (u * v + 2)) := by
  intro h
  exact odd_mul_add_two_not_even hu hv (dvd_trans hq h)

/-- The same statement in `Int.ModEq` form. -/
theorem odd_mul_not_modEq_neg_two_mod_even {u v q : ℤ} (hu : Odd u) (hv : Odd v)
    (hq : (2 : ℤ) ∣ q) : ¬ (u * v ≡ -2 [ZMOD q]) := by
  intro h
  refine odd_mul_not_congr_neg_two_mod_even hu hv hq ?_
  have hdvd : q ∣ (u * v - (-2)) := Int.ModEq.dvd h.symm
  simpa [sub_neg_eq_add] using hdvd

/-- The guard is about the *count*, not about the expected term: the empty
physical count is compatible with any value of an abstract `E`. -/
theorem emptyCount_does_not_determine_E :
    ∃ E : ℤ → ℂ, (∀ q : ℤ, (2 : ℤ) ∣ q → E q ≠ 0) := by
  exact ⟨fun _ => 1, fun _ _ => one_ne_zero⟩

end Gate1B.SafeAlgebra
