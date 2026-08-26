/-
# Gate 1B v8.3 — H7 / H8 character packet algebra

**Status: PROVED_ALGEBRAIC.**

Abstract packet shapes, as exact finite factorisations of a *labelled tensor*
source coefficient:

* H7 packet — seven source transforms × one model transform × one
  dual-frequency transform;
* H8 packet — eight source transforms × one dual-frequency transform.

Only the factorisation is proved.  **No transform is asserted to be small**, no
Kloosterman/Poisson estimate is used, and the H7/H8 analytic status stays OPEN.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteMultiplicativeCharacters

namespace Gate1B.SafeAlgebra

open Finset

variable {A : Type*} [Fintype A]

/-- Exact factorisation of a labelled tensor sum. -/
theorem labelled_tensor_factor {n : ℕ} (T : Fin n → A → ℂ) :
    ∑ x : Fin n → A, ∏ i, T i (x i) = ∏ i, ∑ a : A, T i a := by
  classical
  rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ]

/-- The H7 packet: seven source transforms, one model transform, one
dual-frequency transform. -/
noncomputable def h7Packet (src : Fin 7 → A → ℂ) (model dual : A → ℂ) : ℂ :=
  ∑ xs : Fin 7 → A, ∑ y : A, ∑ z : A, (∏ i, src i (xs i)) * model y * dual z

/-- **H7 packet factorisation.** -/
theorem h7_characterPacket_factor (src : Fin 7 → A → ℂ) (model dual : A → ℂ) :
    h7Packet src model dual
      = (∏ i, ∑ a : A, src i a) * (∑ a : A, model a) * (∑ a : A, dual a) := by
  classical
  unfold h7Packet
  have hz : ∀ (xs : Fin 7 → A) (y : A),
      ∑ z : A, (∏ i, src i (xs i)) * model y * dual z
        = (∏ i, src i (xs i)) * model y * ∑ z : A, dual z := by
    intro xs y; rw [Finset.mul_sum]
  simp_rw [hz]
  have hy : ∀ xs : Fin 7 → A,
      ∑ y : A, (∏ i, src i (xs i)) * model y * ∑ z : A, dual z
        = (∏ i, src i (xs i)) * (∑ y : A, model y) * ∑ z : A, dual z := by
    intro xs
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [hy]
  rw [← Finset.sum_mul, ← Finset.sum_mul, labelled_tensor_factor]

/-- The H8 packet: eight source transforms and one dual-frequency transform. -/
noncomputable def h8Packet (src : Fin 8 → A → ℂ) (dual : A → ℂ) : ℂ :=
  ∑ xs : Fin 8 → A, ∑ z : A, (∏ i, src i (xs i)) * dual z

/-- **H8 packet factorisation.** -/
theorem h8_characterPacket_factor (src : Fin 8 → A → ℂ) (dual : A → ℂ) :
    h8Packet src dual = (∏ i, ∑ a : A, src i a) * (∑ a : A, dual a) := by
  classical
  unfold h8Packet
  have hz : ∀ xs : Fin 8 → A,
      ∑ z : A, (∏ i, src i (xs i)) * dual z = (∏ i, src i (xs i)) * ∑ z : A, dual z := by
    intro xs; rw [Finset.mul_sum]
  simp_rw [hz]
  rw [← Finset.sum_mul, labelled_tensor_factor]

/-- The H7 packet has nine labelled factors in total. -/
theorem h7Packet_factor_count : 7 + 1 + 1 = 9 := by norm_num

/-- The H8 packet has nine labelled factors in total. -/
theorem h8Packet_factor_count : 8 + 1 = 9 := by norm_num

end Gate1B.SafeAlgebra
