/-
# Gate1B / R11 / Frontier / Latest : nonunit stripping and the prime-denominator D2 covariance

Append-only module.  **Exact finite algebra only.**

* §1 **nonunit stripping**: every residue sum splits exactly into its unit part and its nonunit
  part, with no double charge; the two indexing sets are disjoint and cover.
* §2 **prime denominators**: modulo a prime the nonunit residues are exactly `{0}`.
* §3 **D2 nonunit centered covariance at a prime denominator is exactly zero.**  This is a
  theorem, not an estimate: a function which is centered on a one-point class vanishes on that
  class, so every covariance built from it is exactly `0`.
* §4 the general fibrewise form: the centered covariance vanishes exactly on every one-point
  fibre.
-/
import Mathlib

namespace Gate1B.R11.Frontier.Latest

open Finset
open scoped Classical

/-! ## 1. Nonunit stripping -/

section Stripping

variable {R : Type*} [CommRing R] {n : ℕ} [NeZero n]

/-- **Nonunit stripping.**  A complete residue sum is exactly the unit part plus the nonunit
part. -/
theorem sum_units_add_nonunits (F : ZMod n → R) :
    ∑ v : ZMod n, F v
      = ∑ v ∈ (univ : Finset (ZMod n)).filter (fun v => IsUnit v), F v
        + ∑ v ∈ (univ : Finset (ZMod n)).filter (fun v => ¬ IsUnit v), F v :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The unit and nonunit strata are disjoint: no residue is charged twice. -/
theorem units_nonunits_disjoint :
    Disjoint ((univ : Finset (ZMod n)).filter (fun v => IsUnit v))
      ((univ : Finset (ZMod n)).filter (fun v => ¬ IsUnit v)) :=
  Finset.disjoint_filter_filter_not _ _ _

end Stripping

/-! ## 2. Prime denominators -/

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- Modulo a prime, the nonunit residues are exactly `{0}`. -/
theorem nonunits_prime_eq_zero :
    (univ : Finset (ZMod p)).filter (fun v => ¬ IsUnit v) = {0} := by
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    by_contra hv
    exact h (IsUnit.mk0 v hv)
  · rintro rfl
    simp

/-- Consequently the nonunit stratum of a prime denominator is a single point. -/
theorem card_nonunits_prime :
    ((univ : Finset (ZMod p)).filter (fun v => ¬ IsUnit v)).card = 1 := by
  rw [nonunits_prime_eq_zero]
  simp

/-! ## 3. The D2 nonunit centered covariance at a prime denominator -/

/-- **Prime-denominator D2 nonunit centered covariance is exactly zero.**  If the D2 numerator
`f` is centered over the nonunit stratum of a prime denominator — a single residue — then it
vanishes there, and hence *every* covariance `∑ f · conj g` over that stratum is exactly `0`,
for every companion `g`. -/
theorem prime_nonunit_centered_covariance_eq_zero (f g : ZMod p → ℂ)
    (hcent : ∑ v ∈ (univ : Finset (ZMod p)).filter (fun v => ¬ IsUnit v), f v = 0) :
    ∑ v ∈ (univ : Finset (ZMod p)).filter (fun v => ¬ IsUnit v),
      f v * (starRingEnd ℂ) (g v) = 0 := by
  rw [nonunits_prime_eq_zero] at hcent ⊢
  have hf0 : f 0 = 0 := by simpa using hcent
  simp [hf0]

end Prime

/-! ## 4. The general one-point fibre form -/

/-- The exact fibrewise statement behind §3: on any one-point fibre a centered function has zero
covariance against every companion. -/
theorem centered_covariance_eq_zero_of_card_one {α : Type*} {S : Finset α} (hS : S.card = 1)
    (f g : α → ℂ) (hcent : ∑ v ∈ S, f v = 0) :
    ∑ v ∈ S, f v * (starRingEnd ℂ) (g v) = 0 := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
  have hf0 : f a = 0 := by simpa using hcent
  simp [hf0]

end Gate1B.R11.Frontier.Latest
