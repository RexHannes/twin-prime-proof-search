/-
# UniversalV8 Module I — no-free-gain countermodels

Finite, explicit guards against two narrative errors:

* "each local packet is a contraction, therefore the family is Bessel";
* "the coefficients contain signs, therefore there is cancellation".

Both are FALSE, and these theorems are the counterexamples.
-/
import UniversalV8.BlockGram
import UniversalV8.BoundedVariation

open Finset

namespace UniversalV8

/-- **No free family.**  Take `N` identical norm-one packets (the identity of `ℂ`) and the
all-ones input.  Each local operator is a contraction and the input energy is `N`, but the
synthesis has squared norm `N²`.

Hence uniform local bounds do NOT imply a family Bessel bound: in
`normalizedSynthesisBound` the congestion `η` must be at least `N`. -/
theorem identical_packets_have_family_congestion (N : ℕ) :
    (∀ _γ : Fin N, ‖(ContinuousLinearMap.id ℂ ℂ)‖ ≤ 1) ∧
      ‖synthesis (fun _ : Fin N => ContinuousLinearMap.id ℂ ℂ) (fun _ => (1 : ℂ))‖ ^ 2
        = (N : ℝ) ^ 2 ∧
      ∑ _γ : Fin N, ‖(1 : ℂ)‖ ^ 2 = (N : ℝ) := by
  refine ⟨fun _ => ?_, ?_, by simp⟩
  · simp [ContinuousLinearMap.norm_id_le]
  · simp [synthesis]

/-- The gap in the previous theorem is genuine for `N ≥ 2`: the family square strictly
exceeds the sum of the local squares. -/
theorem identical_packets_gap (N : ℕ) (hN : 2 ≤ N) :
    ∑ _γ : Fin N, ‖(1 : ℂ)‖ ^ 2
      < ‖synthesis (fun _ : Fin N => ContinuousLinearMap.id ℂ ℂ) (fun _ => (1 : ℂ))‖ ^ 2 := by
  obtain ⟨-, h2, h3⟩ := identical_packets_have_family_congestion N
  rw [h2, h3]
  have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith

/-- **No free sign.**  Opposite signs in the coefficients do not force cancellation: with
`z = (1, -1)` and `v = (1, -1)` the signed sum is `2`, i.e. the signs reinforce. -/
theorem signs_do_not_force_cancellation :
    ∑ i : Fin 2, (![1, -1] : Fin 2 → ℝ) i * (![1, -1] : Fin 2 → ℝ) i = 2 := by
  norm_num [Fin.sum_univ_succ]

/-- The same guard in the Hilbert-space normalisation used by the diagonal-baseline
module: a signed coefficient vector attains the *maximal* possible Gram square. -/
theorem signed_family_can_attain_maximum :
    ‖∑ i : Fin 2, (![1, -1] : Fin 2 → ℂ) i • (![1, -1] : Fin 2 → ℂ) i‖ ^ 2
      = ∑ i : Fin 2, ‖(![1, -1] : Fin 2 → ℂ) i‖ ^ 2 * ‖(![1, -1] : Fin 2 → ℂ) i‖ ^ 2
        + 2 := by
  norm_num [Fin.sum_univ_succ]

/-- **The partial-sum bound in the backend-dual norm theorem is load-bearing.**  With
`a ≡ 1` (unbounded partial sums) and `w ≡ 1` (bounded by `1`, zero variation) the weighted
sum is `N` while the dBV factor is `1`. -/
theorem dBV_needs_partialSum_bound (N : ℕ) :
    ‖∑ _k ∈ Finset.Ico 0 N, (1 : ℂ) * (1 : ℂ)‖ = (N : ℝ) ∧
      ‖(1 : ℂ)‖ + variation 0 (N - 1) (fun _ => (1 : ℂ)) = 1 := by
  constructor
  · simp
  · simp [variation]

end UniversalV8
