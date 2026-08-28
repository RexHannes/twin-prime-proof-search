/-
# Gate 1B v8.4 — the `μ(c₀)` simplification of the primitive projector

**Status: PROVED_ALGEBRAIC (given the projector identity of
`PrimitiveCharacterProjector.lean`).**

For squarefree `c₀` and `d ∣ c₀`:  `μ(c₀) μ(c₀/d) = μ(d)`.

Hence the `μ`-weighted projector simplifies:

  `(μ(c₀)/c₀) ∑_{χ primitive mod c₀} χ(A) = (1/c₀) ∑_{d ∣ c₀, d ∣ A-1} μ(d) φ(d)`.
-/
import Mathlib
import Gate1B.SafeAlgebra.PrimitiveCharacterProjector

namespace Gate1B.SafeAlgebra

open scoped ArithmeticFunction.Moebius
open ArithmeticFunction Finset

/-- **Sign identity.**  `μ(c₀) μ(c₀/d) = μ(d)` for squarefree `c₀` and
`d ∣ c₀`. -/
theorem mu_mul_quotient_mu {c0 d : ℕ} (hc0 : Squarefree c0) (hd : d ∣ c0) :
    μ c0 * μ (c0 / d) = μ d := by
  obtain ⟨k, hk⟩ := hd
  have hsq : Squarefree (d * k) := hk ▸ hc0
  have hcop : Nat.Coprime d k := (Nat.squarefree_mul_iff.1 hsq).1
  have hd0 : d ≠ 0 := by rintro rfl; simp at hsq
  have hquot : c0 / d = k := by rw [hk, Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hd0)]
  have hk2 : Squarefree k := (Nat.squarefree_mul_iff.1 hsq).2.2
  rw [hquot, hk, isMultiplicative_moebius.map_mul_of_coprime hcop]
  have hsqk : μ k * μ k = 1 := by
    have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hk2
    nlinarith [h]
  calc μ d * μ k * μ k = μ d * (μ k * μ k) := by ring
    _ = μ d := by rw [hsqk, mul_one]

open scoped Classical in
/-- **`μ`-weighted primitive projector.**  For squarefree `c₀`,

  `(μ(c₀)/c₀) · primSum c₀ = (1/c₀) ∑_{d ∣ c₀, d ∣ A-1} μ(d) φ(d)`. -/
theorem mu_weighted_primitiveProjector (A : ℤ) (primSum : ℕ → ℂ)
    (hdecomp : ∀ n : ℕ, n > 0 → ∑ d ∈ n.divisors, primSum d
      = if (n : ℤ) ∣ A - 1 then ((n.totient : ℕ) : ℂ) else 0)
    {c0 : ℕ} (hc0 : 0 < c0) (hsf : Squarefree c0) :
    ((μ c0 : ℂ) / (c0 : ℂ)) * primSum c0
      = (1 / (c0 : ℂ)) * ∑ d ∈ Finset.filter (fun d : ℕ => (d : ℤ) ∣ A - 1) c0.divisors,
          (μ d : ℂ) * ((d.totient : ℕ) : ℂ) := by
  rw [primitiveChar_sum_squarefree A primSum hdecomp hc0, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ c0 := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
  have hmu : ((μ c0 * μ (c0 / d) : ℤ) : ℂ) = ((μ d : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (mu_mul_quotient_mu hsf hdvd)
  push_cast at hmu ⊢
  rw [← hmu]
  ring

end Gate1B.SafeAlgebra
