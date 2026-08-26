import Mathlib

/-!
# Gate 0–1 finite bank: the `h = 0` centering cancellation

For a modulus `p` put `ρ_p(n) = 1_{p ∣ n} - 1/p`.  In the generic `p ≠ q`
stratum, the centered joint count against a common smooth weight `W` expands
into four pieces: the joint count, the two singleton counts, and the constant
term.  This file banks

1. the exact finite expansion of the centered bilinear sum
   (`centered_pair_expansion`), which is pure `Finset` algebra;
2. the `h = 0` cancellation (`h_zero_centering_cancellation`): once the four
   zero-frequency masses take their main-term values
   `Ŵ(0)/(pq)`, `Ŵ(0)/p`, `Ŵ(0)/q`, `Ŵ(0)`, the total is exactly `0`.

This is finite centering algebra only.  No nonzero-frequency estimate, and no
statement about the actual size of the error in replacing a count by its main
term, is proved or assumed here.

Status label: `H_ZERO_CENTERING_CANCELLATION_BANKED`.
-/

namespace RouteAFibreFrame
namespace Gate01

open Finset

/-- The centered local factor `ρ_p(n) = 1_{p ∣ n} - 1/p`, as a rational number. -/
noncomputable def rho (p : ℚ) (ind : ℚ) : ℚ := ind - 1 / p

/-- **Exact centered expansion.**  For any finite index set, weight `W` and
indicator-valued functions `a`, `b`, the centered bilinear sum expands into the
joint term, the two singleton terms and the constant term. -/
theorem centered_pair_expansion {ι : Type*} (s : Finset ι) (W a b : ι → ℚ) (p q : ℚ) :
    ∑ n ∈ s, W n * rho p (a n) * rho q (b n)
      = (∑ n ∈ s, W n * (a n * b n))
        - (1 / q) * (∑ n ∈ s, W n * a n)
        - (1 / p) * (∑ n ∈ s, W n * b n)
        + (1 / p) * (1 / q) * (∑ n ∈ s, W n) := by
  simp only [rho, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro n _
  ring

/-- **`h = 0` centering cancellation.**  If the four zero-frequency masses take
their main-term values — joint `Ŵ(0)/(pq)`, singletons `Ŵ(0)/p` and `Ŵ(0)/q`,
total `Ŵ(0)` — then the total `h = 0` contribution vanishes. -/
theorem h_zero_centering_cancellation (W0 p q J Sp Sq T : ℚ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hJ : J = W0 / (p * q)) (hSp : Sp = W0 / p) (hSq : Sq = W0 / q) (hT : T = W0) :
    J - (1 / q) * Sp - (1 / p) * Sq + (1 / p) * (1 / q) * T = 0 := by
  subst hJ hSp hSq hT
  field_simp
  ring

/-- The same cancellation stated directly on the four `Ŵ(0)/(pq)` masses:
`+ - - +` sums to zero. -/
theorem h_zero_four_masses (W0 p q : ℚ) :
    W0 / (p * q) - W0 / (p * q) - W0 / (p * q) + W0 / (p * q) = 0 := by
  ring

/-- Combination of the two banked facts: under the main-term evaluation of the
four zero-frequency masses, the centered bilinear sum vanishes at `h = 0`. -/
theorem centered_pair_h_zero_vanishes {ι : Type*} (s : Finset ι) (W a b : ι → ℚ)
    (W0 p q : ℚ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hJ : (∑ n ∈ s, W n * (a n * b n)) = W0 / (p * q))
    (hSp : (∑ n ∈ s, W n * a n) = W0 / p)
    (hSq : (∑ n ∈ s, W n * b n) = W0 / q)
    (hT : (∑ n ∈ s, W n) = W0) :
    ∑ n ∈ s, W n * rho p (a n) * rho q (b n) = 0 := by
  rw [centered_pair_expansion s W a b p q, hJ, hSp, hSq, hT]
  exact h_zero_centering_cancellation W0 p q _ _ _ _ hp hq rfl rfl rfl rfl

end Gate01
end RouteAFibreFrame
