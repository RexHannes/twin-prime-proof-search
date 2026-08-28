/-
# Gate 1B v8.4 — full-divisor self-duality (anti-loop certificate)

**Status: PROVED_FINITE.**

Specialising the projector divisor to `d = c₀` gives `p c₀ ∣ n N - 2`, i.e. with
`c = p c₀` the exact shell

  `n N - c ℓ' = 2`,

and, reassociating `N = C₇ x`,

  `C₇ x n - c ℓ' = 2`.

This is the same two-model determinant SHAPE as the original H7 packet: the
full-divisor projector child reconstructs the H7 determinant geometry.  It is an
**anti-loop certificate** — no analytic equivalence of the weights is claimed
(see `CountermodelsV84.lean`, item D).
-/
import Mathlib
import Gate1B.SafeAlgebra.H7DualDeterminant

namespace Gate1B.SafeAlgebra

/-- **Full-divisor dual shell.**  With `d = c₀` and `c = p c₀`, the dual
determinant shell is `n N - c ℓ' = 2`. -/
theorem h7_fullDivisor_dualShell {p c0 c n N : ℤ} (hc : c = p * c0)
    (hp : p ∣ n * N - 2) (hd : c0 ∣ n * N - 2) (hcop : IsCoprime p c0) :
    ∃ ell : ℤ, n * N - c * ell = 2 := by
  obtain ⟨ell, hell⟩ := h7_dualDet_shell (pd_dvd_dualDet hp hd hcop)
  exact ⟨ell, by rw [hc]; linarith [hell]⟩

/-- **Self-dual shell shape.**  Reassociating `N = C₇ x` the shell reads
`C₇ x n - c ℓ' = 2`, the two-model determinant shape of the H7 packet. -/
theorem h7_selfDual_shellShape {c n N C7 x ell : ℤ} (hN : N = C7 * x)
    (h : n * N - c * ell = 2) :
    C7 * x * n - c * ell = 2 := by
  rw [hN] at h; linarith [h]

/-- The two statements combined: full-divisor projector child ⟹ H7 determinant
geometry. -/
theorem h7_fullDivisor_reconstructs_H7shape {p c0 c n N C7 x : ℤ} (hc : c = p * c0)
    (hN : N = C7 * x) (hp : p ∣ n * N - 2) (hd : c0 ∣ n * N - 2) (hcop : IsCoprime p c0) :
    ∃ ell : ℤ, C7 * x * n - c * ell = 2 := by
  obtain ⟨ell, hell⟩ := h7_fullDivisor_dualShell hc hp hd hcop
  exact ⟨ell, h7_selfDual_shellShape hN hell⟩

end Gate1B.SafeAlgebra
