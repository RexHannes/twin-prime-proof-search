/-
# Gate-1A Δv4 §11 — rank-one prime-coefficient preservation

Any residual smooth dependence on the prime variables `u = L/p`, `v = L/q`
must not destroy the rank-one structure of the source in `(p,q)`.  The exact
statement proved here is the *separable expansion* one:

if
```
F(u, v, x) = ∑_λ c_λ(x) A_λ(u) B_λ(v)
```
(a finite, absolutely summable separable expansion), then the weighted prime
source satisfies exactly

```
∑_p ∑_q b_p d_q F(L/p, L/q, x)
  = ∑_λ c_λ(x) · (∑_p b_p A_λ(L/p)) · (∑_q d_q B_λ(L/q)),
```

so each mode `λ` acts only by `b_p ↦ b_p A_λ(L/p)`, `d_q ↦ d_q B_λ(L/q)` and
remains **rank-one** in the prime source variables.  The nuclear bound
`∑_λ ‖c_λ‖ ‖A_λ‖_∞ ‖B_λ‖_∞ ≤ C` is carried as a hypothesis and used to bound
the total.
-/
import Mathlib

namespace Gate1A

namespace Delta4

open Finset

/-! ## The exact rank-one factorisation -/

/-- **§11 (`smooth_pq_separation_preserves_rankOne`).**  A finite separable
expansion of the smooth `p/q` factor turns the double prime sum into a sum of
**rank-one** modes, exactly. -/
theorem smooth_pq_separation_preserves_rankOne {P Q Λ : Type*}
    (sp : Finset P) (sq : Finset Q) (sl : Finset Λ)
    (b : P → ℂ) (d : Q → ℂ) (Amod : Λ → P → ℂ) (Bmod : Λ → Q → ℂ) (c : Λ → ℂ)
    (F : P → Q → ℂ)
    (hF : ∀ p ∈ sp, ∀ q ∈ sq, F p q = ∑ lam ∈ sl, c lam * Amod lam p * Bmod lam q) :
    (∑ p ∈ sp, ∑ q ∈ sq, b p * d q * F p q)
      = ∑ lam ∈ sl, c lam * (∑ p ∈ sp, b p * Amod lam p) * (∑ q ∈ sq, d q * Bmod lam q) := by
  have h1 : ∀ p ∈ sp, ∑ q ∈ sq, b p * d q * F p q
      = ∑ lam ∈ sl, ∑ q ∈ sq, c lam * (b p * Amod lam p) * (d q * Bmod lam q) := by
    intro p hp
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hF p hp q hq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun lam _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- The accompanying nuclear bound: with `∑_λ |c_λ| ‖A_λ‖_∞ ‖B_λ‖_∞ ≤ C` and
`ℓ¹`-bounded prime coefficients, the rank-one expansion is absolutely
summable with total mass at most `C · ‖b‖₁ ‖d‖₁`. -/
theorem rankOne_nuclear_bound {P Q Λ : Type*}
    (sp : Finset P) (sq : Finset Q) (sl : Finset Λ)
    (b : P → ℂ) (d : Q → ℂ) (Amod : Λ → P → ℂ) (Bmod : Λ → Q → ℂ) (c : Λ → ℂ)
    (nA nB : Λ → ℝ) (C Nb Nd : ℝ)
    (hA : ∀ lam ∈ sl, ∀ p ∈ sp, ‖Amod lam p‖ ≤ nA lam)
    (hB : ∀ lam ∈ sl, ∀ q ∈ sq, ‖Bmod lam q‖ ≤ nB lam)
    (hnuc : ∑ lam ∈ sl, ‖c lam‖ * nA lam * nB lam ≤ C)
    (hb : ∑ p ∈ sp, ‖b p‖ ≤ Nb) (hd : ∑ q ∈ sq, ‖d q‖ ≤ Nd)
    (hNb : 0 ≤ Nb) (hNd : 0 ≤ Nd) (hnA : ∀ lam ∈ sl, 0 ≤ nA lam)
    (hnB : ∀ lam ∈ sl, 0 ≤ nB lam) :
    ‖∑ lam ∈ sl, c lam * (∑ p ∈ sp, b p * Amod lam p) * (∑ q ∈ sq, d q * Bmod lam q)‖
      ≤ C * Nb * Nd := by
  have hX : ∀ lam ∈ sl, ‖∑ p ∈ sp, b p * Amod lam p‖ ≤ Nb * nA lam := by
    intro lam hlam
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ p ∈ sp, ‖b p * Amod lam p‖ ≤ ‖b p‖ * nA lam := by
      intro p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hA lam hlam p hp) (norm_nonneg _)
    calc ∑ p ∈ sp, ‖b p * Amod lam p‖ ≤ ∑ p ∈ sp, ‖b p‖ * nA lam :=
          Finset.sum_le_sum hterm
      _ = (∑ p ∈ sp, ‖b p‖) * nA lam := by rw [Finset.sum_mul]
      _ ≤ Nb * nA lam := mul_le_mul_of_nonneg_right hb (hnA lam hlam)
  have hY : ∀ lam ∈ sl, ‖∑ q ∈ sq, d q * Bmod lam q‖ ≤ Nd * nB lam := by
    intro lam hlam
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ q ∈ sq, ‖d q * Bmod lam q‖ ≤ ‖d q‖ * nB lam := by
      intro q hq
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB lam hlam q hq) (norm_nonneg _)
    calc ∑ q ∈ sq, ‖d q * Bmod lam q‖ ≤ ∑ q ∈ sq, ‖d q‖ * nB lam :=
          Finset.sum_le_sum hterm
      _ = (∑ q ∈ sq, ‖d q‖) * nB lam := by rw [Finset.sum_mul]
      _ ≤ Nd * nB lam := mul_le_mul_of_nonneg_right hd (hnB lam hlam)
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ lam ∈ sl,
      ‖c lam * (∑ p ∈ sp, b p * Amod lam p) * (∑ q ∈ sq, d q * Bmod lam q)‖
        ≤ (‖c lam‖ * nA lam * nB lam) * (Nb * Nd) := by
    intro lam hlam
    rw [norm_mul, norm_mul]
    have h1 : ‖c lam‖ * ‖∑ p ∈ sp, b p * Amod lam p‖ ≤ ‖c lam‖ * (Nb * nA lam) :=
      mul_le_mul_of_nonneg_left (hX lam hlam) (norm_nonneg _)
    have h2 : ‖∑ q ∈ sq, d q * Bmod lam q‖ ≤ Nd * nB lam := hY lam hlam
    have h3 : (0 : ℝ) ≤ ‖c lam‖ * (Nb * nA lam) := by
      have := hnA lam hlam
      positivity
    calc ‖c lam‖ * ‖∑ p ∈ sp, b p * Amod lam p‖ * ‖∑ q ∈ sq, d q * Bmod lam q‖
        ≤ (‖c lam‖ * (Nb * nA lam)) * ‖∑ q ∈ sq, d q * Bmod lam q‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ (‖c lam‖ * (Nb * nA lam)) * (Nd * nB lam) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = (‖c lam‖ * nA lam * nB lam) * (Nb * Nd) := by ring
  calc ∑ lam ∈ sl, ‖c lam * (∑ p ∈ sp, b p * Amod lam p) * (∑ q ∈ sq, d q * Bmod lam q)‖
      ≤ ∑ lam ∈ sl, (‖c lam‖ * nA lam * nB lam) * (Nb * Nd) := Finset.sum_le_sum hterm
    _ = (∑ lam ∈ sl, ‖c lam‖ * nA lam * nB lam) * (Nb * Nd) := by rw [Finset.sum_mul]
    _ ≤ C * (Nb * Nd) := mul_le_mul_of_nonneg_right hnuc (by positivity)
    _ = C * Nb * Nd := by ring

end Delta4

end Gate1A
