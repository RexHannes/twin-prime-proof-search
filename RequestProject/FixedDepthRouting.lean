import Mathlib
import RequestProject.FixedDepthConvolution
import RequestProject.RoutingThreshold

/-!
# Fixed-depth routing reindexing (§6, §13.5)

A fixed-depth fragmented piece has coefficients coming from
`u w_1 ⋯ w_r = mn+2` with a Heath–Brown block `γ` on `u` and smooth blocks `ψ_i`
on the `w_i`.  Selecting a block `j` and folding the rest into the modulus,
`q = u ∏_{i≠j} w_i`, produces the routed coefficient
`λ_q^{(j)} = Σ_{u ∏_{i≠j} w_i = q} γ_u ∏_{i≠j} ψ_i(w_i)`.

This module machine-checks the **exact routing reindexing** as an identity of
Dirichlet convolutions of arithmetic functions:

`γ * ∏_i ψ_i = λ^{(j)} * ψ_j`,   `λ^{(j)} = γ * ∏_{i≠j} ψ_i`,

together with its explicit finite-sum (divisor-antidiagonal) coefficient form.
This is precisely the finite-sum bijection
`(u, w_1, …, w_r) ↔ (q, w_j)` under `u w_1 ⋯ w_r = k`.

It also records the divisor-boundedness of `λ^{(j)}` (via
`FixedDepthConvolution.maj_fixed_depth`) and the routability criterion
(via `RoutingThreshold`).
-/

namespace ShiftedMobiusBank

open ArithmeticFunction

variable {r : ℕ}

/-- The routed coefficient function `λ^{(j)} = γ * ∏_{i≠j} ψ_i`. -/
noncomputable def routedCoeff (gamma : ArithmeticFunction ℝ)
    (psi : Fin r → ArithmeticFunction ℝ) (j : Fin r) : ArithmeticFunction ℝ :=
  gamma * ∏ i ∈ Finset.univ.erase j, psi i

/-- §13.5 — the exact routing reindexing identity.  Folding all blocks except `j`
into the modulus turns the full fixed-depth convolution into a single convolution
of the routed coefficient with the selected block:
`γ * ∏_i ψ_i = λ^{(j)} * ψ_j`. -/
theorem routing_reindex (gamma : ArithmeticFunction ℝ)
    (psi : Fin r → ArithmeticFunction ℝ) (j : Fin r) :
    gamma * ∏ i, psi i = routedCoeff gamma psi j * psi j := by
  unfold routedCoeff
  have hsplit : ∏ i, psi i = (∏ i ∈ Finset.univ.erase j, psi i) * psi j := by
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  rw [hsplit]; ring

/-- §13.5 — explicit finite-sum (divisor-antidiagonal) coefficient form of the
routed piece: the coefficient at `k` is a sum over factorizations `k = q · w_j`,
with the inner factorization folded into `λ^{(j)}(q)`.  Read together with
`routing_reindex`, this is the finite-sum bijection
`(u, w_1, …, w_r) ↔ (q, w_j)`. -/
theorem routing_reindex_apply (gamma : ArithmeticFunction ℝ)
    (psi : Fin r → ArithmeticFunction ℝ) (j : Fin r) (k : ℕ) :
    (gamma * ∏ i, psi i) k
      = ∑ x ∈ k.divisorsAntidiagonal, routedCoeff gamma psi j x.1 * psi j x.2 := by
  rw [routing_reindex gamma psi j, mul_apply]

/-- §13.5 / §13.4 — the routed coefficient is divisor-bounded: if `γ` and every
`ψ_i` are bounded by a common nonnegative majorant `τ`, then `|λ^{(j)}| ≤ τ^r`
(exponent depends only on the depth `r`), matching `|λ_q^{(j)}| ≪ τ_{C(r)}(q)`. -/
theorem routedCoeff_divBounded (gamma : ArithmeticFunction ℝ)
    (psi : Fin r → ArithmeticFunction ℝ) (j : Fin r) (tau : ArithmeticFunction ℝ)
    (hτ : ∀ n, 0 ≤ tau n) (hγ : ∀ n, |gamma n| ≤ tau n)
    (hψ : ∀ i, ∀ n, |psi i n| ≤ tau n) :
    Majorizes (tau ^ r) (routedCoeff gamma psi j) := by
  unfold routedCoeff
  have hbase : Majorizes tau gamma := ⟨hτ, hγ⟩
  have hprod : Majorizes (tau ^ (Finset.univ.erase j).card)
      (∏ i ∈ Finset.univ.erase j, psi i) :=
    maj_fixed_depth _ tau psi hτ (fun i _ => hψ i)
  have hmul := maj_mul hbase hprod
  have hcard : (Finset.univ.erase j).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  rw [hcard] at hmul
  -- `tau * tau^(r-1) = tau^r` needs `r ≥ 1`, which holds since `Fin r` is inhabited by `j`.
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (fun h => by rw [h] at j; exact j.elim0)
  have : tau * tau ^ (r - 1) = tau ^ r := by
    rw [← pow_succ']; congr 1; omega
  rw [this] at hmul
  exact hmul

/-- §13.1 (routing criterion, restated for the selected block).  With
`θ_j = 1/2 - w_j`, the routed modulus satisfies the widened wedge exactly when the
selected block is longer than the routing threshold: `w_j > w*(μ)`. -/
theorem block_routable_iff (mu w : ℝ) :
    122 * mu + 162 * thetaOfW w < 1 ↔ w > wStar mu := by
  unfold thetaOfW
  exact routing_threshold_equiv mu w

end ShiftedMobiusBank
