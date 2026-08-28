/-
# Gate 1B v13 — same-`q` character Gram: exact diagonal / off-diagonal splitting

**Status: PROVED_ALGEBRAIC (finite algebra only, no estimate).**

For an abstract finite character index `Ch` (a finite group: the dual `Ĝ`),
coefficients `c : Ch → ℂ` and a kernel `K : Ch → ℂ` of product shape
`K(ψ) = U(ψ) · V(ψ)`, the same-`q` Gram form is

    S = (1/|Ch|²) ∑_{χ₁,χ₂} c(χ₁) conj(c(χ₂)) K(χ₁ χ₂⁻¹).

We prove the exact decomposition `S = S_diag + S_off`, where `S_diag` is the
`χ₁ = χ₂` part and equals `K(1)/|Ch|² · ∑_χ |c(χ)|²`.

No estimate is made anywhere: this is bookkeeping that keeps the diagonal —
which can carry the uniform-density mass — separate from the cross-character
off-diagonal (**Counterguard A**).

Contents:

* `sameQGram`, `sameQGramDiag`, `sameQGramOff`;
* `sameQGram_split` — the exact decomposition;
* `sameQGramDiag_eq` — the closed form of the diagonal;
* `sameQGram_diag_ne_off` — the counterguard instance.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] [CommGroup Ch]

/-- The kernel of product shape `K(ψ) = U(ψ) V(ψ)`. -/
def gramKernel (U V : Ch → ℂ) (psi : Ch) : ℂ := U psi * V psi

/-- The same-`q` character Gram form. -/
noncomputable def sameQGram (c : Ch → ℂ) (K : Ch → ℂ) : ℂ :=
  (1 / (Fintype.card Ch : ℂ) ^ 2)
    * ∑ x1 : Ch, ∑ x2 : Ch, c x1 * (starRingEnd ℂ) (c x2) * K (x1 * x2⁻¹)

/-- The diagonal (`χ₁ = χ₂`) part. -/
noncomputable def sameQGramDiag (c : Ch → ℂ) (K : Ch → ℂ) : ℂ :=
  (1 / (Fintype.card Ch : ℂ) ^ 2) * ∑ x : Ch, c x * (starRingEnd ℂ) (c x) * K (x * x⁻¹)

/-- The off-diagonal (`χ₁ ≠ χ₂`) part. -/
noncomputable def sameQGramOff (c : Ch → ℂ) (K : Ch → ℂ) : ℂ :=
  (1 / (Fintype.card Ch : ℂ) ^ 2)
    * ∑ x1 : Ch, ∑ x2 ∈ Finset.univ.erase x1, c x1 * (starRingEnd ℂ) (c x2) * K (x1 * x2⁻¹)

/-- **Exact same-`q` Gram decomposition.** -/
theorem sameQGram_split (c : Ch → ℂ) (K : Ch → ℂ) :
    sameQGram c K = sameQGramDiag c K + sameQGramOff c K := by
  classical
  unfold sameQGram sameQGramDiag sameQGramOff
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x1 _ => ?_
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ x1)).symm

omit [DecidableEq Ch] in
/-- **Closed form of the diagonal**: it is `K(1)` times the coefficient energy. -/
theorem sameQGramDiag_eq (c : Ch → ℂ) (K : Ch → ℂ) :
    sameQGramDiag c K
      = (1 / (Fintype.card Ch : ℂ) ^ 2) * (K 1 * ∑ x : Ch, ((‖c x‖ ^ 2 : ℝ) : ℂ)) := by
  unfold sameQGramDiag
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_inv_cancel]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ring

omit [DecidableEq Ch] in
/-- With a centred kernel (`K(1) = 0`) the diagonal vanishes identically, so the
whole Gram form is its off-diagonal part. -/
theorem sameQGramDiag_eq_zero_of_centred (c : Ch → ℂ) (K : Ch → ℂ) (hK : K 1 = 0) :
    sameQGramDiag c K = 0 := by
  rw [sameQGramDiag_eq c K, hK]
  simp

omit [DecidableEq Ch] in
/-- **Counterguard A (same-`q` full energy ≠ cross-character off-diagonal).**
With the flat kernel the diagonal alone is already nonzero for any nonzero
coefficient vector, so the diagonal — which can carry the uniform-density mass —
must never be discarded into the off-diagonal. -/
theorem sameQGramDiag_ne_zero_of_flat_kernel (c : Ch → ℂ) (x0 : Ch) (hx0 : c x0 ≠ 0) :
    sameQGramDiag c (fun _ => 1) ≠ 0 := by
  classical
  rw [sameQGramDiag_eq c (fun _ => 1)]
  have hpos : 0 < ∑ x : Ch, ‖c x‖ ^ 2 := by
    refine Finset.sum_pos' (fun x _ => by positivity) ⟨x0, Finset.mem_univ x0, ?_⟩
    have : 0 < ‖c x0‖ := norm_pos_iff.mpr hx0
    positivity
  have hne : ((∑ x : Ch, ‖c x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hcard : ((Fintype.card Ch : ℂ)) ≠ 0 := by
    have : 0 < Fintype.card Ch := Fintype.card_pos
    exact_mod_cast Nat.cast_ne_zero.2 this.ne'
  have hsum : (∑ x : Ch, ((‖c x‖ ^ 2 : ℝ) : ℂ)) = ((∑ x : Ch, ‖c x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsum, one_mul]
  exact mul_ne_zero (by simp [pow_ne_zero 2 hcard]) hne

end Gate1B.SafeAlgebra
