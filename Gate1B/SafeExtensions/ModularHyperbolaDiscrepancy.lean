/-
# Gate 1B v13 — modular-hyperbola discrepancy input (UNINHABITED)

**Status: interface UNINHABITED; the implications are PROVED.**

The off-diagonal same-`q` Gram is controlled by the *discrepancy*

    Δ ≥ max_r | g(r) − mean |,

where `g` is the weighted product-residue function and
`mean = (∑u)(∑v)/|G|`.  This is exactly the modular-hyperbola discrepancy.

The research value `q^{1/2+o(1)}` is **NOT** inserted: no numerical value is
asserted anywhere.  The repository contains no finite Weil/Kloosterman theorem
strong enough to construct the input honestly (the banked Kloosterman material
is reindexing and exact algebra only), so the interface stays **UNINHABITED**.

Proved here:

* `centredKernel_norm_le_of_discrepancy` — the discrepancy input bounds the
  centred kernel at every non-principal character by `|G| Δ`;
* `sameQGramOff_bound_of_kernel_bound` — a kernel bound at non-principal
  characters bounds the off-diagonal Gram;
* `sameQGramOff_bound_of_discrepancy` — the composition.
-/
import Mathlib
import Gate1B.SafeAlgebra.ProductResidueCharacterKernel
import Gate1B.SafeAlgebra.SameQCharacterGramDiagonalization

namespace Gate1B.SafeExtensions

open Finset Gate1B.SafeAlgebra Gate1B.SafeAlgebra.MulCharSystem

variable {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] [CommGroup Ch]

/-- **UNINHABITED INTERFACE.**  The modular-hyperbola discrepancy bound. -/
structure ModularHyperbolaDiscrepancyInput (u v : G → ℂ) (Delta : ℝ) : Prop where
  /-- EXTERNAL ANALYTIC INPUT — never supplied here. -/
  discrepancy_le : ∀ r : G, ‖productResidueWeight u v r - productResidueMean u v‖ ≤ Delta

omit [DecidableEq G] in
/-- **Non-vacuity guard.** -/
theorem modularHyperbolaDiscrepancyInput_not_vacuous [Nonempty G] (u v : G → ℂ) :
    ¬ ModularHyperbolaDiscrepancyInput u v (-1) := by
  intro h
  obtain ⟨r⟩ := ‹Nonempty G›
  have := h.discrepancy_le r
  have h0 : (0 : ℝ) ≤ ‖productResidueWeight u v r - productResidueMean u v‖ := norm_nonneg _
  linarith

/-- Non-principal characters sum to zero over the group. -/
theorem sum_chi_eq_zero_of_ne_one (S : MulCharSystem G Ch)
    (hprin : ∀ g : G, S.chi (1 : Ch) g = 1) {psi : Ch} (hpsi : psi ≠ 1) :
    ∑ g : G, S.chi psi g = 0 := by
  have h := S.orthogonality psi 1
  simp only [hprin, map_one, mul_one] at h
  rw [h]
  simp [hpsi]

/-- **Discrepancy ⟹ centred-kernel bound.**  At every non-principal character the
kernel is `∑_r (g(r) − mean) ψ(r)`, hence bounded by `|G| Δ`. -/
theorem centredKernel_norm_le_of_discrepancy (S : MulCharSystem G Ch)
    (hprin : ∀ g : G, S.chi (1 : Ch) g = 1) (u v : G → ℂ) (Delta : ℝ)
    (hin : ModularHyperbolaDiscrepancyInput u v Delta) {psi : Ch} (hpsi : psi ≠ 1) :
    ‖S.productKernel u v psi‖ ≤ (Fintype.card G : ℝ) * Delta := by
  classical
  have hzero : ∑ r : G, productResidueMean u v * S.chi psi r = 0 := by
    rw [← Finset.mul_sum, sum_chi_eq_zero_of_ne_one S hprin hpsi, mul_zero]
  have hK : S.productKernel u v psi
      = ∑ r : G, (productResidueWeight u v r - productResidueMean u v) * S.chi psi r := by
    rw [S.kernel_eq_sum_productResidue u v psi]
    rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => sub_mul
      (productResidueWeight u v r) (productResidueMean u v) (S.chi psi r)]
    rw [Finset.sum_sub_distrib, hzero, sub_zero]
  rw [hK]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ r : G,
      ‖(productResidueWeight u v r - productResidueMean u v) * S.chi psi r‖ ≤ Delta := by
    intro r
    rw [norm_mul, S.norm_one psi r, mul_one]
    exact hin.discrepancy_le r
  calc ∑ r : G, ‖(productResidueWeight u v r - productResidueMean u v) * S.chi psi r‖
      ≤ ∑ _r : G, Delta := Finset.sum_le_sum fun r _ => hterm r
    _ = (Fintype.card G : ℝ) * Delta := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Kernel bound at non-principal characters ⟹ off-diagonal Gram bound.** -/
theorem sameQGramOff_bound_of_kernel_bound (c : Ch → ℂ) (K : Ch → ℂ) (D : ℝ)
    (hD0 : 0 ≤ D) (hK : ∀ psi : Ch, psi ≠ 1 → ‖K psi‖ ≤ D) :
    ‖sameQGramOff c K‖
      ≤ (1 / (Fintype.card Ch : ℝ) ^ 2) * (D * (∑ x : Ch, ‖c x‖) ^ 2) := by
  classical
  unfold sameQGramOff
  rw [norm_mul]
  have hcard : ‖(1 / (Fintype.card Ch : ℂ) ^ 2)‖ = 1 / (Fintype.card Ch : ℝ) ^ 2 := by
    rw [norm_div, NormOneClass.norm_one, norm_pow, Complex.norm_natCast]
  rw [hcard]
  have hinner : ‖∑ x1 : Ch, ∑ x2 ∈ Finset.univ.erase x1,
      c x1 * (starRingEnd ℂ) (c x2) * K (x1 * x2⁻¹)‖
      ≤ D * (∑ x : Ch, ‖c x‖) ^ 2 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hrow : ∀ x1 : Ch, ‖∑ x2 ∈ Finset.univ.erase x1,
        c x1 * (starRingEnd ℂ) (c x2) * K (x1 * x2⁻¹)‖
        ≤ ∑ x2 : Ch, ‖c x1‖ * ‖c x2‖ * D := by
      intro x1
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun x2 hx2 => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun x2 _ _ => by positivity))
      have hne : x1 * x2⁻¹ ≠ 1 := by
        intro h0
        exact (Finset.mem_erase.mp hx2).1 (by
          have : x1 = x2 := by
            have := mul_inv_eq_one.mp h0
            exact this
          exact this.symm)
      rw [norm_mul, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hK _ hne) (by positivity)
    refine le_trans (Finset.sum_le_sum fun x1 _ => hrow x1) ?_
    have : ∀ x1 : Ch, ∑ x2 : Ch, ‖c x1‖ * ‖c x2‖ * D
        = ‖c x1‖ * (∑ x2 : Ch, ‖c x2‖) * D := by
      intro x1
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x1 _ => this x1]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    rw [sq]
    ring_nf
    exact le_of_eq rfl
  have hpos : (0 : ℝ) ≤ 1 / (Fintype.card Ch : ℝ) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hinner hpos

/-- **Discrepancy ⟹ off-diagonal same-`q` Gram bound.**  The composition; the
discrepancy input is never supplied. -/
theorem sameQGramOff_bound_of_discrepancy (S : MulCharSystem G Ch)
    (hprin : ∀ g : G, S.chi (1 : Ch) g = 1) (u v : G → ℂ) (Delta : ℝ) (hDelta : 0 ≤ Delta)
    (hin : ModularHyperbolaDiscrepancyInput u v Delta) (c : Ch → ℂ) :
    ‖sameQGramOff c (S.productKernel u v)‖
      ≤ (1 / (Fintype.card Ch : ℝ) ^ 2)
          * (((Fintype.card G : ℝ) * Delta) * (∑ x : Ch, ‖c x‖) ^ 2) := by
  refine sameQGramOff_bound_of_kernel_bound c (S.productKernel u v)
    ((Fintype.card G : ℝ) * Delta) (by positivity) ?_
  intro psi hpsi
  exact centredKernel_norm_le_of_discrepancy S hprin u v Delta hin hpsi

end Gate1B.SafeExtensions
