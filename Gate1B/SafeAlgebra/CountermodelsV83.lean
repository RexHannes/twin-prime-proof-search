/-
# Gate 1B v8.3 — firewall countermodels

**Status: COUNTERMODEL (all four are explicit finite constructions).**

* `A` — high-order grouping: with at least two models left, anchoring one
  particular set of defects is **not** the only legal regroup, and different
  legal regroups genuinely produce different coefficients `B`;
* `B` — same-`q`: equal Fourier/residue energy, different character-Gram
  output;
* `C` — bulk/spike: a finite instance where the generic bulk/spike bound is
  strictly worse than the direct ℓ² (Cauchy–Schwarz) bound;
* `D` — zero mode: changing the expected term `E` leaves the nonzero-frequency
  part unchanged but moves the zero residual `R_E`.
-/
import Mathlib
import Gate1B.SafeAlgebra.HighOrderShellRegroup
import Gate1B.SafeAlgebra.SameQCountermodel
import Gate1B.SafeExtensions.V83ZeroModeResidual
import Universal.SafeAlgebra.BulkSpikeInterpolation

namespace Gate1B.SafeAlgebra

open Finset

/-- **Countermodel A — the regroup is not unique.**  Both two-model regroups of
a four-model shell are exact, yet the two absorbed coefficients differ. -/
theorem countermodel_A_regroup_not_unique :
    (∀ C x1 x2 x3 x4 q ell : ℤ,
        (C * x1 * x2 * x3 * x4 - q * ell = -2 ↔ (C * x1 * x2) * x3 * x4 - q * ell = -2) ∧
        (C * x1 * x2 * x3 * x4 - q * ell = -2 ↔ (C * x3 * x4) * x1 * x2 - q * ell = -2)) ∧
      ∃ C x1 x2 x3 x4 : ℤ, C * x1 * x2 ≠ C * x3 * x4 := by
  constructor
  · intro C x1 x2 x3 x4 q ell
    exact ⟨by constructor <;> intro h <;> linear_combination h,
      by constructor <;> intro h <;> linear_combination h⟩
  · exact ⟨1, 1, 1, 2, 3, by norm_num⟩

/-- **Countermodel B — same-`q`.**  Two hat-vectors with equal total Fourier
energy and different Gram output (restated from `SameQCountermodel`). -/
theorem countermodel_B_sameQ_gram :
    ∃ (w : Fin 2 → Fin 2 → ℂ) (R1 R2 : Fin 2 → ℂ),
      fourierEnergy R1 = fourierEnergy R2 ∧ gramForm w R1 ≠ gramForm w R2 :=
  sameQ_not_function_of_residueEnergy

/-- **Countermodel C — bulk/spike can be worse than plain ℓ².**  On a one-point
index set with `A = T = 1` and threshold `L = 1`, the direct Cauchy–Schwarz
bound is `1` while the generic bulk/spike bound is `2`. -/
theorem countermodel_C_bulkSpike_worse_than_l2 :
    ∃ (A T : Fin 1 → ℂ) (L Tsup : ℝ), 0 < L ∧ 0 ≤ Tsup ∧ (∀ d, ‖T d‖ ≤ Tsup) ∧
      Universal.SafeAlgebra.l2Norm A * Universal.SafeAlgebra.l2Norm T
        < L * Real.sqrt (Fintype.card (Fin 1)) * Universal.SafeAlgebra.l2Norm T
            + Tsup * ((∑ d : Fin 1, ‖A d‖ ^ 2) / L) := by
  refine ⟨fun _ => 1, fun _ => 1, 1, 1, by norm_num, by norm_num, fun d => by norm_num, ?_⟩
  have hl2 : Universal.SafeAlgebra.l2Norm (fun _ : Fin 1 => (1 : ℂ)) = 1 := by
    unfold Universal.SafeAlgebra.l2Norm
    norm_num
  rw [hl2]
  norm_num

/-- **Countermodel D — zero mode.**  Two expected terms with the same nonzero
part but different residual `R_E`. -/
theorem countermodel_D_zeroMode_residual :
    ∃ (lam canonicalMain E E' : Fin 2 → ℂ),
      nonzeroPart E' = nonzeroPart E ∧
        Gate1B.SafeExtensions.RE lam canonicalMain E'
          ≠ Gate1B.SafeExtensions.RE lam canonicalMain E := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 1, ?_, ?_⟩
  · have h := nonzeroPart_independent_expectedTerm (ι := Fin 2) (fun _ => (1 : ℂ)) 1
    have hfun : (fun i : Fin 2 => (1 : ℂ) - 1) = fun _ : Fin 2 => (0 : ℂ) := by
      funext i; ring
    rw [hfun] at h
    exact h.symm
  · unfold Gate1B.SafeExtensions.RE
    simp [Fin.sum_univ_two]

end Gate1B.SafeAlgebra
