/-
# Gate 1B safe extension — near-primitive diagonal, conditional finite form

`NPL-DIAG45` is NOT banked as an unconditional analytic statement.  What is banked is the
conditional finite inequality, and its restriction along an injective (no-wrap) index map.

The abstract same-conductor reduction itself lives in
`Gate1B/SafeAlgebra/NPLDiagonalReduction.lean` and is reused here rather than duplicated.
-/
import Gate1B.SafeAlgebra.NPLDiagonalReduction

open Finset

namespace Gate1B.SafeExtensions

open Gate1B.SafeAlgebra

/-- **Near-primitive (no-wrap) diagonal bound.**  If the conductor index map `e` is
injective on the near-primitive set `S` and lands in the ambient conductor set `T`, then the
restricted diagonal energy inherits the conditional same-conductor bound.

The injectivity ("no-wrap") hypothesis is load-bearing: without it the restricted sum can
count the same conductor many times. -/
theorem nearPrimitive_diag_energy_bound_restricted {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (T : Finset κ) (e : ι → κ) (gw Z T2 : κ → ℝ) (B2 C2 Kbd : ℝ)
    (hB2 : 0 ≤ B2)
    (hT2nn : ∀ g ∈ T, 0 ≤ T2 g)
    (hT2 : ∀ g ∈ T, T2 g ≤ gw g ^ 2 * B2)
    (hglob : ∑ g ∈ T, gw g ^ 2 * Z g ^ 2 ≤ Kbd * C2)
    (hmaps : ∀ i ∈ S, e i ∈ T) (hinj : Set.InjOn e S) :
    ∑ i ∈ S, Z (e i) ^ 2 * T2 (e i) ≤ Kbd * B2 * C2 := by
  have hrestrict : ∑ i ∈ S, Z (e i) ^ 2 * T2 (e i) ≤ ∑ g ∈ T, Z g ^ 2 * T2 g :=
    sum_le_of_injOn S T e (fun g => Z g ^ 2 * T2 g)
      (fun g hg => mul_nonneg (sq_nonneg _) (hT2nn g hg)) hmaps hinj
  exact le_trans hrestrict (sameConductorDiagonal_le T gw Z T2 B2 C2 Kbd hB2 hT2 hglob)

/-- The injectivity hypothesis is load-bearing: with a constant index map the restricted
sum grows with `|S|` while the ambient sum does not. -/
theorem nearPrimitive_needs_injectivity :
    ∃ (S : Finset (Fin 3)) (T : Finset (Fin 1)) (e : Fin 3 → Fin 1) (F : Fin 1 → ℝ),
      (∀ k ∈ T, 0 ≤ F k) ∧ (∀ i ∈ S, e i ∈ T) ∧ ∑ k ∈ T, F k < ∑ i ∈ S, F (e i) := by
  refine ⟨Finset.univ, Finset.univ, fun _ => 0, fun _ => 1, by norm_num, by simp, ?_⟩
  simp

end Gate1B.SafeExtensions
