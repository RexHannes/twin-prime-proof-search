/-
# Gate 1B — abstract same-conductor diagonal reduction

An elementary implication between supplied nonnegative data.  It captures exactly the
logical step used by `NPL-DIAG45` and NOTHING ELSE: the two hypotheses are NOT asserted
for the actual Gate source, where they are analytic/source interfaces.
-/
import Mathlib

open Finset

namespace Gate1B.SafeAlgebra

/-- **(DIAG-RED).**  If `T₂(g) ≤ g² B₂` for every `g`, and `∑_g g² |Z g|² ≤ K C₂`, then
`∑_g |Z g|² T₂(g) ≤ K B₂ C₂`. -/
theorem sameConductorDiagonal_le {ι : Type*} (S : Finset ι) (gw Z T2 : ι → ℝ)
    (B2 C2 Kbd : ℝ) (hB2 : 0 ≤ B2)
    (hT2 : ∀ g ∈ S, T2 g ≤ gw g ^ 2 * B2)
    (hglob : ∑ g ∈ S, gw g ^ 2 * Z g ^ 2 ≤ Kbd * C2) :
    ∑ g ∈ S, Z g ^ 2 * T2 g ≤ Kbd * B2 * C2 := by
  have step1 : ∑ g ∈ S, Z g ^ 2 * T2 g ≤ ∑ g ∈ S, Z g ^ 2 * (gw g ^ 2 * B2) :=
    Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left (hT2 g hg) (sq_nonneg _)
  have step2 : ∑ g ∈ S, Z g ^ 2 * (gw g ^ 2 * B2) = B2 * ∑ g ∈ S, gw g ^ 2 * Z g ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  have step3 : B2 * ∑ g ∈ S, gw g ^ 2 * Z g ^ 2 ≤ B2 * (Kbd * C2) :=
    mul_le_mul_of_nonneg_left hglob hB2
  calc ∑ g ∈ S, Z g ^ 2 * T2 g ≤ ∑ g ∈ S, Z g ^ 2 * (gw g ^ 2 * B2) := step1
    _ = B2 * ∑ g ∈ S, gw g ^ 2 * Z g ^ 2 := step2
    _ ≤ B2 * (Kbd * C2) := step3
    _ = Kbd * B2 * C2 := by ring

/-- Restriction along an injective index map: a nonnegative finite sum over an injective
image is bounded by the ambient sum.  (The "injective-subset restriction inequality"
used inside the near-primitive diagonal argument.) -/
theorem sum_le_of_injOn {ι κ : Type*} [DecidableEq κ] (S : Finset ι) (T : Finset κ)
    (e : ι → κ) (F : κ → ℝ) (hnn : ∀ k ∈ T, 0 ≤ F k)
    (hmaps : ∀ i ∈ S, e i ∈ T) (hinj : Set.InjOn e S) :
    ∑ i ∈ S, F (e i) ≤ ∑ k ∈ T, F k := by
  classical
  rw [← Finset.sum_image (f := F) (g := e) (fun x hx y hy h => hinj hx hy h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k hk _ => hnn k hk)
  intro k hk
  simp only [Finset.mem_image] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  exact hmaps i hi

/-- **Near-primitive conditional diagonal energy bound.**  Under the supplied finite
hypotheses (A2/B2/C2 in the Gate notation) the diagonal energy obeys the stated algebraic
bound.  The passage to an asymptotic `X R^{-1/2} X^{o(1)}` statement is analytic and is
deliberately NOT formalised here. -/
theorem nearPrimitive_diag_energy_bound {ι : Type*} (S : Finset ι) (gw Z T2 : ι → ℝ)
    (A2 B2 C2 Kbd : ℝ) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hT2 : ∀ g ∈ S, T2 g ≤ gw g ^ 2 * B2)
    (hglob : ∑ g ∈ S, gw g ^ 2 * Z g ^ 2 ≤ Kbd * C2) :
    A2 * ∑ g ∈ S, Z g ^ 2 * T2 g ≤ A2 * (Kbd * B2 * C2) :=
  mul_le_mul_of_nonneg_left
    (sameConductorDiagonal_le S gw Z T2 B2 C2 Kbd hB2 hT2 hglob) hA2

/-! ## Gate 1B congestion-budget algebra -/

/-- **Gate 1B congestion budget.**  From `A₂ ≤ c_A U`, `B₂ ≤ c_B V`, `C₂ ≤ c_C Q`,
`E ≤ 𝔠 B₂ C₂` and `U V = X` one gets `A₂ E ≤ c_A c_B c_C 𝔠 X Q`.

No log-saving and no `X^{o(1)}` claim is encoded. -/
theorem gate1B_congestionBudget (A2 B2 C2 E U V Q X cA cB cC cong : ℝ)
    (hB2nn : 0 ≤ B2) (hC2nn : 0 ≤ C2) (hEnn : 0 ≤ E)
    (hcongnn : 0 ≤ cong) (hcAnn : 0 ≤ cA) (hUnn : 0 ≤ U)
    (hA2 : A2 ≤ cA * U) (hB2 : B2 ≤ cB * V) (hC2 : C2 ≤ cC * Q)
    (hE : E ≤ cong * B2 * C2) (hUV : U * V = X) :
    A2 * E ≤ cA * cB * cC * cong * X * Q := by
  have hBC : B2 * C2 ≤ (cB * V) * (cC * Q) :=
    mul_le_mul hB2 hC2 hC2nn (le_trans hB2nn hB2)
  have hE' : E ≤ cong * ((cB * V) * (cC * Q)) := by
    calc E ≤ cong * B2 * C2 := hE
      _ = cong * (B2 * C2) := by ring
      _ ≤ cong * ((cB * V) * (cC * Q)) := mul_le_mul_of_nonneg_left hBC hcongnn
  have hprod : A2 * E ≤ (cA * U) * (cong * ((cB * V) * (cC * Q))) :=
    mul_le_mul hA2 hE' hEnn (by positivity)
  calc A2 * E ≤ (cA * U) * (cong * ((cB * V) * (cC * Q))) := hprod
    _ = cA * cB * cC * cong * (U * V) * Q := by ring
    _ = cA * cB * cC * cong * X * Q := by rw [hUV]

/-- Sufficient budget: if the target `T` satisfies `c_A c_B c_C 𝔠 X Q ≤ T` then the
conclusion of `gate1B_congestionBudget` closes the target. -/
theorem gate1B_congestionBudget_closes (A2 B2 C2 E U V Q X cA cB cC cong T : ℝ)
    (hB2nn : 0 ≤ B2) (hC2nn : 0 ≤ C2) (hEnn : 0 ≤ E)
    (hcongnn : 0 ≤ cong) (hcAnn : 0 ≤ cA) (hUnn : 0 ≤ U)
    (hA2 : A2 ≤ cA * U) (hB2 : B2 ≤ cB * V) (hC2 : C2 ≤ cC * Q)
    (hE : E ≤ cong * B2 * C2) (hUV : U * V = X)
    (hT : cA * cB * cC * cong * X * Q ≤ T) : A2 * E ≤ T :=
  le_trans (gate1B_congestionBudget A2 B2 C2 E U V Q X cA cB cC cong hB2nn hC2nn hEnn
    hcongnn hcAnn hUnn hA2 hB2 hC2 hE hUV) hT

end Gate1B.SafeAlgebra
