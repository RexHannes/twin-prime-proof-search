/-
# Gate 1B v8.2 — signed-parent / asymmetric Cauchy, and the double-Cauchy firewall

* `asymmetricCauchy_left` — `β` stays inside the coherent inner sum:

      |∑_r δ_r (∑_q β_q K_{r,q})|² ≤ (∑_r |δ_r|²) · (∑_r |∑_q β_q K_{r,q}|²).

* `asymmetricCauchy_right` — the mirror statement, `δ` coherent inside.
* `signedParent_zero_counterexample` / `coefficientBlindEnergy_positive_counterexample`
  — an explicit `Fin 2` example where the signed parent vanishes while the
  coefficient-blind energy is positive.
* `doubleCauchy_can_destroy_exact_signed_cancellation` — the firewall: two data
  sets with *equal* coefficient-blind energies and *different* signed parents,
  so no coefficient-blind quantity can certify signed cancellation.
* `signedParentCounterexample_smul_energy` — compatibility with the banked v8.1
  homogeneity lemmas (`quadraticEnergy_smul`, `noPositiveUniformEnergyFloor`).

Everything is finite complex algebra.  **No** analytic estimate is claimed, and
in particular an asymmetric Cauchy inequality does not prove signed-parent
cancellation.
-/
import Gate1B.SafeExtensions.PhysicalSecondMoment
import Universal.SafeAlgebra.Homogeneity

namespace Gate1B.SafeExtensions

open Finset Universal.SafeAlgebra

variable {Rr Qq : Type*} [Fintype Rr] [Fintype Qq]

/-- **Asymmetric Cauchy, `β` coherent.**  The inner `q`-sum is never squared
coefficient-wise: it stays as one coherent complex number per `r`. -/
theorem asymmetricCauchy_left (delta : Rr → ℂ) (beta : Qq → ℂ) (K : Rr → Qq → ℂ) :
    ‖∑ r, delta r * ∑ q, beta q * K r q‖ ^ 2
      ≤ (∑ r, ‖delta r‖ ^ 2) * ∑ r, ‖∑ q, beta q * K r q‖ ^ 2 :=
  physicalOuterCauchy Finset.univ delta (fun r => ∑ q, beta q * K r q)

/-- **Asymmetric Cauchy, `δ` coherent.**  The mirror statement, squaring the
`β` family instead. -/
theorem asymmetricCauchy_right (delta : Rr → ℂ) (beta : Qq → ℂ) (K : Rr → Qq → ℂ) :
    ‖∑ q, beta q * ∑ r, delta r * K r q‖ ^ 2
      ≤ (∑ q, ‖beta q‖ ^ 2) * ∑ q, ‖∑ r, delta r * K r q‖ ^ 2 :=
  physicalOuterCauchy Finset.univ beta (fun q => ∑ r, delta r * K r q)

/-- The signed parent of a pair of finite families. -/
noncomputable def signedParent {ι : Type*} [Fintype ι] (sigma K : ι → ℂ) : ℂ := ∑ i, sigma i * K i

/-- The coefficient-blind energy of a pair of finite families. -/
noncomputable def coefficientBlindEnergy {ι : Type*} [Fintype ι] (sigma K : ι → ℂ) : ℝ :=
  ∑ i, ‖sigma i‖ ^ 2 * ‖K i‖ ^ 2

/-- **Exact signed cancellation.**  With `σ = (1,1)` and `K = (1,−1)` the signed
parent vanishes. -/
theorem signedParent_zero_counterexample :
    signedParent (fun _ : Fin 2 => (1 : ℂ)) (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1)
      = 0 := by
  simp [signedParent, Fin.sum_univ_two]

/-- …while the coefficient-blind energy of the very same data is `2 > 0`. -/
theorem coefficientBlindEnergy_positive_counterexample :
    coefficientBlindEnergy (fun _ : Fin 2 => (1 : ℂ))
      (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1) = 2 := by
  simp [coefficientBlindEnergy, Fin.sum_univ_two]
  norm_num

/-- **Double-Cauchy firewall.**  Two data sets with *identical* coefficient-blind
energies can have signed parents `0` and `2`.  Hence no coefficient-blind
quantity — in particular no bound obtained after squaring both outer sign
families — can detect, or recover, the cancellation present only in the coherent
signed combination. -/
theorem doubleCauchy_can_destroy_exact_signed_cancellation :
    ∃ sigma K K' : Fin 2 → ℂ,
      coefficientBlindEnergy sigma K = coefficientBlindEnergy sigma K' ∧
      signedParent sigma K = 0 ∧ signedParent sigma K' ≠ 0 := by
  refine ⟨fun _ => 1, fun i => if i = 0 then (1 : ℂ) else -1, fun _ => 1, ?_, ?_, ?_⟩
  · simp [coefficientBlindEnergy, Fin.sum_univ_two]
    norm_num
  · simp [signedParent, Fin.sum_univ_two]
  · simp [signedParent]

/-- **Compatibility with the banked v8.1 homogeneity family.**  Scaling the
signed-parent counterexample by `lam` keeps the parent zero and scales the
energy of the coefficient family by exactly `‖lam‖²`, exactly as
`quadraticEnergy_smul` predicts; combined with `noPositiveUniformEnergyFloor`
this shows the v8.1 `C₂`-floor guard and the v8.2 signed-parent guard are two
faces of the same safe-algebra fact. -/
theorem signedParentCounterexample_smul_energy (lam : ℂ) :
    signedParent (fun _ : Fin 2 => lam)
        (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1) = 0 ∧
      quadraticEnergy (Finset.univ : Finset (Fin 2)) (fun _ : Fin 2 => lam • (1 : ℂ))
        = ‖lam‖ ^ 2 * quadraticEnergy (Finset.univ : Finset (Fin 2)) (fun _ : Fin 2 => (1 : ℂ)) := by
  refine ⟨?_, quadraticEnergy_smul _ lam _⟩
  simp [signedParent, Fin.sum_univ_two]

end Gate1B.SafeExtensions
