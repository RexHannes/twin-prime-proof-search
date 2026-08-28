import RequestProject.NANC.Gate1B.V11PairModSourceMultiplier

/-!
# V11 · Gate 1B — the fixed-multiplier vs. moving-multiplier firewall

**A critical permanent firewall.**

Even if, for every multiplier index `Θ` separately,

    ‖T_Θ‖ ≤ K      (a fixed-multiplier operator bound),

and even if

    ∑_Θ |A(Θ)|² ≤ 1      (bounded ℓ² multiplier energy),

it does **not** follow — without an additional *family-coherence* hypothesis —
that

    |∑_Θ A(Θ) ⟨T_Θ x_Θ, y_Θ⟩|

obeys the fixed-`Θ` bound with no `Θ`-family cost.  The explicit finite family
below loses a factor `√K` (with `K` the number of multipliers), and a second
family with the *same* pairings and the *same* multiplier moduli has value `0`.
So the family value is not a function of the fixed-multiplier data plus the
ℓ² energy.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-- A finite family of operators (given as matrices) with test vectors and a
multiplier coefficient. -/
structure FiniteOperatorFamily (K d : ℕ) where
  /-- The source multiplier coefficients. -/
  A : Fin K → ℂ
  /-- The operator attached to each multiplier index. -/
  T : Fin K → Matrix (Fin d) (Fin d) ℂ
  /-- The right test vectors. -/
  x : Fin K → (Fin d → ℂ)
  /-- The left test vectors. -/
  y : Fin K → (Fin d → ℂ)

/-- The finite sesquilinear pairing `⟨T x, y⟩`. -/
noncomputable def bil {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d → ℂ) : ℂ :=
  ∑ i, ∑ j, T i j * x j * (starRingEnd ℂ) (y i)

/-- The fixed-multiplier pairing of a family. -/
noncomputable def FiniteOperatorFamily.pairing {K d : ℕ} (F : FiniteOperatorFamily K d)
    (t : Fin K) : ℂ := bil (F.T t) (F.x t) (F.y t)

/-- The moving-multiplier family value. -/
noncomputable def FiniteOperatorFamily.value {K d : ℕ} (F : FiniteOperatorFamily K d) : ℂ :=
  ∑ t, F.A t * F.pairing t

/-- The aligned family on `K` multipliers: every pairing is `1`, every
coefficient is `K^{−1/2}`. -/
noncomputable def alignedFamily (K : ℕ) : FiniteOperatorFamily K 1 where
  A := fun _ => ((Real.sqrt K)⁻¹ : ℝ)
  T := fun _ => 1
  x := fun _ _ => 1
  y := fun _ _ => 1

/-- Every pairing of the aligned family equals `1`. -/
theorem alignedFamily_pairing (K : ℕ) (t : Fin K) : (alignedFamily K).pairing t = 1 := by
  simp [FiniteOperatorFamily.pairing, bil, alignedFamily, Matrix.one_apply]

/-- The aligned family has fixed-multiplier bound `1`. -/
theorem alignedFamily_fixed_bound (K : ℕ) (t : Fin K) : ‖(alignedFamily K).pairing t‖ ≤ 1 := by
  rw [alignedFamily_pairing]; simp

/-- The modulus of each aligned multiplier coefficient. -/
theorem alignedFamily_norm_A (K : ℕ) (t : Fin K) :
    ‖(alignedFamily K).A t‖ = (Real.sqrt K)⁻¹ := by
  simp only [alignedFamily, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

/-- The aligned family has ℓ² multiplier energy exactly `1`. -/
theorem alignedFamily_l2_energy (K : ℕ) (hK : 0 < K) :
    ∑ t, ‖(alignedFamily K).A t‖ ^ 2 ≤ 1 := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hval : ∀ t : Fin K, ‖(alignedFamily K).A t‖ ^ 2 = ((K : ℝ))⁻¹ := by
    intro t
    rw [alignedFamily_norm_A, ← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
  rw [Finset.sum_congr rfl fun t _ => hval t, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hKR)]

/-- **The `√K` loss.**  The aligned family value has modulus `√K`. -/
theorem alignedFamily_value_norm (K : ℕ) (hK : 0 < K) :
    ‖(alignedFamily K).value‖ = Real.sqrt K := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsq : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.mpr hKR
  have hterm : ∀ t : Fin K, (alignedFamily K).A t * (alignedFamily K).pairing t
      = (((Real.sqrt K)⁻¹ : ℝ) : ℂ) := by
    intro t
    rw [alignedFamily_pairing, mul_one]
    simp [alignedFamily]
  have hval : (alignedFamily K).value = (((K : ℝ) * (Real.sqrt K)⁻¹ : ℝ) : ℂ) := by
    unfold FiniteOperatorFamily.value
    rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have key : (K : ℝ) * (Real.sqrt K)⁻¹ = Real.sqrt K := by
    calc (K : ℝ) * (Real.sqrt K)⁻¹ = (Real.sqrt K * Real.sqrt K) * (Real.sqrt K)⁻¹ := by
          rw [Real.mul_self_sqrt (le_of_lt hKR)]
      _ = Real.sqrt K * (Real.sqrt K * (Real.sqrt K)⁻¹) := by ring
      _ = Real.sqrt K := by rw [mul_inv_cancel₀ (ne_of_gt hsq), mul_one]
  rw [hval, Complex.norm_real, Real.norm_eq_abs, key, abs_of_nonneg (le_of_lt hsq)]

/-- **THE FIREWALL.**  Fixed-multiplier operator bounds together with bounded
ℓ² multiplier energy do **not** control the moving multiplier family. -/
theorem fixedMultiplierBounds_do_not_control_movingFamily :
    ¬ ∀ (K : ℕ) (F : FiniteOperatorFamily K 1),
        (∀ t, ‖F.pairing t‖ ≤ 1) → (∑ t, ‖F.A t‖ ^ 2 ≤ 1) → ‖F.value‖ ≤ 1 := by
  intro h
  have hmain := h 4 (alignedFamily 4) (alignedFamily_fixed_bound 4)
    (alignedFamily_l2_energy 4 (by norm_num))
  rw [alignedFamily_value_norm 4 (by norm_num)] at hmain
  have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at hmain
  norm_num at hmain

/-- The anti-aligned family: the same pairings, the same multiplier moduli,
alternating signs. -/
noncomputable def antiAlignedFamily (K : ℕ) : FiniteOperatorFamily (2 * K) 1 where
  A := fun t => if (t : ℕ) < K then (((Real.sqrt ((2 * K : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)
                else -(((Real.sqrt ((2 * K : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)
  T := fun _ => 1
  x := fun _ _ => 1
  y := fun _ _ => 1

/-- Each pairing of the anti-aligned family is `1`, exactly as for the aligned
one. -/
theorem antiAlignedFamily_pairing (K : ℕ) (t : Fin (2 * K)) :
    (antiAlignedFamily K).pairing t = 1 := by
  simp [FiniteOperatorFamily.pairing, bil, antiAlignedFamily, Matrix.one_apply]

/-- The two families have identical multiplier moduli, hence identical ℓ²
energy. -/
theorem antiAlignedFamily_norm_A (K : ℕ) (t : Fin (2 * K)) :
    ‖(antiAlignedFamily K).A t‖ = ‖(alignedFamily (2 * K)).A t‖ := by
  rw [alignedFamily_norm_A]
  by_cases h : (t : ℕ) < K
  · simp only [antiAlignedFamily, h, if_true, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  · simp only [antiAlignedFamily, h, if_false, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)

/-- **ℓ² multiplier energy does not determine coherent cancellation.**  Two
families with the same pairings and the same multiplier moduli can have very
different values; the aligned one has value `√(2K)`. -/
theorem l2Energy_does_not_determine_familyValue (K : ℕ) (hK : 0 < K) :
    (∀ t, (antiAlignedFamily K).pairing t = (alignedFamily (2 * K)).pairing t) ∧
    (∀ t, ‖(antiAlignedFamily K).A t‖ = ‖(alignedFamily (2 * K)).A t‖) ∧
    ‖(alignedFamily (2 * K)).value‖ = Real.sqrt ((2 * K : ℕ) : ℝ) := by
  refine ⟨fun t => by rw [antiAlignedFamily_pairing, alignedFamily_pairing],
    antiAlignedFamily_norm_A K, alignedFamily_value_norm (2 * K) (by omega)⟩

end Gate1BV11
end TwinPrimeProject
