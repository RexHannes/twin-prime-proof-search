import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-!
# Phase A4 / C1 · exact finite cyclic line-Fourier identities

**Everything here is an exact finite identity.**  No analytic Fourier estimate
is formalised, and no bound on any of the transforms is claimed.

The repository contains no pre-existing finite Parseval identity for the
line-frequency transforms (searched: `RANKONE`, `ENDPOINT`, Parseval), so the
exact cyclic version is proved here from Mathlib's `ZMod.dft`, with the
normalisation kept explicit:

  `Z_{u,ℓ}(k) = ∑_t β(z_t) · W₁(t) · e_H(-kt) = 𝓕 Φ k`,
  `B_{u,ℓ}(k) = ∑_t b₅(v_t) · W₂(t) · e_H(-kt) = 𝓕 Ψ k`,

with `Φ t = β(z_t) W₁(t)`, `Ψ t = b₅(v_t) W₂(t)` on `ZMod H`, and

  `M_{u,ℓ} = (1/H) ∑_k Z(k) conj(B(k)) = ∑_t Φ t · conj(Ψ t)`.

The coefficient sequences `β`, `b₅`, `W₁`, `W₂` are kept **abstract**: nothing
below depends on their arithmetic meaning.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FiniteLineFourier

open ZMod Finset

variable {H : ℕ} [NeZero H]

/-! ## 1. Orthogonality -/

/-- Exact additive-character orthogonality on `ZMod H`. -/
theorem sum_stdAddChar_mul (b : ZMod H) [DecidableEq (ZMod H)] :
    ∑ x : ZMod H, (ZMod.stdAddChar : AddChar (ZMod H) ℂ) (x * b)
      = (if b = 0 then (H : ℂ) else 0) := by
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar H)]
  split <;> simp [ZMod.card]

/-! ## 2. The line-frequency transforms -/

/-- The `z`-side line transform `Z_{u,ℓ}(k)`, with the normalisation made
explicit: it is the standard `ZMod H` discrete Fourier transform of
`t ↦ β (z t) · W₁ t`. -/
noncomputable def lineZ (beta : ℤ → ℂ) (z : ZMod H → ℤ) (W₁ : ZMod H → ℂ) :
    ZMod H → ℂ :=
  𝓕 (fun t => beta (z t) * W₁ t)

/-- The `v`-side line transform `B_{u,ℓ}(k)`. -/
noncomputable def lineB (b5 : ℤ → ℂ) (v : ZMod H → ℤ) (W₂ : ZMod H → ℂ) :
    ZMod H → ℂ :=
  𝓕 (fun t => b5 (v t) * W₂ t)

theorem lineZ_apply (beta : ℤ → ℂ) (z : ZMod H → ℤ) (W₁ : ZMod H → ℂ) (k : ZMod H) :
    lineZ beta z W₁ k =
      ∑ t : ZMod H, (ZMod.stdAddChar (-(t * k))) * (beta (z t) * W₁ t) := by
  simp [lineZ, ZMod.dft_apply]

/-! ## 3. Exact Parseval / Plancherel on `ZMod H` -/

/-- **Exact finite Parseval (polarised form).**

  `∑_k 𝓕f k · conj (𝓕g k) = H · ∑_j f j · conj (g j)`.

Kernel-checked; the normalisation `1/H` appears exactly once. -/
theorem dft_inner (f g : ZMod H → ℂ) :
    ∑ k : ZMod H, (𝓕 f k) * (starRingEnd ℂ) (𝓕 g k)
      = (H : ℂ) * ∑ j : ZMod H, f j * (starRingEnd ℂ) (g j) := by
  classical
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul,
    ← AddChar.map_neg_eq_conj, neg_neg]
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_mul_sum _ _ _ _)]
  rw [Finset.sum_comm]
  have step : ∀ j : ZMod H, ∑ k : ZMod H, ∑ l : ZMod H,
      (stdAddChar (-(j * k)) * f j) * (stdAddChar (l * k) * (starRingEnd ℂ) (g l))
      = (H : ℂ) * (f j * (starRingEnd ℂ) (g j)) := by
    intro j
    rw [Finset.sum_comm]
    have hin : ∀ l : ZMod H, ∑ k : ZMod H,
        (stdAddChar (-(j * k)) * f j) * (stdAddChar (l * k) * (starRingEnd ℂ) (g l))
        = (f j * (starRingEnd ℂ) (g l)) * (if l - j = 0 then (H : ℂ) else 0) := by
      intro l
      rw [← sum_stdAddChar_mul (l - j), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hchar : stdAddChar (k * (l - j))
          = stdAddChar (-(j * k)) * stdAddChar (l * k) := by
        rw [← AddChar.map_add_eq_mul]; ring_nf
      rw [hchar]; ring
    rw [Finset.sum_congr rfl (fun l _ => hin l), Finset.sum_eq_single j]
    · simp; ring
    · intro l _ hl; simp [sub_eq_zero, hl]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [Finset.sum_congr rfl (fun j _ => step j), ← Finset.mul_sum]

/-- **A4, the exact finite mixed moment.**  With the explicit `1/H`
normalisation,

  `M = (1/H) ∑_k Z(k) conj(B(k)) = ∑_t β(z_t)W₁(t) · conj(b₅(v_t)W₂(t))`. -/
theorem mixedMoment (beta b5 : ℤ → ℂ) (z v : ZMod H → ℤ) (W₁ W₂ : ZMod H → ℂ) :
    ((H : ℂ))⁻¹ * ∑ k : ZMod H, lineZ beta z W₁ k *
        (starRingEnd ℂ) (lineB b5 v W₂ k)
      = ∑ t : ZMod H, (beta (z t) * W₁ t) *
          (starRingEnd ℂ) (b5 (v t) * W₂ t) := by
  have hH : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne H)
  rw [lineZ, lineB, dft_inner, ← mul_assoc, inv_mul_cancel₀ hH, one_mul]

/-- **C1, Parseval for the `z`-side transform.** -/
theorem parseval_lineZ (beta : ℤ → ℂ) (z : ZMod H → ℤ) (W₁ : ZMod H → ℂ) :
    ((H : ℂ))⁻¹ * ∑ k : ZMod H, ((‖lineZ beta z W₁ k‖ : ℝ) : ℂ) ^ 2
      = ∑ t : ZMod H, ((‖beta (z t)‖ : ℝ) : ℂ) ^ 2 * ((‖W₁ t‖ : ℝ) : ℂ) ^ 2 := by
  have h := mixedMoment (H := H) beta beta z z W₁ W₁
  rw [show (lineB (H := H) beta z W₁) = lineZ beta z W₁ from rfl] at h
  simp only [Complex.mul_conj'] at h
  rw [h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [norm_mul]
  push_cast
  ring

/-- **C1, Parseval for the `v`-side transform.** -/
theorem parseval_lineB (b5 : ℤ → ℂ) (v : ZMod H → ℤ) (W₂ : ZMod H → ℂ) :
    ((H : ℂ))⁻¹ * ∑ k : ZMod H, ((‖lineB b5 v W₂ k‖ : ℝ) : ℂ) ^ 2
      = ∑ t : ZMod H, ((‖b5 (v t)‖ : ℝ) : ℂ) ^ 2 * ((‖W₂ t‖ : ℝ) : ℂ) ^ 2 :=
  parseval_lineZ b5 v W₂

/-! ## 4. Firewall: Parseval is not a cancellation mechanism (C2) -/

/-- **C2 COUNTERMODEL.**  Separate energy control of the two sides does *not*
produce signed cancellation in the mixed moment.  Two functions can each have
energy `1` per point while the mixed moment attains the trivial Cauchy–Schwarz
maximum: there is no saving.

Witness: `H = 1` is degenerate, so we take `H = 2`, `f = g = 1`.  Then
`(1/H)∑_k Z conj B = 2`, which equals `√(energy)·√(energy) = 2`. -/
theorem separate_energy_gives_no_cancellation :
    ∃ (f : ZMod 2 → ℂ),
      ((2 : ℂ))⁻¹ * ∑ k : ZMod 2, 𝓕 f k * (starRingEnd ℂ) (𝓕 f k)
        = ∑ t : ZMod 2, f t * (starRingEnd ℂ) (f t) ∧
      ∑ t : ZMod 2, f t * (starRingEnd ℂ) (f t) = 2 := by
  refine ⟨fun _ => 1, ?_, by simp⟩
  have := dft_inner (H := 2) (fun _ : ZMod 2 => (1 : ℂ)) (fun _ : ZMod 2 => (1 : ℂ))
  rw [this, ← mul_assoc]
  norm_num

end FiniteLineFourier
end CurrentProgramme
end TwinPrimeProject
