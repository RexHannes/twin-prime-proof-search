/-
# NANC Gate 1A v9.1 — finite cyclic defect translations

For `w, f : ZMod n → ℂ` the **defect operator** is the translation (convolution)
operator

    (defectOp w f)(z) = ∑_r w r * f (z - r).

Everything here is finite: the additive phase is the standard additive character
`ZMod.stdAddChar`, and the orthogonality relation is the already-banked
`Gate1BDet2.Recip.sum_addPhase_mul` (reused, not restated).

Contents.

* `defectOp_character_eigen` — additive characters are exact eigenvectors, with
  eigenvalue the finite Fourier coefficient `dftHat w`.
* `dftHat_defectOp` — the convolution theorem.
* `dftHat_plancherel` — Plancherel: `∑_k |ŵ(k)|² = n · ∑_z |w z|²`.
* `defectOp_energy_le_fourierSup` / `defectOp_of_multiplierBound` — the operator
  energy bound `‖defectOp w f‖² ≤ C² ‖f‖²` from the Fourier multiplier bound
  `FourierMultiplierBound w C`.

**NO RAW `ℓ¹` CLAIM.**  `defectOp_l1_mass_not_canonical` exhibits, for every `n`,
a weight `w ≡ 1` with `ℓ¹`-mass exactly `n` whose defect operator annihilates
every mean-zero input.  Hence `∑_r |w r|` is *not* the canonical resource; the
safe interface is `FourierMultiplierBound`.
-/
import Mathlib
import RequestProject.NANC.Gate1BDet2.Det2AdditiveReciprocalFrame

namespace TwinPrimeProject.NANC.Gate1A.V91

open Finset TwinPrimeProject.Gate1BDet2.Recip

variable {n : ℕ} [NeZero n]

/-- The finite cyclic defect (translation/convolution) operator. -/
noncomputable def defectOp (w f : ZMod n → ℂ) (z : ZMod n) : ℂ := ∑ r : ZMod n, w r * f (z - r)

/-- The finite Fourier coefficient `ŵ(k) = ∑_r w r e_n(-r k)`. -/
noncomputable def dftHat (w : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  ∑ r : ZMod n, w r * addPhase n (-(r * k))

/-- **Characters are eigenvectors of the defect operator**, with eigenvalue
`ŵ(t)`. -/
theorem defectOp_character_eigen (w : ZMod n → ℂ) (t : ZMod n) :
    defectOp w (fun z => addPhase n (t * z)) = fun z => dftHat w t * addPhase n (t * z) := by
  funext z
  show (∑ r : ZMod n, w r * addPhase n (t * (z - r))) = dftHat w t * addPhase n (t * z)
  unfold dftHat
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : t * (z - r) = -(r * t) + t * z := by ring
  rw [this, addPhase_add]
  ring

/-- **Convolution theorem** for the finite defect operator. -/
theorem dftHat_defectOp (w f : ZMod n → ℂ) (k : ZMod n) :
    dftHat (defectOp w f) k = dftHat w k * dftHat f k := by
  classical
  unfold dftHat defectOp
  have hL : ∑ z : ZMod n, (∑ r : ZMod n, w r * f (z - r)) * addPhase n (-(z * k))
      = ∑ r : ZMod n, ∑ z : ZMod n, w r * f (z - r) * addPhase n (-(z * k)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => by rw [Finset.sum_mul]
  rw [hL]
  have hinner : ∀ r : ZMod n, ∑ z : ZMod n, w r * f (z - r) * addPhase n (-(z * k))
      = (w r * addPhase n (-(r * k))) * ∑ y : ZMod n, f y * addPhase n (-(y * k)) := by
    intro r
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight r) _ _ fun z => ?_
    have hz : -(z * k) = -(r * k) + -((z - r) * k) := by ring
    simp only [Equiv.subRight_apply]
    rw [hz, addPhase_add]
    ring
  rw [Finset.sum_congr rfl fun r _ => hinner r, ← Finset.sum_mul]

/-- Plancherel, complex form. -/
theorem dftHat_plancherel_complex (f : ZMod n → ℂ) :
    ∑ k : ZMod n, dftHat f k * (starRingEnd ℂ) (dftHat f k)
      = (n : ℂ) * ∑ j : ZMod n, f j * (starRingEnd ℂ) (f j) := by
  classical
  have hconj : ∀ x : ZMod n, (starRingEnd ℂ) (addPhase n x) = addPhase n (-x) := by
    intro x
    exact (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  have hexp : ∀ k : ZMod n, dftHat f k * (starRingEnd ℂ) (dftHat f k)
      = ∑ j : ZMod n, ∑ j' : ZMod n,
          f j * (starRingEnd ℂ) (f j') * addPhase n (k * (j' - j)) := by
    intro k
    unfold dftHat
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [map_mul, hconj]
    have : addPhase n (-(j * k)) * addPhase n (-(-(j' * k))) = addPhase n (k * (j' - j)) := by
      rw [← addPhase_add]
      congr 1
      ring
    calc f j * addPhase n (-(j * k)) * ((starRingEnd ℂ) (f j') * addPhase n (-(-(j' * k))))
        = f j * (starRingEnd ℂ) (f j') *
            (addPhase n (-(j * k)) * addPhase n (-(-(j' * k)))) := by ring
      _ = f j * (starRingEnd ℂ) (f j') * addPhase n (k * (j' - j)) := by rw [this]
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
  have : ∀ j : ZMod n, ∑ k : ZMod n, ∑ j' : ZMod n,
      f j * (starRingEnd ℂ) (f j') * addPhase n (k * (j' - j))
      = (n : ℂ) * (f j * (starRingEnd ℂ) (f j)) := by
    intro j
    rw [Finset.sum_comm]
    have hj' : ∀ j' : ZMod n, ∑ k : ZMod n, f j * (starRingEnd ℂ) (f j')
        * addPhase n (k * (j' - j))
        = f j * (starRingEnd ℂ) (f j') * (if j' - j = 0 then (n : ℂ) else 0) := by
      intro j'
      rw [← Finset.mul_sum, sum_addPhase_mul]
    rw [Finset.sum_congr rfl fun j' _ => hj' j']
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro j' _ hne
      have : j' - j ≠ 0 := sub_ne_zero_of_ne hne
      rw [if_neg this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum]

/-- **Plancherel** for the finite Fourier transform on `ZMod n`. -/
theorem dftHat_plancherel (f : ZMod n → ℂ) :
    ∑ k : ZMod n, ‖dftHat f k‖ ^ 2 = (n : ℝ) * ∑ j : ZMod n, ‖f j‖ ^ 2 := by
  have h := dftHat_plancherel_complex f
  have hL : ∑ k : ZMod n, dftHat f k * (starRingEnd ℂ) (dftHat f k)
      = ((∑ k : ZMod n, ‖dftHat f k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => Complex.mul_conj' _
  have hR : ∑ j : ZMod n, f j * (starRingEnd ℂ) (f j)
      = ((∑ j : ZMod n, ‖f j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun j _ => Complex.mul_conj' _
  rw [hL, hR] at h
  exact_mod_cast h

/-- **Fourier multiplier bound**: every character coefficient of the defect
weight has norm at most `C`.  This — not `∑_r |w r|` — is the canonical
resource. -/
def FourierMultiplierBound (w : ZMod n → ℂ) (C : ℝ) : Prop := ∀ k : ZMod n, ‖dftHat w k‖ ≤ C

/-- **Defect operator energy bound.**  If every Fourier coefficient of `w` has
norm at most `C`, then the defect operator contracts the energy by at most
`C²`. -/
theorem defectOp_energy_le_fourierSup (w f : ZMod n → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k : ZMod n, ‖dftHat w k‖ ≤ C) :
    ∑ z : ZMod n, ‖defectOp w f z‖ ^ 2 ≤ C ^ 2 * ∑ z : ZMod n, ‖f z‖ ^ 2 := by
  have hn : (0 : ℝ) < n := by
    have := NeZero.ne n
    exact_mod_cast Nat.pos_of_ne_zero this
  have key : (n : ℝ) * ∑ z : ZMod n, ‖defectOp w f z‖ ^ 2
      ≤ (n : ℝ) * (C ^ 2 * ∑ z : ZMod n, ‖f z‖ ^ 2) := by
    rw [← dftHat_plancherel (defectOp w f)]
    have hstep : ∀ k : ZMod n, ‖dftHat (defectOp w f) k‖ ^ 2 ≤ C ^ 2 * ‖dftHat f k‖ ^ 2 := by
      intro k
      rw [dftHat_defectOp, norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hw k) 2) (by positivity)
    calc ∑ k : ZMod n, ‖dftHat (defectOp w f) k‖ ^ 2
        ≤ ∑ k : ZMod n, C ^ 2 * ‖dftHat f k‖ ^ 2 := Finset.sum_le_sum fun k _ => hstep k
      _ = C ^ 2 * ∑ k : ZMod n, ‖dftHat f k‖ ^ 2 := by rw [Finset.mul_sum]
      _ = C ^ 2 * ((n : ℝ) * ∑ z : ZMod n, ‖f z‖ ^ 2) := by rw [dftHat_plancherel]
      _ = (n : ℝ) * (C ^ 2 * ∑ z : ZMod n, ‖f z‖ ^ 2) := by ring
  exact le_of_mul_le_mul_left key hn

/-- The same statement packaged through the `FourierMultiplierBound` interface. -/
theorem defectOp_of_multiplierBound (w f : ZMod n → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : FourierMultiplierBound w C) :
    ∑ z : ZMod n, ‖defectOp w f z‖ ^ 2 ≤ C ^ 2 * ∑ z : ZMod n, ‖f z‖ ^ 2 :=
  defectOp_energy_le_fourierSup w f C hC hw

/-! ## Guard: the `ℓ¹` mass is not the canonical resource -/

/-- With all translation coefficients equal to `1`, the defect operator is the
constant "total mass" operator. -/
theorem defectOp_const_one (f : ZMod n → ℂ) (z : ZMod n) :
    defectOp (fun _ => (1 : ℂ)) f z = ∑ y : ZMod n, f y := by
  unfold defectOp
  rw [show (∑ r : ZMod n, (1 : ℂ) * f (z - r)) = ∑ r : ZMod n, f (z - r) by
    exact Finset.sum_congr rfl fun r _ => one_mul _]
  exact Fintype.sum_equiv (Equiv.subLeft z) _ _ fun r => rfl

/-- **NO RAW FEJÉR `ℓ¹` CLAIM.**  The all-ones weight has `ℓ¹`-mass exactly `n`
— arbitrarily large — yet its defect operator annihilates every mean-zero
input.  Hence `∑_r |w r|` is not the canonical resource for the defect
multiplier; `FourierMultiplierBound` is. -/
theorem defectOp_l1_mass_not_canonical (f : ZMod n → ℂ) (hf : ∑ y : ZMod n, f y = 0) :
    (∑ r : ZMod n, ‖(1 : ℂ)‖ = (n : ℝ)) ∧
      (∀ z : ZMod n, defectOp (fun _ => (1 : ℂ)) f z = 0) := by
  refine ⟨by simp [Finset.card_univ, ZMod.card], fun z => ?_⟩
  rw [defectOp_const_one, hf]

end TwinPrimeProject.NANC.Gate1A.V91
