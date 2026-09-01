import Gate1B.FM722SecondAtomHardOpening
import Gate1B.PuncturedFourierFrame

/-!
# Gate 1B · FM722 · the **soft second-atom opening** (finite additive projector)

The soft alternative to the hard opening of `Gate1B.FM722SecondAtomHardOpening`.

For a positive modulus `y` the divisibility indicator is the finite additive
average

```
  1_{y ∣ n} = (1/y) ∑_{h mod y} e_y(h n) ,
```

which applied to `n = b₀ + ell s` gives the **soft-opening phase**

```
  1_{y ∣ b₀ + ell s} = (1/y) ∑_h e_y(h b₀) · e_y(h ell s) .
```

§4 splits the frequency sum exactly into its `h = 0` and `h ≠ 0` parts, kept as
separately named objects.

## Semantic guards

* A finite additive projector is an **identity**, not a cancellation theorem:
  no `h ≠ 0` saving is proved or assumed here, and no analytic owner is
  assigned to either part.
* Hard and soft openings are **not interchangeable** (§5): the hard opening
  multiplies the slope by `y` and rescales the line spacing, the soft opening
  keeps the slope `A` and introduces a frequency `h mod y`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier

/-! ## 1. The finite divisibility projector -/

/-- **FM722-LONGLINE-SOFT-DIVISIBILITY-PROJECTOR45.**  For a positive modulus
`y`, `1_{y ∣ n} = (1/y) ∑_{h mod y} e_y(h n)` in the `ℂ`-valued
normalisation. -/
theorem soft_divisibility_projector (y : ℕ) [NeZero y] (n : ℤ) :
    (if ((y : ℤ) ∣ n) then (1 : ℂ) else 0)
      = ((y : ℂ))⁻¹ * ∑ h : ZMod y, eM y (h * (n : ZMod y)) := by
  have hy : (y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne y)
  rw [full_char_sum ((n : ZMod y))]
  by_cases hdvd : ((y : ℤ) ∣ n)
  · have h0 : ((n : ZMod y)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd n y).mpr hdvd
    simp [hdvd, h0, hy]
  · have h0 : ((n : ZMod y)) ≠ 0 := fun h =>
      hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd n y).mp h)
    simp [hdvd, h0]

/-! ## 2. Soft opening of `b₀ + ell · s` -/

/-- **FM722-LONGLINE-SOFT-OPENING45.**  The projector applied to the line
value `n = b₀ + ell s`, in factored phase form. -/
theorem soft_opening_phase (y : ℕ) [NeZero y] (b0 ell s : ℤ) :
    (if ((y : ℤ) ∣ b0 + ell * s) then (1 : ℂ) else 0)
      = ((y : ℂ))⁻¹ *
          ∑ h : ZMod y, eM y (h * (b0 : ZMod y)) * eM y (h * ((ell : ZMod y) * (s : ZMod y))) := by
  rw [soft_divisibility_projector y (b0 + ell * s)]
  congr 1
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← eM_add]
  congr 1
  push_cast
  ring

/-! ## 3. The soft opening as a structure -/

/-- **`SoftSecondAtomOpening`.**  The result of a soft second-atom opening:
the slope `A` is *retained*, and a frequency variable `h mod y` is introduced.
Finite data plus a determinant certificate; no analytic field. -/
structure SoftSecondAtomOpening where
  /-- The retained slope. -/
  A : ℤ
  /-- The `b`-side slope. -/
  ell : ℤ
  /-- The modulus anchor. -/
  q0 : ℤ
  /-- The `b`-anchor. -/
  b0 : ℤ
  /-- The projector modulus (the second atom), as a positive natural number. -/
  yNat : ℕ
  /-- Positivity of the projector modulus. -/
  yPos : 0 < yNat
  /-- Oddness of the second atom. -/
  yOdd : Odd yNat
  /-- **Determinant certificate (unchanged slope).** -/
  det : A * b0 - ell * q0 = -2

namespace SoftSecondAtomOpening

variable (S : SoftSecondAtomOpening)

/-- **The soft opening retains the original slope.** -/
def retainedSlope : ℤ := S.A

@[simp] theorem retainedSlope_def : S.retainedSlope = S.A := rfl

/-- The soft opening introduces exactly `yNat` frequencies. -/
theorem frequency_count : Nat.card (ZMod S.yNat) = S.yNat := by
  simp [Nat.card_zmod]

end SoftSecondAtomOpening

/-! ## 4. The exact `h = 0` / `h ≠ 0` split -/

/-- The `h = 0` part of the soft opening (mass `1/y`, no phase). -/
noncomputable def softZeroPart (y : ℕ) : ℂ := ((y : ℂ))⁻¹

/-- The `h ≠ 0` part of the soft opening (pure phase sum, **no analytic owner
is assigned to it**). -/
noncomputable def softNonzeroPart (y : ℕ) [NeZero y] (n : ℤ) : ℂ :=
  ((y : ℂ))⁻¹ * ∑ h ∈ nzFreq y, eM y (h * (n : ZMod y))

/-- **FM722-LONGLINE-SOFT-ZERO-NONZERO-SPLIT45.**  The exact finite
decomposition of the soft opening into its zero and nonzero frequency parts. -/
theorem soft_zero_nonzero_split (y : ℕ) [NeZero y] (n : ℤ) :
    (if ((y : ℤ) ∣ n) then (1 : ℂ) else 0)
      = softZeroPart y + softNonzeroPart y n := by
  rw [soft_divisibility_projector y n, softZeroPart, softNonzeroPart, nzFreq,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod y))]
  simp only [zero_mul, eM_zero]
  ring

/-- The two parts are genuinely different objects: the zero part carries no
phase and no frequency, the nonzero part is a sum over `y − 1` frequencies. -/
theorem nzFreq_card (y : ℕ) [NeZero y] : (nzFreq y).card = y - 1 := by
  simp [nzFreq, Finset.card_erase_of_mem, ZMod.card]

/-! ## 5. The hard-versus-soft firewall -/

/-- The hard slope `A y` differs from the retained soft slope `A` whenever the
opened atom is not `1` and the slope is nonzero. -/
theorem hard_slope_ne_soft_slope (A y : ℤ) (hA : A ≠ 0) (hy : y ≠ 1) : A * y ≠ A := by
  intro h
  have : A * (y - 1) = 0 := by linarith [h]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hA h1
  · exact hy (by linarith)

/-- **HARD ≠ SOFT.**  A hard opening and a soft opening of the *same* datum are
different representations: the hard slope is `A y`, the soft slope is `A`, and
they disagree as soon as the atom is nontrivial. -/
theorem hard_soft_representations_differ (H : HardSecondAtomOpening)
    (S : SoftSecondAtomOpening) (hA : H.A = S.A) (hA0 : S.A ≠ 0) (hy : H.y ≠ 1) :
    H.newSlope ≠ S.retainedSlope := by
  simp only [HardSecondAtomOpening.newSlope_def, SoftSecondAtomOpening.retainedSlope_def, hA]
  exact hard_slope_ne_soft_slope S.A H.y hA0 hy

/-! ## 6. The deterministic soft compiler -/

/-- **FM722 soft second-atom data compiler (conditional, deterministic).**
Given two-atom incidence data with a positive natural presentation of the
second atom, this constructs the soft opening. -/
def compileSoft (I : TwoAtomIncidenceData) (yNat : ℕ) (hpos : 0 < yNat)
    (hodd : Odd yNat) : SoftSecondAtomOpening where
  A := I.A
  ell := I.ell
  q0 := I.q0
  b0 := I.b0
  yNat := yNat
  yPos := hpos
  yOdd := hodd
  det := I.det

/-- **Exact source reconstruction for the soft compiler.**  Over any finite set
of line parameters, the divisibility-restricted arithmetic sum equals the soft
frequency expansion.  This is an identity: no estimate is involved. -/
theorem compileSoft_reconstruction (I : TwoAtomIncidenceData) (yNat : ℕ) [NeZero yNat]
    (f : ℤ → ℂ) :
    ∑ s ∈ I.params, (if ((yNat : ℤ) ∣ I.bAt s) then f s else 0)
      = ((yNat : ℂ))⁻¹ *
          ∑ h : ZMod yNat, ∑ s ∈ I.params, f s * eM yNat (h * ((I.bAt s : ℤ) : ZMod yNat)) := by
  have hterm : ∀ s : ℤ,
      (if ((yNat : ℤ) ∣ I.bAt s) then f s else 0)
        = ((yNat : ℂ))⁻¹ * ∑ h : ZMod yNat, f s * eM yNat (h * ((I.bAt s : ℤ) : ZMod yNat)) := by
    intro s
    have h := soft_divisibility_projector yNat (I.bAt s)
    calc (if ((yNat : ℤ) ∣ I.bAt s) then f s else 0)
        = f s * (if ((yNat : ℤ) ∣ I.bAt s) then (1 : ℂ) else 0) := by
          by_cases hd : ((yNat : ℤ) ∣ I.bAt s) <;> simp [hd]
      _ = f s * (((yNat : ℂ))⁻¹ * ∑ h : ZMod yNat, eM yNat (h * ((I.bAt s : ℤ) : ZMod yNat))) := by
          rw [h]
      _ = ((yNat : ℂ))⁻¹ * ∑ h : ZMod yNat, f s * eM yNat (h * ((I.bAt s : ℤ) : ZMod yNat)) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.mul_sum, Finset.sum_comm]

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
