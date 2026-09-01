import Gate1B.FM722SecondAtomSoftProjector

/-!
# Gate 1B · FM722 · **centering scope of the long-line openings**

The physical packet on the long line is *centred*: it is

```
  centred = arithmetic line contribution − principal/model contribution .
```

This module proves that **both** second-atom openings — the hard fibre
reparametrisation and the soft additive projector — are deterministic linear
operations, so that

```
  T(arithmetic − model) = T(arithmetic) − T(model) .
```

The point is the *scope guard* of §3: the model may **not** be dropped before
the transformation.  Dropping it is not a linear operation and changes the
value; an explicit finite countermodel is proved.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier

/-! ## 1. The centred packet -/

/-- The centred packet: arithmetic contribution minus model contribution. -/
def centred (arith model : ℤ → ℂ) : ℤ → ℂ := fun s => arith s - model s

@[simp] theorem centred_apply (arith model : ℤ → ℂ) (s : ℤ) :
    centred arith model s = arith s - model s := rfl

/-! ## 2. The two transformations and their linearity -/

/-- The **hard** transformation: sum along the opened fibre `s = s₀ + y r`. -/
noncomputable def hardTransform (R : Finset ℤ) (s0 y : ℤ) (f : ℤ → ℂ) : ℂ :=
  ∑ r ∈ R, f (s0 + y * r)

/-- The **soft** transformation: the additive projector expansion over the
line parameter set `P` with `b`-values `b s`. -/
noncomputable def softTransform (P : Finset ℤ) (yNat : ℕ) [NeZero yNat] (b : ℤ → ℤ)
    (f : ℤ → ℂ) : ℂ :=
  ((yNat : ℂ))⁻¹ * ∑ h : ZMod yNat, ∑ s ∈ P, f s * eM yNat (h * ((b s : ℤ) : ZMod yNat))

/-- **Hard opening is linear on the centred packet.** -/
theorem hardTransform_centred (R : Finset ℤ) (s0 y : ℤ) (arith model : ℤ → ℂ) :
    hardTransform R s0 y (centred arith model)
      = hardTransform R s0 y arith - hardTransform R s0 y model := by
  simp [hardTransform, centred, Finset.sum_sub_distrib]

/-- **Soft opening is linear on the centred packet.** -/
theorem softTransform_centred (P : Finset ℤ) (yNat : ℕ) [NeZero yNat] (b : ℤ → ℤ)
    (arith model : ℤ → ℂ) :
    softTransform P yNat b (centred arith model)
      = softTransform P yNat b arith - softTransform P yNat b model := by
  simp only [softTransform, centred, sub_mul, Finset.sum_sub_distrib, mul_sub]

/-! ## 3. The centering scope guard -/

/-- **The model may not be dropped before transforming.**  Applying the hard
transformation to the arithmetic part alone is *not* the same as applying it to
the centred packet: an explicit finite countermodel. -/
theorem model_cannot_be_dropped_hard :
    ∃ (R : Finset ℤ) (s0 y : ℤ) (arith model : ℤ → ℂ),
      hardTransform R s0 y (centred arith model) ≠ hardTransform R s0 y arith := by
  refine ⟨{0}, 0, 1, (fun _ => 0), (fun _ => 1), ?_⟩
  simp [hardTransform, centred]

/-- The same guard for the soft transformation. -/
theorem model_cannot_be_dropped_soft :
    ∃ (P : Finset ℤ) (yNat : ℕ) (_ : NeZero yNat) (b : ℤ → ℤ) (arith model : ℤ → ℂ),
      softTransform P yNat b (centred arith model) ≠ softTransform P yNat b arith := by
  refine ⟨{0}, 1, ⟨one_ne_zero⟩, (fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
  simp [softTransform, centred]

/-- **Deterministic centering compiler.**  If both the arithmetic part and the
model part are transformed, the centred value is the difference of the two
transformed pieces — for either opening. -/
theorem centred_transform_pair (R P : Finset ℤ) (s0 y : ℤ) (yNat : ℕ) [NeZero yNat]
    (b : ℤ → ℤ) (arith model : ℤ → ℂ) :
    hardTransform R s0 y (centred arith model)
        = hardTransform R s0 y arith - hardTransform R s0 y model ∧
      softTransform P yNat b (centred arith model)
        = softTransform P yNat b arith - softTransform P yNat b model :=
  ⟨hardTransform_centred R s0 y arith model, softTransform_centred P yNat b arith model⟩

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
