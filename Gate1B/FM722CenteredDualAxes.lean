import Gate1B.FM722CenteredTwoFactorKloosterman

/-!
# Gate 1B · FM722 · **dual-axes vanishing** of the centred Kloosterman kernel

Exact finite algebra.  No analytic estimate.

**FM722-DUAL-AXES-ZERO45 (kernel form).**  For `2` invertible mod `q` and `π` a
unit mod `q`,

```
  K_q(0,j;π) = 0,        K_q(k,0;π) = 0.
```

This is load-bearing: it is exactly the statement that the centred two-factor
completion has no zero-frequency axis contribution, so that both frequency
variables of the completed sum may be taken nonzero.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier
open TwinPrimeProject.CurrentProgramme.HStarCentered

variable {q : ℕ} [NeZero q]

/-- **Vanishing on the `k = 0` axis.** -/
theorem centeredKloostermanKernel_zero_left (h2 : IsUnit (2 : ZMod q)) (j : ZMod q)
    (pi : (ZMod q)ˣ) : centeredKloostermanKernel q 0 j pi = 0 := by
  classical
  rw [centeredKloostermanKernel, kloostermanSum_zero_left, ramanujanSum_zero]
  set v : (ZMod q)ˣ := -(h2.unit * pi⁻¹) with hv
  have hvval : (v : ZMod q) = -(2 * ((pi⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
    rw [hv]
    simp [IsUnit.unit_spec]
  have hrw : (-2 * j * ((pi⁻¹ : (ZMod q)ˣ) : ZMod q)) = j * (v : ZMod q) := by
    rw [hvval]; ring
  rw [hrw, ramanujanSum_unit_mul]
  have hcancel : (q.totient : ℂ) * ramanujanSum q j / (q.totient : ℂ) = ramanujanSum q j := by
    have hphi := totient_cast_ne_zero q
    field_simp
  rw [hcancel, sub_self]

/-- **Vanishing on the `j = 0` axis.** -/
theorem centeredKloostermanKernel_zero_right (k : ZMod q) (pi : (ZMod q)ˣ) :
    centeredKloostermanKernel q k 0 pi = 0 := by
  classical
  rw [centeredKloostermanKernel]
  rw [show (-2 * (0 : ZMod q) * ((pi⁻¹ : (ZMod q)ˣ) : ZMod q)) = 0 by ring]
  rw [kloostermanSum_zero_right, ramanujanSum_zero]
  have hcancel : ramanujanSum q k * (q.totient : ℂ) / (q.totient : ℂ) = ramanujanSum q k := by
    have hphi := totient_cast_ne_zero q
    field_simp
  rw [hcancel, sub_self]

/-- **Dual-axes zero, joint form.** -/
theorem centeredKloostermanKernel_dual_axes_zero (h2 : IsUnit (2 : ZMod q))
    (k j : ZMod q) (pi : (ZMod q)ˣ) :
    centeredKloostermanKernel q 0 j pi = 0 ∧ centeredKloostermanKernel q k 0 pi = 0 :=
  ⟨centeredKloostermanKernel_zero_left h2 j pi, centeredKloostermanKernel_zero_right k pi⟩

/-- Consequently the completed two-factor sum is supported on the **punctured**
frequency square `k ≠ 0`, `j ≠ 0`: every term of the completed sum with a zero
frequency coordinate vanishes. -/
theorem twoFactor_axis_terms_vanish (h2 : IsUnit (2 : ZMod q))
    (alpha gamma : ZMod q → ℂ) (k j : ZMod q) (pi : (ZMod q)ˣ) :
    dftHat q alpha 0 * dftHat q gamma j * centeredKloostermanKernel q 0 j pi = 0 ∧
      dftHat q alpha k * dftHat q gamma 0 * centeredKloostermanKernel q k 0 pi = 0 := by
  constructor
  · rw [centeredKloostermanKernel_zero_left h2 j pi, mul_zero]
  · rw [centeredKloostermanKernel_zero_right k pi, mul_zero]

end FM722
end CurrentProgramme
end TwinPrimeProject
