import Gate1B.FM722CenteredTwoFactorKloosterman

/-!
# Gate 1B · FM722 · exact **CRT factorisation** of the complete Kloosterman sum
and the centred CRT decomposition

Exact finite algebra plus the exact evaluation of the standard additive
character.  **No analytic estimate is proved or assumed**; in particular the
factorisation below is an identity, not a bound.

## Contents

* §1 Bézout data for a coprime pair, and the exact **character CRT identity**
  `e_{mp}(x) = e_m(x·v) e_p(x·u)` for `u m + v p = 1`;
* §2 the CRT bijection of unit groups and its two coordinate identities;
* §3 the **exact Kloosterman CRT factorisation**
  `S(a,b;mp) = S(a v, b v; m) · S(a u, b u; p)`
  with `v ≡ p⁻¹ (mod m)`, `u ≡ m⁻¹ (mod p)`;
* §4 finite **Ramanujan multiplicativity** `c_{mp}(k) = c_m(k) c_p(k)`,
  derived from §3;
* §5 the deterministic **centred CRT decomposition**
  `S_m S_p − R_m R_p = (S_m−R_m)(S_p−R_p) + R_m(S_p−R_p) + (S_m−R_m)R_p`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier
open TwinPrimeProject.CurrentProgramme.HStarCentered

/-! ## 1. Bézout data and the character CRT identity -/

/-- Bézout data for a coprime pair of moduli. -/
theorem exists_bezout (m p : ℕ) (h : Nat.Coprime m p) :
    ∃ u v : ℤ, u * (m : ℤ) + v * (p : ℤ) = 1 := by
  have hco : IsCoprime (m : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using h
  obtain ⟨u, v, huv⟩ := hco
  exact ⟨u, v, huv⟩

/-- **Character CRT identity.**  For `u m + v p = 1`,
`e_{mp}(x) = e_m(x v) · e_p(x u)`; here `v ≡ p⁻¹ (mod m)` and
`u ≡ m⁻¹ (mod p)`. -/
theorem eM_crt (m p : ℕ) [NeZero m] [NeZero p] (hm : (m : ℕ) ∣ m * p) (hp : (p : ℕ) ∣ m * p)
    (u v : ℤ) (huv : u * m + v * p = 1) (x : ZMod (m * p)) :
    haveI : NeZero (m * p) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne p)⟩
    eM (m * p) x
      = eM m (ZMod.castHom hm (ZMod m) x * (v : ZMod m))
        * eM p (ZMod.castHom hp (ZMod p) x * (u : ZMod p)) := by
  haveI : NeZero (m * p) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne p)⟩
  have hxint : ((x.val : ℤ) : ZMod (m * p)) = x := by push_cast; simp
  have hxm : ZMod.castHom hm (ZMod m) x * (v : ZMod m) = (((x.val : ℤ) * v : ℤ) : ZMod m) := by
    push_cast; simp [ZMod.natCast_val]
  have hxp : ZMod.castHom hp (ZMod p) x * (u : ZMod p) = (((x.val : ℤ) * u : ℤ) : ZMod p) := by
    push_cast; simp [ZMod.natCast_val]
  have hL : eM (m * p) x
      = Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℤ) : ℂ) / ((m * p : ℕ) : ℂ)) := by
    conv_lhs => rw [← hxint]
    exact ZMod.stdAddChar_coe (N := m * p) (x.val : ℤ)
  have hR1 : eM m (ZMod.castHom hm (ZMod m) x * (v : ZMod m))
      = Complex.exp (2 * Real.pi * Complex.I * ((((x.val : ℤ) * v : ℤ)) : ℂ) / (m : ℂ)) := by
    rw [hxm]; exact ZMod.stdAddChar_coe (N := m) _
  have hR2 : eM p (ZMod.castHom hp (ZMod p) x * (u : ZMod p))
      = Complex.exp (2 * Real.pi * Complex.I * ((((x.val : ℤ) * u : ℤ)) : ℂ) / (p : ℂ)) := by
    rw [hxp]; exact ZMod.stdAddChar_coe (N := p) _
  rw [hL, hR1, hR2, ← Complex.exp_add]
  congr 1
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have huvC : (u : ℂ) * (m : ℂ) + (v : ℂ) * (p : ℂ) = 1 := by exact_mod_cast huv
  push_cast
  field_simp
  linear_combination (-(((x.val : ℤ) : ℂ))) * huvC

/-! ## 2. The CRT bijection of unit groups -/

/-- The CRT bijection of unit groups. -/
noncomputable def crtUnits (m p : ℕ) [NeZero m] [NeZero p] (h : Nat.Coprime m p) :
    (ZMod (m * p))ˣ ≃* (ZMod m)ˣ × (ZMod p)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

theorem crtUnits_fst (m p : ℕ) [NeZero m] [NeZero p] (h : Nat.Coprime m p) (hm : (m : ℕ) ∣ m * p)
    (W : (ZMod (m * p))ˣ) :
    (((crtUnits m p h W).1 : (ZMod m)ˣ) : ZMod m)
      = ZMod.castHom hm (ZMod m) (W : ZMod (m * p)) := by
  simp [crtUnits, MulEquiv.prodUnits, ZMod.chineseRemainder]

theorem crtUnits_snd (m p : ℕ) [NeZero m] [NeZero p] (h : Nat.Coprime m p) (hp : (p : ℕ) ∣ m * p)
    (W : (ZMod (m * p))ˣ) :
    (((crtUnits m p h W).2 : (ZMod p)ˣ) : ZMod p)
      = ZMod.castHom hp (ZMod p) (W : ZMod (m * p)) := by
  simp [crtUnits, MulEquiv.prodUnits, ZMod.chineseRemainder]

theorem crtUnits_fst_inv (m p : ℕ) [NeZero m] [NeZero p] (h : Nat.Coprime m p)
    (hm : (m : ℕ) ∣ m * p) (W : (ZMod (m * p))ˣ) :
    ((((crtUnits m p h W).1)⁻¹ : (ZMod m)ˣ) : ZMod m)
      = ZMod.castHom hm (ZMod m) ((W⁻¹ : (ZMod (m * p))ˣ) : ZMod (m * p)) := by
  have hinv : ((crtUnits m p h W).1)⁻¹ = (crtUnits m p h W⁻¹).1 := by rw [map_inv]; rfl
  rw [hinv, crtUnits_fst]

theorem crtUnits_snd_inv (m p : ℕ) [NeZero m] [NeZero p] (h : Nat.Coprime m p)
    (hp : (p : ℕ) ∣ m * p) (W : (ZMod (m * p))ˣ) :
    ((((crtUnits m p h W).2)⁻¹ : (ZMod p)ˣ) : ZMod p)
      = ZMod.castHom hp (ZMod p) ((W⁻¹ : (ZMod (m * p))ˣ) : ZMod (m * p)) := by
  have hinv : ((crtUnits m p h W).2)⁻¹ = (crtUnits m p h W⁻¹).2 := by rw [map_inv]; rfl
  rw [hinv, crtUnits_snd]

/-! ## 3. The exact Kloosterman CRT factorisation -/

/-- **FM722-CENTERED-KLOOSTERMAN-CRT45 (Kloosterman half, kernel form).**

For coprime `m, p` and Bézout data `u m + v p = 1` (so `v ≡ p⁻¹ (mod m)` and
`u ≡ m⁻¹ (mod p)`),

```
  S(a, b; m p) = S(a v, b v; m) · S(a u, b u; p).
```
-/
theorem kloostermanSum_crt (m p : ℕ) [NeZero m] [NeZero p] (h : Nat.Coprime m p)
    (hm : (m : ℕ) ∣ m * p) (hp : (p : ℕ) ∣ m * p)
    (u v : ℤ) (huv : u * m + v * p = 1) (a b : ZMod (m * p)) :
    haveI : NeZero (m * p) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne p)⟩
    kloostermanSum (m * p) a b
      = kloostermanSum m (ZMod.castHom hm (ZMod m) a * (v : ZMod m))
            (ZMod.castHom hm (ZMod m) b * (v : ZMod m))
        * kloostermanSum p (ZMod.castHom hp (ZMod p) a * (u : ZMod p))
            (ZMod.castHom hp (ZMod p) b * (u : ZMod p)) := by
  haveI : NeZero (m * p) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne p)⟩
  classical
  rw [kloostermanSum_eq_units, kloostermanSum_eq_units, kloostermanSum_eq_units]
  set F : (ZMod m)ˣ → ℂ := fun z =>
    eM m ((ZMod.castHom hm (ZMod m) a * (v : ZMod m)) * (z : ZMod m)
      + (ZMod.castHom hm (ZMod m) b * (v : ZMod m)) * ((z⁻¹ : (ZMod m)ˣ) : ZMod m)) with hF
  set G : (ZMod p)ˣ → ℂ := fun z =>
    eM p ((ZMod.castHom hp (ZMod p) a * (u : ZMod p)) * (z : ZMod p)
      + (ZMod.castHom hp (ZMod p) b * (u : ZMod p)) * ((z⁻¹ : (ZMod p)ˣ) : ZMod p)) with hG
  have hRHS : (∑ z1 : (ZMod m)ˣ, F z1) * (∑ z2 : (ZMod p)ˣ, G z2)
      = ∑ w : (ZMod m)ˣ × (ZMod p)ˣ, F w.1 * G w.2 := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [hRHS]
  refine Fintype.sum_equiv (crtUnits m p h).toEquiv _ _ ?_
  intro W
  show eM (m * p) _ = F ((crtUnits m p h W).1) * G ((crtUnits m p h W).2)
  rw [eM_crt m p hm hp u v huv]
  congr 1
  · rw [hF]
    simp only [map_add, map_mul]
    rw [crtUnits_fst m p h hm W, crtUnits_fst_inv m p h hm W]
    congr 1
    ring
  · rw [hG]
    simp only [map_add, map_mul]
    rw [crtUnits_snd m p h hp W, crtUnits_snd_inv m p h hp W]
    congr 1
    ring

/-! ## 4. Finite Ramanujan multiplicativity -/

/-- `v` is a unit mod `m` and `u` is a unit mod `p`. -/
theorem bezout_units (m p : ℕ) [NeZero m] [NeZero p] (u v : ℤ) (huv : u * m + v * p = 1) :
    IsUnit ((v : ZMod m)) ∧ IsUnit ((u : ZMod p)) := by
  constructor
  · have hmul : (v : ZMod m) * ((p : ℤ) : ZMod m) = 1 := by
      have h1 : ((u * m + v * p : ℤ) : ZMod m) = ((1 : ℤ) : ZMod m) := by rw [huv]
      push_cast at h1 ⊢
      simpa using h1
    exact IsUnit.of_mul_eq_one _ hmul
  · have hmul : (u : ZMod p) * ((m : ℤ) : ZMod p) = 1 := by
      have h1 : ((u * m + v * p : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) := by rw [huv]
      push_cast at h1 ⊢
      simpa using h1
    exact IsUnit.of_mul_eq_one _ hmul

/-- **Finite Ramanujan multiplicativity**, derived from the Kloosterman CRT
factorisation: `c_{mp}(k) = c_m(k) c_p(k)` for coprime `m, p`. -/
theorem ramanujanSum_crt (m p : ℕ) [NeZero m] [NeZero p] (h : Nat.Coprime m p)
    (hm : (m : ℕ) ∣ m * p) (hp : (p : ℕ) ∣ m * p) (k : ZMod (m * p)) :
    haveI : NeZero (m * p) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne p)⟩
    ramanujanSum (m * p) k
      = ramanujanSum m (ZMod.castHom hm (ZMod m) k) * ramanujanSum p (ZMod.castHom hp (ZMod p) k) := by
  haveI : NeZero (m * p) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne p)⟩
  obtain ⟨u, v, huv⟩ := exists_bezout m p h
  obtain ⟨hv, hu⟩ := bezout_units m p u v huv
  have hcrt := kloostermanSum_crt m p h hm hp u v huv k 0
  rw [kloostermanSum_zero_right] at hcrt
  simp only [map_zero, zero_mul] at hcrt
  rw [kloostermanSum_zero_right, kloostermanSum_zero_right] at hcrt
  rw [hcrt]
  rw [show (ZMod.castHom hm (ZMod m) k * (v : ZMod m))
      = ZMod.castHom hm (ZMod m) k * (hv.unit : ZMod m) by rw [IsUnit.unit_spec]]
  rw [show (ZMod.castHom hp (ZMod p) k * (u : ZMod p))
      = ZMod.castHom hp (ZMod p) k * (hu.unit : ZMod p) by rw [IsUnit.unit_spec]]
  rw [ramanujanSum_unit_mul, ramanujanSum_unit_mul]

/-! ## 5. The centred CRT decomposition -/

/-- The centred principal kernel `R_c(k,j) = c_c(k) c_c(j)/φ(c)`. -/
noncomputable def centeredPrincipalKernel (c : ℕ) [NeZero c] (k j : ZMod c) : ℂ :=
  ramanujanSum c k * ramanujanSum c j / (c.totient : ℂ)

/-- **Deterministic centred CRT algebra.**  Purely formal; no analytic claim. -/
theorem centered_crt_decomposition (Sm Sp Rm Rp : ℂ) :
    Sm * Sp - Rm * Rp
      = (Sm - Rm) * (Sp - Rp) + Rm * (Sp - Rp) + (Sm - Rm) * Rp := by ring

/-- The centred CRT decomposition applied to the Kloosterman/Ramanujan data of
two coprime moduli. -/
theorem centered_crt_decomposition_applied (m p : ℕ) [NeZero m] [NeZero p]
    (am bm km jm : ZMod m) (ap bp kp jp : ZMod p) :
    kloostermanSum m am bm * kloostermanSum p ap bp
        - centeredPrincipalKernel m km jm * centeredPrincipalKernel p kp jp
      = (kloostermanSum m am bm - centeredPrincipalKernel m km jm)
          * (kloostermanSum p ap bp - centeredPrincipalKernel p kp jp)
        + centeredPrincipalKernel m km jm
          * (kloostermanSum p ap bp - centeredPrincipalKernel p kp jp)
        + (kloostermanSum m am bm - centeredPrincipalKernel m km jm)
          * centeredPrincipalKernel p kp jp :=
  centered_crt_decomposition _ _ _ _

end FM722
end CurrentProgramme
end TwinPrimeProject
