/-
# Gate-1A: the exact cross-`q` side-2 sign (Section 4)

We start from the authoritative UNSQUARED form

```
Z_q(k) = ∑_{t mod q} e_q(-t (k + r⁻¹ m)) · Y_q(t r⁻²)
```

and ask what happens to the frequency variables when `Z_{q1}(k)` is multiplied
by `conj Z_{q2}(k)` for coprime `q1, q2` and `Q = q1 q2`.

The authoritative CRT frequency relation is

```
t ≡ t1 q2 − t2 q1   (mod Q),
```

whose exact consequences are

```
t1 ≡ + t · q2⁻¹ (mod q1),
t2 ≡ − t · q1⁻¹ (mod q2).
```

The **minus sign on side 2** is kernel-checked below
(`crt_side2_inverse_negative`), and the old "plus/plus" dictionary is refuted
(`old_plus_plus_cross_q_false`).
-/
import Mathlib

namespace Gate1A

open Finset

namespace CRTSign

/-! ## Integer-level frequency relation -/

/-- Reduction of the authoritative frequency relation modulo `q1` and `q2`. -/
theorem crt_frequency_relation_int (q1 q2 : ℕ) (T T1 T2 : ℤ)
    (h : T ≡ T1 * q2 - T2 * q1 [ZMOD ((q1 : ℤ) * q2)]) :
    (T ≡ T1 * q2 [ZMOD (q1 : ℤ)]) ∧ (T ≡ -(T2 * q1) [ZMOD (q2 : ℤ)]) := by
  constructor
  · have h1 : T ≡ T1 * q2 - T2 * q1 [ZMOD (q1 : ℤ)] :=
      h.of_dvd ⟨(q2 : ℤ), rfl⟩
    have h2 : T1 * q2 - T2 * q1 ≡ T1 * q2 [ZMOD (q1 : ℤ)] := by
      have : (q1 : ℤ) ∣ (T1 * q2 - T2 * q1) - T1 * q2 := ⟨-T2, by ring⟩
      exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr this)
    exact h1.trans h2
  · have h1 : T ≡ T1 * q2 - T2 * q1 [ZMOD (q2 : ℤ)] :=
      h.of_dvd ⟨(q1 : ℤ), by ring⟩
    have h2 : T1 * q2 - T2 * q1 ≡ -(T2 * q1) [ZMOD (q2 : ℤ)] := by
      have : (q2 : ℤ) ∣ (T1 * q2 - T2 * q1) - (-(T2 * q1)) := ⟨T1, by ring⟩
      exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr this)
    exact h1.trans h2

/-- **Side 1 dictionary (positive).** `t1 ≡ + t q2⁻¹ (mod q1)`. -/
theorem crt_side1_inverse (q1 q2 : ℕ) (T T1 U2 : ℤ)
    (hU2 : (q2 : ℤ) * U2 ≡ 1 [ZMOD (q1 : ℤ)])
    (hT : T ≡ T1 * q2 [ZMOD (q1 : ℤ)]) :
    T1 ≡ T * U2 [ZMOD (q1 : ℤ)] := by
  have h1 : T * U2 ≡ (T1 * q2) * U2 [ZMOD (q1 : ℤ)] := hT.mul_right U2
  have h2 : (T1 * q2) * U2 = T1 * ((q2 : ℤ) * U2) := by ring
  have h3 : T1 * ((q2 : ℤ) * U2) ≡ T1 * 1 [ZMOD (q1 : ℤ)] := hU2.mul_left T1
  exact ((h1.trans (h2 ▸ h3)).trans (by simp)).symm

/-- **Side 2 dictionary (NEGATIVE).** `t2 ≡ − t q1⁻¹ (mod q2)`.

This is the load-bearing sign. -/
theorem crt_side2_inverse_negative (q1 q2 : ℕ) (T T2 U1 : ℤ)
    (hU1 : (q1 : ℤ) * U1 ≡ 1 [ZMOD (q2 : ℤ)])
    (hT : T ≡ -(T2 * q1) [ZMOD (q2 : ℤ)]) :
    T2 ≡ -(T * U1) [ZMOD (q2 : ℤ)] := by
  have h1 : T * U1 ≡ (-(T2 * q1)) * U1 [ZMOD (q2 : ℤ)] := hT.mul_right U1
  have h2 : -(T * U1) ≡ -((-(T2 * q1)) * U1) [ZMOD (q2 : ℤ)] := h1.neg
  have h3 : -((-(T2 * q1)) * U1) = T2 * ((q1 : ℤ) * U1) := by ring
  have h4 : T2 * ((q1 : ℤ) * U1) ≡ T2 * 1 [ZMOD (q2 : ℤ)] := hU1.mul_left T2
  exact ((h2.trans (h3 ▸ h4)).trans (by simp)).symm

/-- **Retraction of the old plus/plus cross-`q` form.**  The two dictionaries
`t2 ≡ − t q1⁻¹` and `t2 ≡ + t q1⁻¹` genuinely differ: at `q1 = 2, q2 = 3,
t = 1, q1⁻¹ = 2` they give `1` and `2` modulo `3`. -/
theorem old_plus_plus_cross_q_false :
    ∃ (q1 q2 : ℕ) (T U1 : ℤ), Nat.Coprime q1 q2 ∧
      ((q1 : ℤ) * U1 ≡ 1 [ZMOD (q2 : ℤ)]) ∧ ¬ (-(T * U1) ≡ T * U1 [ZMOD (q2 : ℤ)]) := by
  refine ⟨2, 3, 1, 2, by decide, ?_, ?_⟩
  · decide
  · decide

/-! ## ZMod-level reconstruction of the cross sum -/

variable {q1 q2 : ℕ} [NeZero q1] [NeZero q2]

instance neZeroMulPair : NeZero (q1 * q2) :=
  ⟨Nat.mul_ne_zero (NeZero.ne q1) (NeZero.ne q2)⟩

/-- Reduction `ZMod (q1 q2) → ZMod q1`. -/
abbrev red1 (q1 q2 : ℕ) : ZMod (q1 * q2) →+* ZMod q1 :=
  ZMod.castHom ⟨q2, rfl⟩ (ZMod q1)

/-- Reduction `ZMod (q1 q2) → ZMod q2`. -/
abbrev red2 (q1 q2 : ℕ) : ZMod (q1 * q2) →+* ZMod q2 :=
  ZMod.castHom ⟨q1, mul_comm q1 q2⟩ (ZMod q2)

/-- The CRT reparametrisation of the frequency pair with the **correct**
side-2 sign: `t ↦ (a₁ t mod q1, −a₂ t mod q2)`. -/
noncomputable def crtSide2Equiv (h : Nat.Coprime q1 q2)
    (a1 : (ZMod q1)ˣ) (a2 : (ZMod q2)ˣ) :
    ZMod (q1 * q2) ≃ ZMod q1 × ZMod q2 :=
  (ZMod.chineseRemainder h).toEquiv.trans
    { toFun := fun p => ((a1 : ZMod q1) * p.1, -((a2 : ZMod q2) * p.2))
      invFun := fun p => (((a1⁻¹ : (ZMod q1)ˣ) : ZMod q1) * p.1,
        -(((a2⁻¹ : (ZMod q2)ˣ) : ZMod q2) * p.2))
      left_inv := by
        rintro ⟨x, y⟩
        simp [Units.inv_mul_cancel_left]
      right_inv := by
        rintro ⟨x, y⟩
        simp [Units.mul_inv_cancel_left] }

omit [NeZero q1] [NeZero q2] in
theorem crtSide2Equiv_fst (h : Nat.Coprime q1 q2)
    (a1 : (ZMod q1)ˣ) (a2 : (ZMod q2)ˣ) (t : ZMod (q1 * q2)) :
    (crtSide2Equiv h a1 a2 t).1 = (a1 : ZMod q1) * red1 q1 q2 t := by
  simp [crtSide2Equiv, ZMod.chineseRemainder, ZMod.castHom_apply]

omit [NeZero q1] [NeZero q2] in
theorem crtSide2Equiv_snd (h : Nat.Coprime q1 q2)
    (a1 : (ZMod q1)ˣ) (a2 : (ZMod q2)ˣ) (t : ZMod (q1 * q2)) :
    (crtSide2Equiv h a1 a2 t).2 = -((a2 : ZMod q2) * red2 q1 q2 t) := by
  simp [crtSide2Equiv, ZMod.chineseRemainder, ZMod.castHom_apply]

/-- **`cross_q_side2_negative`.**  The cross product of two one-`q` frequency
sums is reconstructed as a single sum over `t mod q1 q2`, in which side 1 is
evaluated at `+ a₁ t` and side 2 at `− a₂ t`.

Applied with `F1 t1 = e_{q1}(-t1 c1) Y_{q1}(t1 u1)` and
`F2 t2 = conj(e_{q2}(-t2 c2) Y_{q2}(t2 u2))` this is exactly the statement that
the cross sum reconstructs `Y_{q1}(t·unit1) · conj Y_{q2}(−t·unit2)`. -/
theorem cross_q_side2_negative (h : Nat.Coprime q1 q2)
    (a1 : (ZMod q1)ˣ) (a2 : (ZMod q2)ˣ)
    (F1 : ZMod q1 → ℂ) (F2 : ZMod q2 → ℂ) :
    (∑ t1 : ZMod q1, F1 t1) * (∑ t2 : ZMod q2, F2 t2)
      = ∑ t : ZMod (q1 * q2),
          F1 ((a1 : ZMod q1) * red1 q1 q2 t) * F2 (-((a2 : ZMod q2) * red2 q1 q2 t)) := by
  classical
  have hcard := Fintype.sum_equiv (crtSide2Equiv h a1 a2)
    (fun t => F1 ((crtSide2Equiv h a1 a2 t).1) * F2 ((crtSide2Equiv h a1 a2 t).2))
    (fun p : ZMod q1 × ZMod q2 => F1 p.1 * F2 p.2) (fun t => rfl)
  rw [Finset.sum_mul_sum]
  rw [show (∑ i : ZMod q1, ∑ j : ZMod q2, F1 i * F2 j)
      = ∑ p : ZMod q1 × ZMod q2, F1 p.1 * F2 p.2 from
    (Fintype.sum_prod_type (fun p : ZMod q1 × ZMod q2 => F1 p.1 * F2 p.2)).symm]
  rw [← hcard]
  exact Finset.sum_congr rfl fun t _ => by
    simp only [crtSide2Equiv_fst, crtSide2Equiv_snd]

end CRTSign

end Gate1A
