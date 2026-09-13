/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
exact CRT phase normalisation  (B2)

Append-only module.  Everything here is exact modular algebra, kernel-proved; no analytic
statement occurs, nothing pre-existing is edited.

Setting (fixed shift `2` throughout — never averaged):  with `C = e·[d₁,d₂]`, `s = s_* + C t`,
and residues

```
α ≡ (s_* z + 2)(C z)⁻¹  (mod u),      β ≡ (s_* z' + 2)(C z')⁻¹  (mod v),
```

let `γ` be a CRT lift of `(α, β)` and put `J = C γ − s_*`.  §1 proves, at the level of integer
congruences (no complex exponentials),

```
z  · J ≡ 2   (mod u),        z' · J ≡ 2   (mod v),        J ≡ −s_*   (mod C),
```

together with the inverse forms `J ≡ 2 z⁻¹ (mod u)` and the CRT uniqueness statement
`C u v ∣ J₁ − J₂`.

§2 proves the **exact phase factorisation** in the additive circle `ℚ / ℤ`:

```
n(s_*/C − γ)/(uv)  ≡  n s_* (uv)⁻¹ / C  −  2n (C v z)⁻¹ / u  −  2n (C u z')⁻¹ / v   (mod 1),
```

§3 derives the complex-exponential form, and §4 contains the **firewall**: a finite instance in
which dropping the `C`-part of the phase changes the value in `ℚ / ℤ`, so the `C` contribution
may never be discarded.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Mathlib

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

/-! ## 1. The CRT lift and the three exact congruences -/

/-- `J = C γ − s_*`, the CRT-normalised numerator of the phase. -/
def shiftedJ (C γ s : ℤ) : ℤ := C * γ - s

/-- **`J ≡ 2 z⁻¹ (mod u)`, multiplicative form.**  From `(C z) α ≡ s_* z + 2 (mod u)` and
`γ ≡ α (mod u)`. -/
theorem J_modEq_u {u C s z α γ : ℤ} (hα : (C * z) * α ≡ s * z + 2 [ZMOD u])
    (hγ : γ ≡ α [ZMOD u]) : z * shiftedJ C γ s ≡ 2 [ZMOD u] := by
  have h1 : (C * z) * γ ≡ (C * z) * α [ZMOD u] := (Int.ModEq.refl (C * z)).mul hγ
  calc z * shiftedJ C γ s = (C * z) * γ - z * s := by unfold shiftedJ; ring
    _ ≡ (s * z + 2) - z * s [ZMOD u] := (h1.trans hα).sub (Int.ModEq.refl _)
    _ = 2 := by ring

/-- **`J ≡ 2 (z')⁻¹ (mod v)`, multiplicative form.** -/
theorem J_modEq_v {v C s z' β γ : ℤ} (hβ : (C * z') * β ≡ s * z' + 2 [ZMOD v])
    (hγ : γ ≡ β [ZMOD v]) : z' * shiftedJ C γ s ≡ 2 [ZMOD v] :=
  J_modEq_u hβ hγ

/-- **`J ≡ −s_* (mod C)`.** -/
theorem J_modEq_C {C γ s : ℤ} : shiftedJ C γ s ≡ -s [ZMOD C] :=
  Int.modEq_iff_dvd.mpr ⟨-γ, by unfold shiftedJ; ring⟩

/-- Cancellation of a unit: if `t w ≡ 1 (mod m)` and `m ∣ t a` then `m ∣ a`. -/
theorem dvd_of_unit_mul {m t w a : ℤ} (hw : t * w ≡ 1 [ZMOD m]) (h : m ∣ t * a) : m ∣ a := by
  have h0 : t * a ≡ 0 [ZMOD m] := (Int.modEq_zero_iff_dvd).mpr h
  have h1 : a ≡ (t * w) * a [ZMOD m] := by
    calc a = 1 * a := (one_mul a).symm
      _ ≡ (t * w) * a [ZMOD m] := (hw.symm).mul_right a
  have h2 : (t * w) * a ≡ 0 [ZMOD m] := by
    calc (t * w) * a = w * (t * a) := by ring
      _ ≡ w * 0 [ZMOD m] := (Int.ModEq.refl w).mul h0
      _ = 0 := by ring
  exact (Int.modEq_zero_iff_dvd).mp (h1.trans h2)

/-- **Inverse form of the `u`-congruence**: if `w` inverts `z` modulo `u` then
`J ≡ 2 w (mod u)`. -/
theorem J_modEq_u_inv {u C s z w γ : ℤ} (hw : z * w ≡ 1 [ZMOD u])
    (h : z * shiftedJ C γ s ≡ 2 [ZMOD u]) : shiftedJ C γ s ≡ 2 * w [ZMOD u] := by
  have h1 : u ∣ z * shiftedJ C γ s - 2 := Int.ModEq.dvd h.symm
  have h2 : u ∣ z * w - 1 := Int.ModEq.dvd hw.symm
  have h3 : u ∣ z * (shiftedJ C γ s - 2 * w) := by
    have hz : z * (shiftedJ C γ s - 2 * w) = (z * shiftedJ C γ s - 2) - 2 * (z * w - 1) := by
      ring
    rw [hz]
    exact dvd_sub h1 (h2.mul_left 2)
  have h4 : u ∣ shiftedJ C γ s - 2 * w := dvd_of_unit_mul hw h3
  have h5 : u ∣ 2 * w - shiftedJ C γ s := by
    have h := dvd_neg.mpr h4
    rwa [neg_sub] at h
  exact Int.modEq_iff_dvd.mpr h5

/-- Three pairwise-coprime moduli divide a common multiple. -/
theorem mul_dvd_of_three {C u v N : ℤ} (hCu : IsCoprime C u) (hCv : IsCoprime C v)
    (huv : IsCoprime u v) (hC : C ∣ N) (hu : u ∣ N) (hv : v ∣ N) : C * u * v ∣ N := by
  have huv' : u * v ∣ N := huv.mul_dvd hu hv
  have h : C * (u * v) ∣ N := (hCu.mul_right hCv).mul_dvd hC huv'
  rwa [← mul_assoc] at h

/-- **CRT uniqueness of the lift.**  Two integers satisfying the three exact congruences of §1
agree modulo `C u v`, provided `z`, `z'` are invertible mod `u`, `v` and the three moduli are
pairwise coprime.  Hence `J = C γ − s_*` *is* the CRT-normalised phase numerator. -/
theorem shiftedJ_unique {u v C s z z' w w' J₁ J₂ : ℤ}
    (hw : z * w ≡ 1 [ZMOD u]) (hw' : z' * w' ≡ 1 [ZMOD v])
    (hCu : IsCoprime C u) (hCv : IsCoprime C v) (huv : IsCoprime u v)
    (h1u : z * J₁ ≡ 2 [ZMOD u]) (h2u : z * J₂ ≡ 2 [ZMOD u])
    (h1v : z' * J₁ ≡ 2 [ZMOD v]) (h2v : z' * J₂ ≡ 2 [ZMOD v])
    (h1C : J₁ ≡ -s [ZMOD C]) (h2C : J₂ ≡ -s [ZMOD C]) :
    C * u * v ∣ J₁ - J₂ := by
  have hu : u ∣ J₁ - J₂ := by
    refine dvd_of_unit_mul hw ?_
    have hd : u ∣ z * J₂ - z * J₁ := Int.ModEq.dvd (h1u.trans h2u.symm)
    have : z * (J₁ - J₂) = -(z * J₂ - z * J₁) := by ring
    rw [this]
    exact (dvd_neg).mpr hd
  have hv : v ∣ J₁ - J₂ := by
    refine dvd_of_unit_mul hw' ?_
    have hd : v ∣ z' * J₂ - z' * J₁ := Int.ModEq.dvd (h1v.trans h2v.symm)
    have : z' * (J₁ - J₂) = -(z' * J₂ - z' * J₁) := by ring
    rw [this]
    exact (dvd_neg).mpr hd
  have hC : C ∣ J₁ - J₂ := by
    have hd : C ∣ J₂ - J₁ := Int.ModEq.dvd (h1C.trans h2C.symm)
    have : J₁ - J₂ = -(J₂ - J₁) := by ring
    rw [this]
    exact (dvd_neg).mpr hd
  exact mul_dvd_of_three hCu hCv huv hC hu hv

/-! ## 2. The exact phase factorisation in `ℚ / ℤ` -/

/-- Equality in the additive circle: two rationals differ by an integer. -/
def CongMod1 (a b : ℚ) : Prop := ∃ k : ℤ, a - b = (k : ℚ)

theorem CongMod1.refl (a : ℚ) : CongMod1 a a := ⟨0, by simp⟩

theorem CongMod1.symm {a b : ℚ} (h : CongMod1 a b) : CongMod1 b a := by
  obtain ⟨k, hk⟩ := h
  exact ⟨-k, by push_cast; linarith⟩

/-- The left-hand phase `n(s_*/C − γ)/(uv) = n(s_* − Cγ)/(C u v)`. -/
def phaseLHS (n s C γ u v : ℤ) : ℚ := ((n * (s - C * γ) : ℤ) : ℚ) / ((C * u * v : ℤ) : ℚ)

/-- The factorised phase `n s_* (uv)⁻¹ / C − 2n(Cvz)⁻¹/u − 2n(Cuz')⁻¹/v`. -/
def phaseRHS (n s P C A u B v : ℤ) : ℚ :=
  ((n * s * P : ℤ) : ℚ) / ((C : ℤ) : ℚ) - ((2 * n * A : ℤ) : ℚ) / ((u : ℤ) : ℚ)
    - ((2 * n * B : ℤ) : ℚ) / ((v : ℤ) : ℚ)

/-- **Exact phase factorisation.**  With `P` an inverse of `uv` mod `C`, `A` an inverse of
`C v z` mod `u`, `B` an inverse of `C u z'` mod `v`, and `J = Cγ − s_*` satisfying the `u`- and
`v`-congruences of §1, the two phases agree in `ℚ / ℤ`.  The `C`-part is *present*: see §4. -/
theorem phase_factorisation {n s C γ u v z z' P A B : ℤ}
    (hC0 : (C : ℚ) ≠ 0) (hu0 : (u : ℚ) ≠ 0) (hv0 : (v : ℚ) ≠ 0)
    (hCu : IsCoprime C u) (hCv : IsCoprime C v) (huv : IsCoprime u v)
    (hP : u * v * P ≡ 1 [ZMOD C]) (hA : (C * v * z) * A ≡ 1 [ZMOD u])
    (hB : (C * u * z') * B ≡ 1 [ZMOD v])
    (hJu : z * shiftedJ C γ s ≡ 2 [ZMOD u]) (hJv : z' * shiftedJ C γ s ≡ 2 [ZMOD v]) :
    CongMod1 (phaseLHS n s C γ u v) (phaseRHS n s P C A u B v) := by
  have hJC : shiftedJ C γ s ≡ -s [ZMOD C] := J_modEq_C
  -- the numerator whose divisibility by `C u v` is the whole content
  have hdC : C ∣ -(n * shiftedJ C γ s)
      - (n * s * P * u * v - 2 * n * A * C * v - 2 * n * B * C * u) := by
    have h1 : -(n * shiftedJ C γ s) ≡ -(n * -s) [ZMOD C] :=
      ((Int.ModEq.refl n).mul hJC).neg
    have h2 : n * s * P * u * v ≡ n * s * 1 [ZMOD C] := by
      calc n * s * P * u * v = (n * s) * (u * v * P) := by ring
        _ ≡ (n * s) * 1 [ZMOD C] := (Int.ModEq.refl (n * s)).mul hP
        _ = n * s * 1 := by ring
    have h3 : -(n * shiftedJ C γ s)
        - (n * s * P * u * v - 2 * n * A * C * v - 2 * n * B * C * u)
        ≡ (-(n * -s)) - (n * s * 1 - 2 * n * A * C * v - 2 * n * B * C * u) [ZMOD C] :=
      h1.sub ((h2.sub (Int.ModEq.refl (2 * n * A * C * v))).sub
        (Int.ModEq.refl (2 * n * B * C * u)))
    have h4 : (-(n * -s)) - (n * s * 1 - 2 * n * A * C * v - 2 * n * B * C * u)
        = C * (2 * n * A * v + 2 * n * B * u) := by ring
    rw [h4] at h3
    have h6 : C * (2 * n * A * v + 2 * n * B * u) ≡ 0 [ZMOD C] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨_, rfl⟩
    exact (Int.modEq_zero_iff_dvd).mp (h3.trans h6)
  have hdu : u ∣ -(n * shiftedJ C γ s)
      - (n * s * P * u * v - 2 * n * A * C * v - 2 * n * B * C * u) := by
    have hzu : z * (C * v * A) ≡ 1 [ZMOD u] := by
      have hrw : z * (C * v * A) = (C * v * z) * A := by ring
      rw [hrw]; exact hA
    refine dvd_of_unit_mul hzu ?_
    have hkey : z * (-(n * shiftedJ C γ s)
        - (n * s * P * u * v - 2 * n * A * C * v - 2 * n * B * C * u))
        = -(z * shiftedJ C γ s) * n + 2 * n * ((C * v * z) * A)
          - z * (n * s * P * u * v) + 2 * n * B * C * u * z := by ring
    rw [hkey]
    have h1 : -(z * shiftedJ C γ s) * n ≡ -(2 : ℤ) * n [ZMOD u] := (hJu.neg).mul_right n
    have h2 : 2 * n * ((C * v * z) * A) ≡ 2 * n * 1 [ZMOD u] :=
      (Int.ModEq.refl (2 * n)).mul hA
    have h3 : z * (n * s * P * u * v) ≡ 0 [ZMOD u] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨z * (n * s * P * v), by ring⟩
    have h4 : 2 * n * B * C * u * z ≡ 0 [ZMOD u] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨2 * n * B * C * z, by ring⟩
    have h5 : -(z * shiftedJ C γ s) * n + 2 * n * ((C * v * z) * A)
        - z * (n * s * P * u * v) + 2 * n * B * C * u * z
        ≡ (-(2 : ℤ) * n) + 2 * n * 1 - 0 + 0 [ZMOD u] := ((h1.add h2).sub h3).add h4
    have h6 : (-(2 : ℤ) * n) + 2 * n * 1 - 0 + 0 = 0 := by ring
    rw [h6] at h5
    exact (Int.modEq_zero_iff_dvd).mp h5
  have hdv : v ∣ -(n * shiftedJ C γ s)
      - (n * s * P * u * v - 2 * n * A * C * v - 2 * n * B * C * u) := by
    have hzv : z' * (C * u * B) ≡ 1 [ZMOD v] := by
      have hrw : z' * (C * u * B) = (C * u * z') * B := by ring
      rw [hrw]; exact hB
    refine dvd_of_unit_mul hzv ?_
    have hkey : z' * (-(n * shiftedJ C γ s)
        - (n * s * P * u * v - 2 * n * A * C * v - 2 * n * B * C * u))
        = -(z' * shiftedJ C γ s) * n + 2 * n * ((C * u * z') * B)
          - z' * (n * s * P * u * v) + 2 * n * A * C * v * z' := by ring
    rw [hkey]
    have h1 : -(z' * shiftedJ C γ s) * n ≡ -(2 : ℤ) * n [ZMOD v] := (hJv.neg).mul_right n
    have h2 : 2 * n * ((C * u * z') * B) ≡ 2 * n * 1 [ZMOD v] :=
      (Int.ModEq.refl (2 * n)).mul hB
    have h3 : z' * (n * s * P * u * v) ≡ 0 [ZMOD v] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨z' * (n * s * P * u), by ring⟩
    have h4 : 2 * n * A * C * v * z' ≡ 0 [ZMOD v] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨2 * n * A * C * z', by ring⟩
    have h5 : -(z' * shiftedJ C γ s) * n + 2 * n * ((C * u * z') * B)
        - z' * (n * s * P * u * v) + 2 * n * A * C * v * z'
        ≡ (-(2 : ℤ) * n) + 2 * n * 1 - 0 + 0 [ZMOD v] := ((h1.add h2).sub h3).add h4
    have h6 : (-(2 : ℤ) * n) + 2 * n * 1 - 0 + 0 = 0 := by ring
    rw [h6] at h5
    exact (Int.modEq_zero_iff_dvd).mp h5
  obtain ⟨k, hk⟩ := mul_dvd_of_three hCu hCv huv hdC hdu hdv
  refine ⟨k, ?_⟩
  have hkq : ((-(n * shiftedJ C γ s)
      - (n * s * P * u * v - 2 * n * A * C * v - 2 * n * B * C * u) : ℤ) : ℚ)
      = ((C * u * v : ℤ) : ℚ) * (k : ℚ) := by exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hk
  have hden : ((C * u * v : ℤ) : ℚ) ≠ 0 := by
    push_cast
    exact mul_ne_zero (mul_ne_zero hC0 hu0) hv0
  have hsplit : phaseLHS n s C γ u v - phaseRHS n s P C A u B v
      = ((-(n * shiftedJ C γ s)
        - (n * s * P * u * v - 2 * n * A * C * v - 2 * n * B * C * u) : ℤ) : ℚ)
        / ((C * u * v : ℤ) : ℚ) := by
    unfold phaseLHS phaseRHS shiftedJ
    push_cast
    field_simp
    ring
  rw [hsplit, hkq]
  field_simp

/-! ## 3. The complex-exponential form -/

/-- `e(t) = exp(2πi t)` for a rational phase `t`. -/
noncomputable def ee (t : ℚ) : ℂ := Complex.exp ((t : ℂ) * (2 * Real.pi * Complex.I))

/-- Phases equal in `ℚ / ℤ` have the same exponential. -/
theorem ee_congr {a b : ℚ} (h : CongMod1 a b) : ee a = ee b := by
  obtain ⟨k, hk⟩ := h
  have ha : (a : ℚ) = b + (k : ℚ) := by linarith
  have hc : (a : ℂ) = (b : ℂ) + (k : ℂ) := by exact_mod_cast congrArg (fun t : ℚ => (t : ℂ)) ha
  rw [ee, ee, hc, add_mul, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Additivity of the phase exponential. -/
theorem ee_add (a b : ℚ) : ee (a + b) = ee a * ee b := by
  rw [ee, ee, ee]
  push_cast
  rw [add_mul, Complex.exp_add]

/-- **Exponential form of the exact phase factorisation.** -/
theorem phase_factorisation_exp {n s C γ u v z z' P A B : ℤ}
    (hC0 : (C : ℚ) ≠ 0) (hu0 : (u : ℚ) ≠ 0) (hv0 : (v : ℚ) ≠ 0)
    (hCu : IsCoprime C u) (hCv : IsCoprime C v) (huv : IsCoprime u v)
    (hP : u * v * P ≡ 1 [ZMOD C]) (hA : (C * v * z) * A ≡ 1 [ZMOD u])
    (hB : (C * u * z') * B ≡ 1 [ZMOD v])
    (hJu : z * shiftedJ C γ s ≡ 2 [ZMOD u]) (hJv : z' * shiftedJ C γ s ≡ 2 [ZMOD v]) :
    ee (phaseLHS n s C γ u v)
      = ee (((n * s * P : ℤ) : ℚ) / ((C : ℤ) : ℚ)) * ee (-(((2 * n * A : ℤ) : ℚ) / ((u : ℤ) : ℚ)))
        * ee (-(((2 * n * B : ℤ) : ℚ) / ((v : ℤ) : ℚ))) := by
  have h := ee_congr (phase_factorisation (n := n) hC0 hu0 hv0 hCu hCv huv hP hA hB hJu hJv)
  rw [h]
  unfold phaseRHS
  rw [show ((n * s * P : ℤ) : ℚ) / ((C : ℤ) : ℚ) - ((2 * n * A : ℤ) : ℚ) / ((u : ℤ) : ℚ)
      - ((2 * n * B : ℤ) : ℚ) / ((v : ℤ) : ℚ)
      = (((n * s * P : ℤ) : ℚ) / ((C : ℤ) : ℚ) + -(((2 * n * A : ℤ) : ℚ) / ((u : ℤ) : ℚ)))
        + -(((2 * n * B : ℤ) : ℚ) / ((v : ℤ) : ℚ)) by ring, ee_add, ee_add]

/-! ## 4. Firewall: the `C` contribution may not be dropped -/

/-- **The `C`-part of the phase is not removable.**  In the finite instance
`n = s_* = 1`, `C = 3`, `u = v = 1`, `γ = 0`, `P = 1`, `A = B = 0`, the exact factorisation
holds, while the version with the `C`-term deleted is *false* in `ℚ / ℤ`: the two phases differ
by `1/3`. -/
theorem C_factor_not_removable :
    CongMod1 (phaseLHS 1 1 3 0 1 1) (phaseRHS 1 1 1 3 0 1 0 1)
      ∧ ¬ CongMod1 (phaseLHS 1 1 3 0 1 1)
          (-(((2 * 1 * 0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) - ((2 * 1 * 0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) := by
  constructor
  · refine ⟨0, ?_⟩
    unfold phaseLHS phaseRHS
    norm_num
  · rintro ⟨k, hk⟩
    unfold phaseLHS at hk
    norm_num at hk
    have h3 : (1 : ℚ) = 3 * (k : ℚ) := by linarith [hk]
    have hk3 : (1 : ℤ) = 3 * k := by exact_mod_cast h3
    omega

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
