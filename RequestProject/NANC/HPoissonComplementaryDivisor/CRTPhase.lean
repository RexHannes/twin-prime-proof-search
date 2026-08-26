import Mathlib

/-!
# HPoissonComplementaryDivisor, Module 1: CRT and the additive inverse phase

Finite arithmetic only.  Nothing analytic is asserted or assumed here.

Setting.  `q₁, q₂` are nonzero integers with `IsCoprime (q₁ : ℤ) q₂`, and
`v₁, v₂` are integers that are units modulo `q₁`, `q₂` respectively.  A CRT
solution `w` satisfies `w ≡ v₁ [ZMOD q₁]` and `w ≡ v₂ [ZMOD q₂]`.

Contents.

* `crt_exists`, `crt_unique`, `crt_existsUnique_mod` : existence and
  uniqueness of `w` modulo `q₁ * q₂`.
* `crt_isCoprime_mul` : a CRT solution is a unit modulo `c = q₁ q₂`.
* `inv_congr_of_congr` : if `w ≡ v [ZMOD q]` then any inverse of `w` mod `q`
  is an inverse of `v` mod `q`, and conversely; inverses are unique mod `q`.
* `crt_inverse_decomposition` : the *integer* form of the additive phase
  identity, `w̄ ≡ a₁ b₂ q₂ + a₂ b₁ q₁ [ZMOD q₁ q₂]`.
* `crt_phase_identity` : the rational phase identity
  `(-2h w̄)/(q₁q₂) ≡ (-2h a₁ b₂)/q₁ + (-2h a₂ b₁)/q₂ (mod 1)`.

Every coprimality hypothesis is stated explicitly.  No statement here is
extended to the case `(q₁, q₂) > 1`.
-/

namespace TwinPrimeProject
namespace HPoissonCD

/-! ## 1. Chinese remainder: existence and uniqueness -/

/-- **CRT existence.**  For coprime moduli `q₁, q₂` and arbitrary residues
`v₁, v₂` there is a simultaneous solution `w`. -/
theorem crt_exists {q₁ q₂ : ℤ} (hq : IsCoprime q₁ q₂) (v₁ v₂ : ℤ) :
    ∃ w : ℤ, w ≡ v₁ [ZMOD q₁] ∧ w ≡ v₂ [ZMOD q₂] := by
  obtain ⟨a, b, hab⟩ := hq
  refine ⟨v₂ * (a * q₁) + v₁ * (b * q₂), ?_, ?_⟩
  · exact Int.modEq_iff_dvd.mpr ⟨v₁ * a - v₂ * a, by linear_combination (-v₁) * hab⟩
  · exact Int.modEq_iff_dvd.mpr ⟨v₂ * b - v₁ * b, by linear_combination (-v₂) * hab⟩

/-- **CRT uniqueness.**  Two simultaneous solutions agree modulo `q₁ * q₂`. -/
theorem crt_unique {q₁ q₂ w w' : ℤ} (hq : IsCoprime q₁ q₂)
    (h₁ : w ≡ w' [ZMOD q₁]) (h₂ : w ≡ w' [ZMOD q₂]) :
    w ≡ w' [ZMOD q₁ * q₂] := by
  have d₁ : q₁ ∣ w' - w := Int.modEq_iff_dvd.mp h₁
  have d₂ : q₂ ∣ w' - w := Int.modEq_iff_dvd.mp h₂
  exact Int.modEq_iff_dvd.mpr (hq.mul_dvd d₁ d₂)

/-- **CRT existence and uniqueness modulo `q₁ q₂`.** -/
theorem crt_existsUnique_mod {q₁ q₂ : ℤ} (hq : IsCoprime q₁ q₂) (v₁ v₂ : ℤ) :
    ∃ w : ℤ, (w ≡ v₁ [ZMOD q₁] ∧ w ≡ v₂ [ZMOD q₂]) ∧
      ∀ w' : ℤ, (w' ≡ v₁ [ZMOD q₁] ∧ w' ≡ v₂ [ZMOD q₂]) → w' ≡ w [ZMOD q₁ * q₂] := by
  obtain ⟨w, hw₁, hw₂⟩ := crt_exists hq v₁ v₂
  refine ⟨w, ⟨hw₁, hw₂⟩, fun w' hw' => crt_unique hq ?_ ?_⟩
  · exact hw'.1.trans hw₁.symm
  · exact hw'.2.trans hw₂.symm

/-! ## 2. Units and inverses -/

/-- A CRT solution inherits coprimality to each modulus. -/
theorem isCoprime_of_congr {q v w : ℤ} (hv : IsCoprime v q) (hw : w ≡ v [ZMOD q]) :
    IsCoprime w q := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hw
  obtain ⟨a, b, hab⟩ := hv
  refine ⟨a, b + a * k, ?_⟩
  have hv' : v = w + q * k := by linarith
  rw [hv'] at hab
  linarith [hab]

/-- **A CRT solution is a unit modulo `c = q₁ q₂`.** -/
theorem crt_isCoprime_mul {q₁ q₂ v₁ v₂ w : ℤ}
    (hv₁ : IsCoprime v₁ q₁) (hv₂ : IsCoprime v₂ q₂)
    (hw₁ : w ≡ v₁ [ZMOD q₁]) (hw₂ : w ≡ v₂ [ZMOD q₂]) :
    IsCoprime w (q₁ * q₂) :=
  (isCoprime_of_congr hv₁ hw₁).mul_right (isCoprime_of_congr hv₂ hw₂)

/-- Existence of an inverse modulo `q` for a unit. -/
theorem exists_inv_of_isCoprime {q v : ℤ} (hv : IsCoprime v q) :
    ∃ x : ℤ, v * x ≡ 1 [ZMOD q] := by
  obtain ⟨a, b, hab⟩ := hv
  refine ⟨a, Int.modEq_iff_dvd.mpr ⟨b, ?_⟩⟩
  linarith [hab]

/-- Inverses modulo `q` are unique modulo `q`. -/
theorem inv_unique {q v x y : ℤ} (hv : IsCoprime v q)
    (hx : v * x ≡ 1 [ZMOD q]) (hy : v * y ≡ 1 [ZMOD q]) : x ≡ y [ZMOD q] := by
  have h : v * (x - y) ≡ 0 [ZMOD q] := by simpa [mul_sub] using hx.sub hy
  have hd : q ∣ (x - y) * v := by rw [mul_comm]; exact (Int.modEq_zero_iff_dvd).mp h
  have h2 : q ∣ x - y := hv.symm.dvd_of_dvd_mul_right hd
  exact Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp h2)

/-- **Inverse transfer along a congruence.**  If `w ≡ v [ZMOD q]` then `x` is
an inverse of `w` mod `q` iff it is an inverse of `v` mod `q`. -/
theorem inv_congr_of_congr {q v w x : ℤ} (hw : w ≡ v [ZMOD q]) :
    (w * x ≡ 1 [ZMOD q]) ↔ (v * x ≡ 1 [ZMOD q]) := by
  constructor
  · intro h; exact ((hw.symm.mul_right x).trans h)
  · intro h; exact ((hw.mul_right x).trans h)

/-- If `w ≡ v [ZMOD q]`, `v` is a unit mod `q`, `w̄` inverts `w` and `a`
inverts `v`, then `w̄ ≡ a [ZMOD q]`.  This is statement (2) of Module 1. -/
theorem inv_congr_inv {q v w wbar a : ℤ} (hv : IsCoprime v q)
    (hw : w ≡ v [ZMOD q]) (hwbar : w * wbar ≡ 1 [ZMOD q]) (ha : v * a ≡ 1 [ZMOD q]) :
    wbar ≡ a [ZMOD q] :=
  inv_unique hv ((inv_congr_of_congr hw).mp hwbar) ha

/-! ## 3. The additive CRT inverse decomposition -/

/-- **Integer form of the additive inverse phase identity.**

Hypotheses (all explicit): `q₁, q₂` coprime; `v₁, v₂` units mod `q₁, q₂`;
`w` a CRT solution; `wbar` an inverse of `w` mod `q₁q₂`; `a₁` an inverse of
`v₁` mod `q₁`; `a₂` an inverse of `v₂` mod `q₂`; `b₂` an inverse of `q₂`
mod `q₁`; `b₁` an inverse of `q₁` mod `q₂`.  Then

`wbar ≡ a₁ * b₂ * q₂ + a₂ * b₁ * q₁  [ZMOD q₁ * q₂]`. -/
theorem crt_inverse_decomposition {q₁ q₂ v₁ v₂ w wbar a₁ a₂ b₁ b₂ : ℤ}
    (hq : IsCoprime q₁ q₂) (hv₁ : IsCoprime v₁ q₁) (hv₂ : IsCoprime v₂ q₂)
    (hw₁ : w ≡ v₁ [ZMOD q₁]) (hw₂ : w ≡ v₂ [ZMOD q₂])
    (hwbar : w * wbar ≡ 1 [ZMOD q₁ * q₂])
    (ha₁ : v₁ * a₁ ≡ 1 [ZMOD q₁]) (ha₂ : v₂ * a₂ ≡ 1 [ZMOD q₂])
    (hb₂ : q₂ * b₂ ≡ 1 [ZMOD q₁]) (hb₁ : q₁ * b₁ ≡ 1 [ZMOD q₂]) :
    wbar ≡ a₁ * b₂ * q₂ + a₂ * b₁ * q₁ [ZMOD q₁ * q₂] := by
  -- reduce mod q₁
  have h₁ : wbar ≡ a₁ * b₂ * q₂ + a₂ * b₁ * q₁ [ZMOD q₁] := by
    have hwb₁ : w * wbar ≡ 1 [ZMOD q₁] := hwbar.of_dvd ⟨q₂, rfl⟩
    have hstep : wbar ≡ a₁ [ZMOD q₁] := inv_congr_inv hv₁ hw₁ hwb₁ ha₁
    refine hstep.trans ?_
    have : a₁ * b₂ * q₂ + a₂ * b₁ * q₁ ≡ a₁ * (q₂ * b₂) + a₂ * b₁ * 0 [ZMOD q₁] := by
      have h0 : q₁ ≡ 0 [ZMOD q₁] := (Int.modEq_zero_iff_dvd).mpr dvd_rfl
      exact ((Int.ModEq.refl (a₁ * b₂ * q₂)).add ((Int.ModEq.refl (a₂ * b₁)).mul h0)).trans
        (by ring_nf; rfl)
    refine (this.trans ?_).symm
    calc a₁ * (q₂ * b₂) + a₂ * b₁ * 0 ≡ a₁ * 1 + a₂ * b₁ * 0 [ZMOD q₁] :=
          ((Int.ModEq.refl a₁).mul hb₂).add (Int.ModEq.refl _)
      _ = a₁ := by ring
  -- reduce mod q₂
  have h₂ : wbar ≡ a₁ * b₂ * q₂ + a₂ * b₁ * q₁ [ZMOD q₂] := by
    have hwb₂ : w * wbar ≡ 1 [ZMOD q₂] := hwbar.of_dvd ⟨q₁, mul_comm q₁ q₂⟩
    have hstep : wbar ≡ a₂ [ZMOD q₂] := inv_congr_inv hv₂ hw₂ hwb₂ ha₂
    refine hstep.trans ?_
    have : a₁ * b₂ * q₂ + a₂ * b₁ * q₁ ≡ a₁ * b₂ * 0 + a₂ * (q₁ * b₁) [ZMOD q₂] := by
      have h0 : q₂ ≡ 0 [ZMOD q₂] := (Int.modEq_zero_iff_dvd).mpr dvd_rfl
      exact (((Int.ModEq.refl (a₁ * b₂)).mul h0).add (Int.ModEq.refl (a₂ * b₁ * q₁))).trans
        (by ring_nf; rfl)
    refine (this.trans ?_).symm
    calc a₁ * b₂ * 0 + a₂ * (q₁ * b₁) ≡ a₁ * b₂ * 0 + a₂ * 1 [ZMOD q₂] :=
          (Int.ModEq.refl _).add ((Int.ModEq.refl a₂).mul hb₁)
      _ = a₂ := by ring
  exact crt_unique hq h₁ h₂

/-- **The additive CRT phase identity, rational form.**

Under the hypotheses of `crt_inverse_decomposition` and `q₁ q₂ ≠ 0`,

`(-2h·w̄)/(q₁q₂) - ((-2h·a₁b₂)/q₁ + (-2h·a₂b₁)/q₂) ∈ ℤ`,

i.e. the two phases agree modulo `1`. -/
theorem crt_phase_identity {q₁ q₂ v₁ v₂ w wbar a₁ a₂ b₁ b₂ : ℤ} (h : ℤ)
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hq : IsCoprime q₁ q₂) (hv₁ : IsCoprime v₁ q₁) (hv₂ : IsCoprime v₂ q₂)
    (hw₁ : w ≡ v₁ [ZMOD q₁]) (hw₂ : w ≡ v₂ [ZMOD q₂])
    (hwbar : w * wbar ≡ 1 [ZMOD q₁ * q₂])
    (ha₁ : v₁ * a₁ ≡ 1 [ZMOD q₁]) (ha₂ : v₂ * a₂ ≡ 1 [ZMOD q₂])
    (hb₂ : q₂ * b₂ ≡ 1 [ZMOD q₁]) (hb₁ : q₁ * b₁ ≡ 1 [ZMOD q₂]) :
    ∃ k : ℤ,
      ((-2 * h * wbar : ℚ) / ((q₁ : ℚ) * (q₂ : ℚ)))
        - (((-2 * h * a₁ * b₂ : ℚ)) / (q₁ : ℚ) + ((-2 * h * a₂ * b₁ : ℚ)) / (q₂ : ℚ))
        = (k : ℚ) := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp
    (crt_inverse_decomposition hq hv₁ hv₂ hw₁ hw₂ hwbar ha₁ ha₂ hb₂ hb₁)
  -- ht : a₁ * b₂ * q₂ + a₂ * b₁ * q₁ - wbar = q₁ * q₂ * t
  refine ⟨2 * h * t, ?_⟩
  have hq₁' : (q₁ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hq₁
  have hq₂' : (q₂ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hq₂
  have htQ : (a₁ : ℚ) * b₂ * q₂ + (a₂ : ℚ) * b₁ * q₁ - wbar = (q₁ : ℚ) * q₂ * t := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) ht
  push_cast
  field_simp
  linear_combination ((h : ℚ)) * htQ

end HPoissonCD
end TwinPrimeProject
