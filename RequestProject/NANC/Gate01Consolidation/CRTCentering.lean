import RequestProject.NANC.Gate01Consolidation.NonzeroOrthogonality

/-!
# BANK D / E / T — CRT centering and the product frequency parametrisation

* **BANK D (natural centering).**  `ρ_q(y) = 1_{q ∣ y} − 1/q` and the exact
  identity `ρ_{dp} = ρ_d ρ_p + ρ_d/p + ρ_p/d` for coprime `d, p`
  (`rho_mul_coprime`, CRT-CENTER).
* **BANK E (abstract source densities).**  `ρ^src_d(y) = 1_{d ∣ y} − δ_d`, and
  under the *hypothesis* `δ_{dp} = δ_d δ_p` (DENS-MULT, never instantiated) the
  identity CRT-SRC (`rhoSrc_mul_coprime`).
* **BANK T (product-frequency CRT isometry).**  The map
  `(a_d, a_p) ↦ a_d p + a_p d (mod dp)` is a bijection
  `ZMod d × ZMod p ≃ ZMod (dp)` for coprime `d, p` (`crtFreq_bijective`), the
  frequencies add exactly (`crtFreq_rat`), and the additive characters agree
  (`ec_crt_split`).  The frequency mode classification of BANK D is
  `CRTMode` / `crtMode`.

No analytic size statement is proved anywhere in this module; in particular
nothing here asserts a large-sieve gain, and nothing asserts that the
double-centered covariance is small.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-! ## Natural centering -/

/-- Natural centering weight `ρ_q(y) = 1_{q ∣ y} − 1/q`. -/
noncomputable def rho (q : ℕ) (y : ℕ) : ℝ := (if q ∣ y then (1 : ℝ) else 0) - 1 / q

/-- The indicator of `d p ∣ y` factorises for coprime `d, p`. -/
theorem indicator_mul_coprime {d p : ℕ} (h : Nat.Coprime d p) (y : ℕ) :
    (if d * p ∣ y then (1 : ℝ) else 0)
      = (if d ∣ y then (1 : ℝ) else 0) * (if p ∣ y then (1 : ℝ) else 0) := by
  by_cases hd : d ∣ y
  · by_cases hp : p ∣ y
    · rw [if_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd h hd hp), if_pos hd, if_pos hp, mul_one]
    · rw [if_neg, if_pos hd, if_neg hp, mul_zero]
      exact fun hc => hp ((dvd_mul_left p d).trans hc)
  · rw [if_neg, if_neg hd, zero_mul]
    exact fun hc => hd ((dvd_mul_right d p).trans hc)

/-- **CRT-CENTER.**  For coprime `d, p > 0`,
`ρ_{dp}(y) = ρ_d(y) ρ_p(y) + ρ_d(y)/p + ρ_p(y)/d`. -/
theorem rho_mul_coprime {d p : ℕ} (hd : 0 < d) (hp : 0 < p) (h : Nat.Coprime d p) (y : ℕ) :
    rho (d * p) y = rho d y * rho p y + rho d y / p + rho p y / d := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  unfold rho
  rw [indicator_mul_coprime h y]
  push_cast
  field_simp
  ring

/-! ## Abstract source densities -/

/-- Source-centered weight `ρ^src_q(y) = 1_{q ∣ y} − δ`. -/
noncomputable def rhoSrc (q : ℕ) (delta : ℝ) (y : ℕ) : ℝ :=
  (if q ∣ y then (1 : ℝ) else 0) - delta

/-- **DENS-MULT.**  The multiplicativity premise for the source densities.
This is *not* source-proved; it only ever occurs as a hypothesis. -/
def DensityMultiplicative (deltad deltap deltadp : ℝ) : Prop := deltadp = deltad * deltap

/-- **CRT-SRC.**  Under DENS-MULT and coprimality,
`ρ^src_{dp} = ρ^src_d ρ^src_p + δ_p ρ^src_d + δ_d ρ^src_p`. -/
theorem rhoSrc_mul_coprime {d p : ℕ} (h : Nat.Coprime d p)
    {deltad deltap deltadp : ℝ} (hmul : DensityMultiplicative deltad deltap deltadp) (y : ℕ) :
    rhoSrc (d * p) deltadp y
      = rhoSrc d deltad y * rhoSrc p deltap y
        + deltap * rhoSrc d deltad y + deltad * rhoSrc p deltap y := by
  unfold rhoSrc
  rw [indicator_mul_coprime h y, hmul]
  ring

/-! ## Product-frequency CRT parametrisation (BANK T) -/

/-- The CRT frequency parametrisation `(a_d, a_p) ↦ a_d p + a_p d (mod dp)`. -/
def crtFreq (d p : ℕ) (ab : ZMod d × ZMod p) : ZMod (d * p) :=
  ((ab.1.val * p + ab.2.val * d : ℕ) : ZMod (d * p))

/-- **CRT frequency bijection.**  For coprime `d, p > 0` the parametrisation is
a bijection: separate `(d, p)` additive frequencies contain exactly as many raw
frequency points as frequencies modulo `dp`. -/
theorem crtFreq_bijective {d p : ℕ} (hd : 0 < d) (hp : 0 < p) (h : Nat.Coprime d p) :
    Function.Bijective (crtFreq d p) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  haveI : NeZero p := ⟨hp.ne'⟩
  haveI : NeZero (d * p) := ⟨Nat.mul_ne_zero hd.ne' hp.ne'⟩
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hEq
    unfold crtFreq at hEq
    have hd1 := congrArg (ZMod.castHom (dvd_mul_right d p) (ZMod d)) hEq
    have hp1 := congrArg (ZMod.castHom (Dvd.intro_left d rfl) (ZMod p)) hEq
    simp only [map_natCast] at hd1 hp1
    push_cast at hd1 hp1
    simp only [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self, add_zero, mul_zero,
      zero_add] at hd1 hp1
    have hup : IsUnit ((p : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime p d).mpr h.symm
    have hud : IsUnit ((d : ℕ) : ZMod p) := (ZMod.isUnit_iff_coprime d p).mpr h
    exact Prod.ext (hup.mul_right_cancel hd1) (hud.mul_right_cancel hp1)
  · simp [ZMod.card]

/-- The exact rational frequency addition underlying the parametrisation:
`a_d/d + a_p/p = (a_d p + a_p d)/(dp)`. -/
theorem crtFreq_rat {d p : ℕ} (hd : 0 < d) (hp : 0 < p) (ad ap : ℤ) :
    (ad : ℚ) / d + (ap : ℚ) / p = ((ad * p + ap * d : ℤ) : ℚ) / ((d * p : ℕ) : ℚ) := by
  have hdR : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hpR : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  push_cast
  field_simp

/-- The additive characters agree under the CRT frequency parametrisation:
`e_{dp}((a_d p + a_p d) y) = e_d(a_d y) e_p(a_p y)`. -/
theorem ec_crt_split {d p : ℕ} (hd : 0 < d) (hp : 0 < p) (ad ap y : ℤ) :
    ec (d * p) ((ad * p + ap * d) * y) = ec d (ad * y) * ec p (ap * y) := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  unfold ec
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp

/-! ## Frequency mode classification -/

/-- The four CRT frequency modes. -/
inductive CRTMode
  /-- Both components are nonzero: the double-centered product mode. -/
  | doubleCentered
  /-- Only the `d`-component is nonzero. -/
  | dOnly
  /-- Only the `p`-component is nonzero. -/
  | pOnly
  /-- Both components vanish: the zero (main-term) mode. -/
  | zeroMode
  deriving DecidableEq, Repr

/-- The mode of a pair of additive frequencies. -/
def crtMode {d p : ℕ} (ad : ZMod d) (ap : ZMod p) : CRTMode :=
  if ad = 0 then (if ap = 0 then CRTMode.zeroMode else CRTMode.pOnly)
  else (if ap = 0 then CRTMode.dOnly else CRTMode.doubleCentered)

theorem crtMode_doubleCentered_iff {d p : ℕ} (ad : ZMod d) (ap : ZMod p) :
    crtMode ad ap = CRTMode.doubleCentered ↔ ad ≠ 0 ∧ ap ≠ 0 := by
  unfold crtMode
  by_cases h1 : ad = 0 <;> by_cases h2 : ap = 0 <;> simp [h1, h2]

theorem crtMode_dOnly_iff {d p : ℕ} (ad : ZMod d) (ap : ZMod p) :
    crtMode ad ap = CRTMode.dOnly ↔ ad ≠ 0 ∧ ap = 0 := by
  unfold crtMode
  by_cases h1 : ad = 0 <;> by_cases h2 : ap = 0 <;> simp [h1, h2]

theorem crtMode_pOnly_iff {d p : ℕ} (ad : ZMod d) (ap : ZMod p) :
    crtMode ad ap = CRTMode.pOnly ↔ ad = 0 ∧ ap ≠ 0 := by
  unfold crtMode
  by_cases h1 : ad = 0 <;> by_cases h2 : ap = 0 <;> simp [h1, h2]

theorem crtMode_zeroMode_iff {d p : ℕ} (ad : ZMod d) (ap : ZMod p) :
    crtMode ad ap = CRTMode.zeroMode ↔ ad = 0 ∧ ap = 0 := by
  unfold crtMode
  by_cases h1 : ad = 0 <;> by_cases h2 : ap = 0 <;> simp [h1, h2]

end Gate01Consolidation
end TwinPrimeProject
