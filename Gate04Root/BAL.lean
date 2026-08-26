/-
# Gate04Root.BAL

The residue-level BAL skeleton.

* `k_mul_inv_mPrime_eq_inv_r` :  in `ZMod m`, if `m' = k r` (which is exactly
  `m' = m + k r` read mod `m`) and `k`, `r` are units, then `k (m')⁻¹ = r⁻¹`.
* the CRT ring equivalence `ZMod (m q) ≃+* ZMod m × ZMod q` with its two
  projection lemmas;
* the two projections of `A = 2 h k (p m')⁻¹  (mod m q)`:
    `A q⁻¹ ≡ 2 h (r p q)⁻¹ (mod m)`,
    `A m⁻¹ ≡ 2 h k (p m m')⁻¹ (mod q)`.

Inverses are handled through explicit *witnesses* (`x` with `a * x = 1`), which
makes the statements meaningful without any `NeZero`/unit side conditions on the
`ZMod.inv` function; a `ZMod.inv` version is derived for `BAL-m`.

No complex exponentials are used: this is the mandatory congruential core.
-/
import Gate04Root.GCD

namespace Gate04Root

section Witness

variable {R : Type*} [CommRing R]

/-- Inverse witnesses are unique. -/
theorem inv_witness_unique {a u v : R} (hu : a * u = 1) (hv : a * v = 1) : u = v := by
  calc u = u * (a * v) := by rw [hv]; ring
    _ = (a * u) * v := by ring
    _ = v := by rw [hu]; ring

/-- **(BAL-m)**, witness form: if `m' = k r` and `x`, `y` are inverse witnesses for
`m'` and `r`, then `k x = y`. -/
theorem k_mul_inv_mPrime_eq_inv_r_witness {k r mPrime x y : R}
    (hmp : mPrime = k * r) (hx : mPrime * x = 1) (hy : r * y = 1) : k * x = y := by
  calc k * x = (k * x) * (r * y) := by rw [hy]; ring
    _ = (mPrime * x) * y := by rw [hmp]; ring
    _ = y := by rw [hx]; ring

end Witness

/-- **(BAL-m)** in `ZMod n` with the `ZMod` inverse: if `m' = k r` with `k`, `r`
units, then `k (m')⁻¹ = r⁻¹`. -/
theorem k_mul_inv_mPrime_eq_inv_r {n : ℕ} {k r mPrime : ZMod n}
    (hmp : mPrime = k * r) (hk : IsUnit k) (hr : IsUnit r) :
    k * mPrime⁻¹ = r⁻¹ := by
  have hmpu : IsUnit mPrime := by rw [hmp]; exact hk.mul hr
  exact k_mul_inv_mPrime_eq_inv_r_witness hmp
    (ZMod.mul_inv_of_unit _ hmpu) (ZMod.mul_inv_of_unit _ hr)

/-- Reduction of the integer relation `m' = m + k r` modulo `m`. -/
theorem cast_mPrime_mod_m {m : ℕ} {k r mPrime : ℤ} (hmp : mPrime = (m : ℤ) + k * r) :
    ((mPrime : ZMod m)) = (k : ZMod m) * (r : ZMod m) := by
  subst hmp
  push_cast
  simp

/-- **(BAL-m)** for the integer data `m' = m + k r`. -/
theorem k_mul_inv_mPrime_eq_inv_r_int {m : ℕ} {k r mPrime : ℤ}
    (hmp : mPrime = (m : ℤ) + k * r)
    (hk : IsUnit (k : ZMod m)) (hr : IsUnit (r : ZMod m)) :
    (k : ZMod m) * ((mPrime : ZMod m))⁻¹ = ((r : ZMod m))⁻¹ :=
  k_mul_inv_mPrime_eq_inv_r (cast_mPrime_mod_m hmp) hk hr

section CRT

variable {m q : ℕ}

/-- The CRT ring equivalence `ZMod (m q) ≃+* ZMod m × ZMod q`. -/
noncomputable def crtEquiv (hco : Nat.Coprime m q) : ZMod (m * q) ≃+* ZMod m × ZMod q :=
  ZMod.chineseRemainder hco

/-- First projection of the CRT equivalence is reduction mod `m`. -/
theorem crtEquiv_fst (hco : Nat.Coprime m q) (x : ZMod (m * q)) :
    (crtEquiv hco x).1 = ZMod.castHom (dvd_mul_right m q) (ZMod m) x := by
  simp [crtEquiv, ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]

/-- Second projection of the CRT equivalence is reduction mod `q`. -/
theorem crtEquiv_snd (hco : Nat.Coprime m q) (x : ZMod (m * q)) :
    (crtEquiv hco x).2 = ZMod.castHom (dvd_mul_left q m) (ZMod q) x := by
  simp [crtEquiv, ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]

/-- CRT uniqueness: an element of `ZMod (m q)` is determined by its two
reductions. -/
theorem crt_ext (hco : Nat.Coprime m q) {x y : ZMod (m * q)}
    (hm : ZMod.castHom (dvd_mul_right m q) (ZMod m) x
        = ZMod.castHom (dvd_mul_right m q) (ZMod m) y)
    (hq : ZMod.castHom (dvd_mul_left q m) (ZMod q) x
        = ZMod.castHom (dvd_mul_left q m) (ZMod q) y) : x = y := by
  have : crtEquiv hco x = crtEquiv hco y := by
    apply Prod.ext
    · rw [crtEquiv_fst, crtEquiv_fst]; exact hm
    · rw [crtEquiv_snd, crtEquiv_snd]; exact hq
  exact (crtEquiv hco).injective this

/-- Projection mod `m` of `A = 2 h k (p m')⁻¹`:  `A q⁻¹ = 2 h (r p q)⁻¹`. -/
theorem bal_project_m {h k r p mPrime : ℤ}
    (hmp : mPrime = (m : ℤ) + k * r)
    {A w : ZMod (m * q)}
    (hw : ((p : ZMod (m * q)) * (mPrime : ZMod (m * q))) * w = 1)
    (hA : A = 2 * (h : ZMod (m * q)) * (k : ZMod (m * q)) * w)
    {ip ir iq : ZMod m}
    (hip : (p : ZMod m) * ip = 1) (hir : (r : ZMod m) * ir = 1) :
    (ZMod.castHom (dvd_mul_right m q) (ZMod m) A) * iq
      = 2 * (h : ZMod m) * (ip * ir * iq) := by
  set F := ZMod.castHom (dvd_mul_right m q) (ZMod m) with hF
  have hwm : ((p : ZMod m) * ((k : ZMod m) * (r : ZMod m))) * F w = 1 := by
    have := congrArg F hw
    simpa [map_mul, map_intCast, cast_mPrime_mod_m hmp] using this
  have hAm : F A = 2 * (h : ZMod m) * (k : ZMod m) * F w := by
    rw [hA]; simp [map_mul, map_intCast, map_ofNat]
  rw [hAm]
  linear_combination (2 * (h : ZMod m) * ip * ir * iq) * hwm
    - (2 * (h : ZMod m) * (k : ZMod m) * F w * iq * (r : ZMod m) * ir) * hip
    - (2 * (h : ZMod m) * (k : ZMod m) * F w * iq) * hir

/-- Projection mod `q` of `A = 2 h k (p m')⁻¹`:  `A m⁻¹ = 2 h k (p m m')⁻¹`. -/
theorem bal_project_q {h k p mPrime : ℤ}
    {A w : ZMod (m * q)}
    (hw : ((p : ZMod (m * q)) * (mPrime : ZMod (m * q))) * w = 1)
    (hA : A = 2 * (h : ZMod (m * q)) * (k : ZMod (m * q)) * w)
    {ip im imPrime : ZMod q}
    (hip : (p : ZMod q) * ip = 1)
    (himP : (mPrime : ZMod q) * imPrime = 1) :
    (ZMod.castHom (dvd_mul_left q m) (ZMod q) A) * im
      = 2 * (h : ZMod q) * (k : ZMod q) * (ip * im * imPrime) := by
  set G := ZMod.castHom (dvd_mul_left q m) (ZMod q) with hG
  have hwq : ((p : ZMod q) * (mPrime : ZMod q)) * G w = 1 := by
    have := congrArg G hw
    simpa [map_mul, map_intCast] using this
  have hAq : G A = 2 * (h : ZMod q) * (k : ZMod q) * G w := by
    rw [hA]; simp [map_mul, map_intCast, map_ofNat]
  rw [hAq]
  linear_combination (2 * (h : ZMod q) * (k : ZMod q) * ip * im * imPrime) * hwq
    - (2 * (h : ZMod q) * (k : ZMod q) * G w * im * (mPrime : ZMod q) * imPrime) * hip
    - (2 * (h : ZMod q) * (k : ZMod q) * G w * im) * himP

end CRT

end Gate04Root
