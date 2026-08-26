import Gate04Root.BAL
import RequestProject.NANC.Gate01Root.GCDRoot

/-!
# Gate01Root: the BAL residue theorem

* `k_mul_inv_mPrime_eq_inv_r` : in `ZMod m`, `k (m')⁻¹ = r⁻¹` when `m' = m + k r`
  and `k`, `r` are units;
* `bal_crt_residue` : the CRT ring isomorphism `ZMod (m q) ≃+* ZMod m × ZMod q`
  together with its two reduction maps;
* `bal_projection_mod_m` / `bal_projection_mod_q` : the two projections of
  `A = 2 h k (p m')⁻¹ (mod m q)`, namely `A q⁻¹ ≡ 2 h (r p q)⁻¹ (mod m)` and
  `A m⁻¹ ≡ 2 h k (p m m')⁻¹ (mod q)`.

Inverses are handled through explicit witnesses, so every invertibility
hypothesis is visible in the statement.  No complex exponential is used.
-/

namespace RouteAFibreFrame
namespace Gate01Root

open Gate04Root

/-- **(BAL-m)**  `k (m')⁻¹ = r⁻¹` in `ZMod n`, for `m' = k r` with `k`, `r`
units. -/
theorem k_mul_inv_mPrime_eq_inv_r {n : ℕ} {k r mPrime : ZMod n}
    (hmp : mPrime = k * r) (hk : IsUnit k) (hr : IsUnit r) :
    k * mPrime⁻¹ = r⁻¹ :=
  Gate04Root.k_mul_inv_mPrime_eq_inv_r hmp hk hr

/-- **(BAL-m)** for integer data `m' = m + k r`, read in `ZMod m`. -/
theorem k_mul_inv_mPrime_eq_inv_r_int {m : ℕ} {k r mPrime : ℤ}
    (hmp : mPrime = (m : ℤ) + k * r)
    (hk : IsUnit (k : ZMod m)) (hr : IsUnit (r : ZMod m)) :
    (k : ZMod m) * ((mPrime : ZMod m))⁻¹ = ((r : ZMod m))⁻¹ :=
  Gate04Root.k_mul_inv_mPrime_eq_inv_r_int hmp hk hr

/-- The CRT ring isomorphism `ZMod (m q) ≃+* ZMod m × ZMod q`. -/
noncomputable def balCrtEquiv {m q : ℕ} (hco : Nat.Coprime m q) :
    ZMod (m * q) ≃+* ZMod m × ZMod q := Gate04Root.crtEquiv hco

/-- **BAL CRT residue theorem.**  The CRT isomorphism together with its two
reduction maps; an element of `ZMod (m q)` is exactly its pair of reductions. -/
theorem bal_crt_residue {m q : ℕ} (hco : Nat.Coprime m q) (x : ZMod (m * q)) :
    (balCrtEquiv hco x).1 = ZMod.castHom (dvd_mul_right m q) (ZMod m) x ∧
      (balCrtEquiv hco x).2 = ZMod.castHom (dvd_mul_left q m) (ZMod q) x :=
  ⟨Gate04Root.crtEquiv_fst hco x, Gate04Root.crtEquiv_snd hco x⟩

/-- CRT uniqueness. -/
theorem bal_crt_ext {m q : ℕ} (hco : Nat.Coprime m q) {x y : ZMod (m * q)}
    (hm : ZMod.castHom (dvd_mul_right m q) (ZMod m) x
        = ZMod.castHom (dvd_mul_right m q) (ZMod m) y)
    (hq : ZMod.castHom (dvd_mul_left q m) (ZMod q) x
        = ZMod.castHom (dvd_mul_left q m) (ZMod q) y) : x = y :=
  Gate04Root.crt_ext hco hm hq

/-- **`m`-projection of BAL.**  `A q⁻¹ ≡ 2 h (r p q)⁻¹ (mod m)`. -/
theorem bal_projection_mod_m {m q : ℕ} {h k r p mPrime : ℤ}
    (hmp : mPrime = (m : ℤ) + k * r)
    {A w : ZMod (m * q)}
    (hw : ((p : ZMod (m * q)) * (mPrime : ZMod (m * q))) * w = 1)
    (hA : A = 2 * (h : ZMod (m * q)) * (k : ZMod (m * q)) * w)
    {ip ir iq : ZMod m}
    (hip : (p : ZMod m) * ip = 1) (hir : (r : ZMod m) * ir = 1) :
    (ZMod.castHom (dvd_mul_right m q) (ZMod m) A) * iq
      = 2 * (h : ZMod m) * (ip * ir * iq) :=
  Gate04Root.bal_project_m hmp hw hA hip hir

/-- **`q`-projection of BAL.**  `A m⁻¹ ≡ 2 h k (p m m')⁻¹ (mod q)`. -/
theorem bal_projection_mod_q {m q : ℕ} {h k p mPrime : ℤ}
    {A w : ZMod (m * q)}
    (hw : ((p : ZMod (m * q)) * (mPrime : ZMod (m * q))) * w = 1)
    (hA : A = 2 * (h : ZMod (m * q)) * (k : ZMod (m * q)) * w)
    {ip im imPrime : ZMod q}
    (hip : (p : ZMod q) * ip = 1)
    (himP : (mPrime : ZMod q) * imPrime = 1) :
    (ZMod.castHom (dvd_mul_left q m) (ZMod q) A) * im
      = 2 * (h : ZMod q) * (k : ZMod q) * (ip * im * imPrime) :=
  Gate04Root.bal_project_q (m := m) hw hA hip himP

end Gate01Root
end RouteAFibreFrame
