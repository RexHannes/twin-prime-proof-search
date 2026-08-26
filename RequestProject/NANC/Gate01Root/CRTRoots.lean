import Gate04Root.CRTRoots
import RequestProject.NANC.Gate01Root.BAL

/-!
# Gate01Root: the exact CRT roots

`t_p = -α m⁻¹ (mod p)`, `t_q = -β (m')⁻¹ (mod q)` and their CRT combination
`T_{pq} (mod p q)`, with the two reductions and uniqueness.

## Relation to the older banked residue

The Gate 0–1 bank contains `RouteAFibreFrame.Gate01.nPrime_residue_mod_qm`, which
pins a *cofactor* `n'` modulo `q m` in terms of a CRT amalgamated `w✦`.  That is a
different object (different unknown, different modulus) from the root `T_{pq}`
of this file, and **no identification between them is claimed or used**.  What is
shared is only the CRT amalgamation pattern.
-/

namespace RouteAFibreFrame
namespace Gate01Root

variable {p q : ℕ}

/-- The local root at `p`, `t_p = -α m⁻¹` (with `im` an inverse of `m`). -/
def rootP (alpha : ℤ) (im : ZMod p) : ZMod p := Gate04Root.rootP alpha im

/-- The local root at `q`, `t_q = -β (m')⁻¹` (with `imPrime` an inverse of `m'`). -/
def rootQ (beta : ℤ) (imPrime : ZMod q) : ZMod q := Gate04Root.rootQ beta imPrime

/-- The CRT root `T_{pq}`. -/
noncomputable def crtRoot (hco : Nat.Coprime p q) (tp : ZMod p) (tq : ZMod q) :
    ZMod (p * q) := Gate04Root.crtRoot hco tp tq

theorem crtRoot_mod_p (hco : Nat.Coprime p q) (tp : ZMod p) (tq : ZMod q) :
    ZMod.castHom (dvd_mul_right p q) (ZMod p) (crtRoot hco tp tq) = tp :=
  Gate04Root.crtRoot_mod_p hco tp tq

theorem crtRoot_mod_q (hco : Nat.Coprime p q) (tp : ZMod p) (tq : ZMod q) :
    ZMod.castHom (dvd_mul_left q p) (ZMod q) (crtRoot hco tp tq) = tq :=
  Gate04Root.crtRoot_mod_q hco tp tq

/-- Uniqueness modulo `p q`. -/
theorem crtRoot_unique (hco : Nat.Coprime p q) {tp : ZMod p} {tq : ZMod q}
    {x : ZMod (p * q)}
    (hxp : ZMod.castHom (dvd_mul_right p q) (ZMod p) x = tp)
    (hxq : ZMod.castHom (dvd_mul_left q p) (ZMod q) x = tq) :
    x = crtRoot hco tp tq :=
  Gate04Root.crtRoot_unique hco hxp hxq

end Gate01Root
end RouteAFibreFrame
