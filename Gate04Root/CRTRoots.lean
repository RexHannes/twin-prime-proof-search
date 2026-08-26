/-
# Gate04Root.CRTRoots

The local roots

  `t_p ≡ -α m⁻¹ (mod p)`,   `t_q ≡ -β (m')⁻¹ (mod q)`

and their CRT combination `T_{pq} (mod p q)`, together with the two reduction
properties and uniqueness.

Inverses are given by explicit witnesses (`im` with `m * im = 1`), so that the
statements carry their invertibility hypotheses visibly.
-/
import Gate04Root.BAL

namespace Gate04Root

variable {p q : ℕ}

/-- The local root at `p`:  `t_p = -α m⁻¹`, where `im` is an inverse of `m`. -/
def rootP (alpha : ℤ) (im : ZMod p) : ZMod p := -(alpha : ZMod p) * im

/-- The local root at `q`:  `t_q = -β (m')⁻¹`, where `imPrime` is an inverse
of `m'`. -/
def rootQ (beta : ℤ) (imPrime : ZMod q) : ZMod q := -(beta : ZMod q) * imPrime

/-- The CRT combination of the two local roots. -/
noncomputable def crtRoot (hco : Nat.Coprime p q) (tp : ZMod p) (tq : ZMod q) :
    ZMod (p * q) := (crtEquiv hco).symm (tp, tq)

@[simp] theorem crtRoot_mod_p (hco : Nat.Coprime p q) (tp : ZMod p) (tq : ZMod q) :
    ZMod.castHom (dvd_mul_right p q) (ZMod p) (crtRoot hco tp tq) = tp := by
  rw [← crtEquiv_fst hco]
  simp [crtRoot]

@[simp] theorem crtRoot_mod_q (hco : Nat.Coprime p q) (tp : ZMod p) (tq : ZMod q) :
    ZMod.castHom (dvd_mul_left q p) (ZMod q) (crtRoot hco tp tq) = tq := by
  rw [← crtEquiv_snd hco]
  simp [crtRoot]

/-- Uniqueness of the CRT root modulo `p q`. -/
theorem crtRoot_unique (hco : Nat.Coprime p q) {tp : ZMod p} {tq : ZMod q}
    {x : ZMod (p * q)}
    (hxp : ZMod.castHom (dvd_mul_right p q) (ZMod p) x = tp)
    (hxq : ZMod.castHom (dvd_mul_left q p) (ZMod q) x = tq) :
    x = crtRoot hco tp tq := by
  refine crt_ext hco ?_ ?_
  · rw [hxp, crtRoot_mod_p]
  · rw [hxq, crtRoot_mod_q]

end Gate04Root
