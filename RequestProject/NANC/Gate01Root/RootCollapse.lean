import Gate04Root.RootCollapse
import RequestProject.NANC.Gate01Root.CRTRoots

/-!
# Gate01Root: ROOT-COLLAPSE

With `p m' u ≡ 1 (mod q m)` and the affine data of a root edge:

* `m ∣ N_J`, `N_J = 2 k p u - α`  (`m_dvd_rootCollapseNumerator`);
* for `J` with `m J = N_J`:
  `J ≡ -α m⁻¹ (mod p)`, `J ≡ -β (m')⁻¹ (mod q)`, hence `J ≡ T_{pq} (mod p q)`;
* the exact rational identity
  `2 h k u/(q m) - h α/(p q m) = h J/(p q)`.

No analytic estimate occurs in this module.
-/

namespace RouteAFibreFrame
namespace Gate01Root

open Gate04Root

/-- The root-collapse numerator `N_J = 2 k p u - α`. -/
def rootCollapseNumerator (k p u alpha : ℤ) : ℤ := Gate04Root.rootCollapseNumerator k p u alpha

/-- **`m ∣ N_J`.** -/
theorem m_dvd_rootCollapseNumerator {m k r p u alpha mPrime : ℤ}
    (hmp : mPrime = m + k * r)
    (hu : m ∣ p * mPrime * u - 1)
    (halpha : m ∣ r * alpha - 2)
    (hcop : IsCoprime m r) :
    m ∣ rootCollapseNumerator k p u alpha :=
  Gate04Root.m_dvd_rootCollapseNumerator hmp hu halpha hcop

/-- Version with the genuine modulus `q m` of the inverse `u`. -/
theorem m_dvd_rootCollapseNumerator_of_qm {m k r p u alpha mPrime q : ℤ}
    (hmp : mPrime = m + k * r)
    (hu : q * m ∣ p * mPrime * u - 1)
    (halpha : m ∣ r * alpha - 2)
    (hcop : IsCoprime m r) :
    m ∣ rootCollapseNumerator k p u alpha :=
  Gate04Root.m_dvd_rootCollapseNumerator hmp (dvd_trans ⟨q, by ring⟩ hu) halpha hcop

variable {p q : ℕ}

/-- `J ≡ -α m⁻¹ (mod p)`. -/
theorem rootCollapseJ_mod_p {m k pz u alpha J : ℤ} {im : ZMod p}
    (hJ : m * J = 2 * k * pz * u - alpha)
    (hpz : (pz : ZMod p) = 0)
    (him : (m : ZMod p) * im = 1) :
    (J : ZMod p) = rootP alpha im :=
  Gate04Root.rootCollapseJ_mod_p hJ hpz him

/-- `J ≡ -β (m')⁻¹ (mod q)`. -/
theorem rootCollapseJ_mod_q {m k pz u alpha beta mPrime J : ℤ}
    {im imPrime : ZMod q}
    (hJ : m * J = 2 * k * pz * u - alpha)
    (halphamPrime : alpha * mPrime = m * beta + 2 * k)
    (hu : (pz : ZMod q) * (mPrime : ZMod q) * (u : ZMod q) = 1)
    (him : (m : ZMod q) * im = 1)
    (himP : (mPrime : ZMod q) * imPrime = 1) :
    (J : ZMod q) = rootQ beta imPrime :=
  Gate04Root.rootCollapseJ_mod_q hJ halphamPrime hu him himP

/-- **(ROOT-RESIDUE)**  `J ≡ T_{pq} (mod p q)`. -/
theorem rootCollapseJ_eq_crtRoot (hco : Nat.Coprime p q)
    {m k pz u alpha beta mPrime J : ℤ} {imp : ZMod p} {im imPrime : ZMod q}
    (hJ : m * J = 2 * k * pz * u - alpha)
    (halphamPrime : alpha * mPrime = m * beta + 2 * k)
    (hpz : (pz : ZMod p) = 0)
    (himp : (m : ZMod p) * imp = 1)
    (hu : (pz : ZMod q) * (mPrime : ZMod q) * (u : ZMod q) = 1)
    (him : (m : ZMod q) * im = 1)
    (himP : (mPrime : ZMod q) * imPrime = 1) :
    (J : ZMod (p * q)) = crtRoot hco (rootP alpha imp) (rootQ beta imPrime) :=
  Gate04Root.rootCollapseJ_eq_crtRoot hco hJ halphamPrime hpz himp hu him himP

/-- The hypothesis `α m' = m β + 2 k` of the `q`-side residue is exactly the
affine determinant identity of a root edge. -/
theorem alpha_mul_mPrime_of_rootEdge (e : RootEdgeData) :
    e.alpha * e.mPrime = e.m * e.beta + 2 * e.k := by
  have h := root_affine_det_eq_two_k e
  linarith [h, (by ring : e.alpha * e.mPrime = e.mPrime * e.alpha)]

/-- **(ROOT-RATIONAL)** `2 h k u/(q m) - h α/(p q m) = h J/(p q)`. -/
theorem rootCollapse_rational_identity {h k p q m u alpha J : ℚ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hm : m ≠ 0)
    (hJ : m * J = 2 * k * p * u - alpha) :
    2 * h * k * u / (q * m) - h * alpha / (p * q * m) = h * J / (p * q) :=
  Gate04Root.rootCollapse_rational_identity hp hq hm hJ

/-- Additive-character form of (ROOT-RATIONAL):
`e_{qm}(2 h k u) · e(-h α/(p q m)) = e_{pq}(h J)`. -/
theorem rootCollapse_exp_identity {h k p q m u alpha J : ℚ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hm : m ≠ 0)
    (hJ : m * J = 2 * k * p * u - alpha) :
    Gate04Root.expRat (2 * h * k * u / (q * m))
        * Gate04Root.expRat (-(h * alpha / (p * q * m)))
      = Gate04Root.expRat (h * J / (p * q)) :=
  Gate04Root.rootCollapse_exp_identity hp hq hm hJ

end Gate01Root
end RouteAFibreFrame
