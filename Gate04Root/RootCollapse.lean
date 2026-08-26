/-
# Gate04Root.RootCollapse

The ROOT-COLLAPSE residue theorem.

With `u ≡ (p m')⁻¹ (mod q m)` and the affine data of an edge we show

* `m ∣ N_J`, where `N_J = 2 k p u - α`   (`m_dvd_rootCollapseNumerator`);
* writing `m J = N_J`,
    `J ≡ -α m⁻¹ (mod p)`   (`rootCollapseJ_mod_p`),
    `J ≡ -β (m')⁻¹ (mod q)` (`rootCollapseJ_mod_q`),
  hence `J ≡ T_{pq} (mod p q)` (`rootCollapseJ_eq_crtRoot`);
* the exact rational identity (ROOT-RATIONAL)
    `2 h k u /(q m) - h α /(p q m) = h J /(p q)`  (`rootCollapse_rational_identity`).

All statements carry their invertibility hypotheses as explicit witnesses.
-/
import Gate04Root.CRTRoots

namespace Gate04Root

/-- The integer numerator of the root-collapse fraction. -/
def rootCollapseNumerator (k p u alpha : ℤ) : ℤ := 2 * k * p * u - alpha

/-- **`m ∣ N_J`.**  With `u` an inverse of `p m'` modulo `q m`, `m' = m + k r`,
`r α ≡ 2 (mod m)` and `r` invertible mod `m`, the numerator `2 k p u - α` is
divisible by `m`. -/
theorem m_dvd_rootCollapseNumerator {m k r p u alpha mPrime : ℤ}
    (hmp : mPrime = m + k * r)
    (hu : m ∣ p * mPrime * u - 1)
    (halpha : m ∣ r * alpha - 2)
    (hcop : IsCoprime m r) :
    m ∣ rootCollapseNumerator k p u alpha := by
  -- first: `p k r u ≡ 1 (mod m)`
  have h1 : m ∣ p * (k * r) * u - 1 := by
    have h3 : p * (k * r) * u - 1 = (p * mPrime * u - 1) - m * (p * u) := by
      rw [hmp]; ring
    rw [h3]
    exact dvd_sub hu ⟨p * u, rfl⟩
  -- then `r * (2 k p u - α) ≡ 0 (mod m)`
  have h4 : m ∣ r * rootCollapseNumerator k p u alpha := by
    have : r * rootCollapseNumerator k p u alpha
        = 2 * (p * (k * r) * u - 1) - (r * alpha - 2) := by
      unfold rootCollapseNumerator; ring
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left h1 2) halpha
  exact hcop.dvd_of_dvd_mul_left h4

section Residues

variable {p q : ℕ}

/-- `J ≡ -α m⁻¹ (mod p)`. -/
theorem rootCollapseJ_mod_p {m k pz u alpha J : ℤ} {im : ZMod p}
    (hJ : m * J = 2 * k * pz * u - alpha)
    (hpz : (pz : ZMod p) = 0)
    (him : (m : ZMod p) * im = 1) :
    (J : ZMod p) = rootP alpha im := by
  have hJ' : (m : ZMod p) * (J : ZMod p)
      = 2 * (k : ZMod p) * (pz : ZMod p) * (u : ZMod p) - (alpha : ZMod p) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) hJ
  rw [hpz] at hJ'
  unfold rootP
  linear_combination im * hJ' - (J : ZMod p) * him

/-- `J ≡ -β (m')⁻¹ (mod q)`. -/
theorem rootCollapseJ_mod_q {m k pz u alpha beta mPrime J : ℤ}
    {im imPrime : ZMod q}
    (hJ : m * J = 2 * k * pz * u - alpha)
    (halphamPrime : alpha * mPrime = m * beta + 2 * k)
    (hu : (pz : ZMod q) * (mPrime : ZMod q) * (u : ZMod q) = 1)
    (him : (m : ZMod q) * im = 1)
    (himP : (mPrime : ZMod q) * imPrime = 1) :
    (J : ZMod q) = rootQ beta imPrime := by
  have hJ' : (m : ZMod q) * (J : ZMod q)
      = 2 * (k : ZMod q) * (pz : ZMod q) * (u : ZMod q) - (alpha : ZMod q) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod q)) hJ
  have hE3 : (alpha : ZMod q) * (mPrime : ZMod q)
      = (m : ZMod q) * (beta : ZMod q) + 2 * (k : ZMod q) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod q)) halphamPrime
  have step : (mPrime : ZMod q) * ((m : ZMod q) * (J : ZMod q))
      = -((m : ZMod q) * (beta : ZMod q)) := by
    rw [hJ']
    linear_combination (2 * (k : ZMod q)) * hu - hE3
  have h1 : (mPrime : ZMod q) * (J : ZMod q) = -(beta : ZMod q) := by
    linear_combination im * step - ((mPrime : ZMod q) * (J : ZMod q) + (beta : ZMod q)) * him
  unfold rootQ
  linear_combination imPrime * h1 - (J : ZMod q) * himP

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
    (J : ZMod (p * q)) = crtRoot hco (rootP alpha imp) (rootQ beta imPrime) := by
  refine crtRoot_unique hco ?_ ?_
  · rw [map_intCast]
    exact rootCollapseJ_mod_p hJ hpz himp
  · rw [map_intCast]
    exact rootCollapseJ_mod_q hJ halphamPrime hu him himP

end Residues

/-- **(ROOT-RATIONAL)**  the exact rational identity
`2 h k u /(q m) - h α /(p q m) = h J /(p q)` whenever `m J = 2 k p u - α`. -/
theorem rootCollapse_rational_identity {h k p q m u alpha J : ℚ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hm : m ≠ 0)
    (hJ : m * J = 2 * k * p * u - alpha) :
    2 * h * k * u / (q * m) - h * alpha / (p * q * m) = h * J / (p * q) := by
  have key : 2 * h * k * u / (q * m) - h * alpha / (p * q * m)
      = h * (m * J) / (p * q * m) := by
    rw [hJ]; field_simp
  rw [key, mul_comm p q, mul_assoc]
  field_simp

/-! ### Optional: the additive-character form of (ROOT-RATIONAL) -/

/-- `e(x) = exp(2 π i x)` for a rational argument `x`. -/
noncomputable def expRat (x : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

@[simp] theorem expRat_add (x y : ℚ) : expRat (x + y) = expRat x * expRat y := by
  unfold expRat
  rw [← Complex.exp_add]
  push_cast
  ring_nf

@[simp] theorem expRat_intCast (n : ℤ) : expRat (n : ℚ) = 1 := by
  unfold expRat
  have h : (2 : ℂ) * Real.pi * Complex.I * (((n : ℚ) : ℂ))
      = (n : ℤ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- The additive-character form of (ROOT-RATIONAL):
`e_{qm}(2 h k u) · e(-h α /(p q m)) = e_{pq}(h J)`. -/
theorem rootCollapse_exp_identity {h k p q m u alpha J : ℚ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hm : m ≠ 0)
    (hJ : m * J = 2 * k * p * u - alpha) :
    expRat (2 * h * k * u / (q * m)) * expRat (-(h * alpha / (p * q * m)))
      = expRat (h * J / (p * q)) := by
  rw [← expRat_add]
  congr 1
  have := rootCollapse_rational_identity (h := h) hp hq hm hJ
  linarith

/-- If two rationals with the same denominator `p q` have integrally congruent
numerators, their additive characters agree.  Combined with (ROOT-RESIDUE) this
shows `e_{pq}(h J)` only depends on `T_{pq}`. -/
theorem expRat_root_periodic {pq : ℚ} (hpq : pq ≠ 0) (J T c : ℤ)
    (hJT : (J : ℚ) = T + c * pq) :
    expRat ((J : ℚ) / pq) = expRat ((T : ℚ) / pq) := by
  have h : (J : ℚ) / pq = (T : ℚ) / pq + (c : ℚ) := by
    rw [hJT]; field_simp
  rw [h, expRat_add, expRat_intCast, mul_one]

end Gate04Root
