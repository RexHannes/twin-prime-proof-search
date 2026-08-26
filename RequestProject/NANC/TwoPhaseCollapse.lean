import RequestProject.NANC.CDVForm
import RequestProject.NANC.W4Frontier.DeterminantGraph

namespace TwinPrimeProject.NANC.TwoPhaseCollapse

/-! # Two-phase collapse: algebraic prerequisites

This module banks only integer, congruence, CRT-specification, and rational-exponent
algebra.  It contains no analytic cancellation claim.
-/

/-- The base quotient on the `A` side of the CDV orbit. -/
def cdvA0 (m w0 r : ℤ) : ℤ := (m * w0 + 2) / r

/-- The base quotient on the `B` side of the CDV orbit. -/
def cdvB0 (mPrime w0 r : ℤ) : ℤ := (mPrime * w0 + 2) / r

/-- The affine `A` coordinate at time `t`. -/
def cdvA (m w0 r t : ℤ) : ℤ := cdvA0 m w0 r + m * t

/-- The affine `B` coordinate at time `t`. -/
def cdvB (mPrime w0 r t : ℤ) : ℤ := cdvB0 mPrime w0 r + mPrime * t

/-- The affine physical coordinate `w_t = w₀ + rt`. -/
def cdvW (w0 r t : ℤ) : ℤ := w0 + r * t

/-- Divisibility makes the quotient definition satisfy its division-free equation. -/
theorem r_mul_cdvA0 (m w0 r : ℤ) (hdiv : r ∣ m * w0 + 2) :
    r * cdvA0 m w0 r = m * w0 + 2 := by
  simpa [cdvA0] using Int.mul_ediv_cancel' hdiv

/-- Divisibility makes the second quotient satisfy its division-free equation. -/
theorem r_mul_cdvB0 (mPrime w0 r : ℤ) (hdiv : r ∣ mPrime * w0 + 2) :
    r * cdvB0 mPrime w0 r = mPrime * w0 + 2 := by
  simpa [cdvB0] using Int.mul_ediv_cancel' hdiv

/-- Quotient-level CDV identity, obtained by reusing the existing division-free theorem. -/
theorem cdv_B_eq_A_add_k_w_quotient
    (m mPrime k r w0 t : ℤ)
    (hmPrime : mPrime = m + k * r)
    (hr : r ≠ 0)
    (hAdiv : r ∣ m * w0 + 2)
    (hBdiv : r ∣ mPrime * w0 + 2) :
    cdvB mPrime w0 r t = cdvA m w0 r t + k * cdvW w0 r t := by
  apply TwinPrimeProject.NANC.cdv_B_eq_A_add_k_w
      m mPrime k r (cdvW w0 r t) (cdvA m w0 r t) (cdvB mPrime w0 r t)
  · exact hmPrime
  · rw [cdvA, cdvW, mul_add, mul_add, r_mul_cdvA0 m w0 r hAdiv]
    ring
  · rw [cdvB, cdvW, mul_add, mul_add, r_mul_cdvB0 mPrime w0 r hBdiv]
    ring
  · exact hr

/-- The second quotient-level CDV identity. -/
theorem cdv_mprimeA_sub_mB_quotient
    (m mPrime k r w0 t : ℤ)
    (hmPrime : mPrime = m + k * r)
    (hr : r ≠ 0)
    (hAdiv : r ∣ m * w0 + 2)
    (hBdiv : r ∣ mPrime * w0 + 2) :
    mPrime * cdvA m w0 r t - m * cdvB mPrime w0 r t = 2 * k := by
  apply TwinPrimeProject.NANC.cdv_mprimeA_sub_mB
      m mPrime k r (cdvW w0 r t) (cdvA m w0 r t) (cdvB mPrime w0 r t)
  · exact hmPrime
  · rw [cdvA, cdvW, mul_add, mul_add, r_mul_cdvA0 m w0 r hAdiv]
    ring
  · rw [cdvB, cdvW, mul_add, mul_add, r_mul_cdvB0 mPrime w0 r hBdiv]
    ring
  · exact hr

/-- Time shifting two affine coordinates produces the determinant `2kz`. -/
theorem cdv_time_shift_determinant
    (A_t B_t A_tz B_tz m mPrime k z : ℤ)
    (hAshift : A_tz = A_t + m * z)
    (hBshift : B_tz = B_t + mPrime * z)
    (hbase : mPrime * A_t - m * B_t = 2 * k) :
    A_t * B_tz - A_tz * B_t = 2 * k * z :=
  TwinPrimeProject.NANC.W4Frontier.jointHitDeterminantIdentity
    hAshift hBshift hbase

/-- Substitution of all four hit factorizations into the time-shift determinant. -/
theorem four_hit_determinant_eq_two_k_z
    (p q pPrime qPrime u v uPrime vPrime A_t B_t A_tz B_tz m mPrime k z : ℤ)
    (hAt : A_t = p * u) (hBt : B_t = q * v)
    (hAtz : A_tz = pPrime * uPrime) (hBtz : B_tz = qPrime * vPrime)
    (hAshift : A_tz = A_t + m * z)
    (hBshift : B_tz = B_t + mPrime * z)
    (hbase : mPrime * A_t - m * B_t = 2 * k) :
    p * qPrime * u * vPrime - pPrime * q * uPrime * v = 2 * k * z := by
  apply TwinPrimeProject.NANC.W4Frontier.four_hit_determinant
      p q pPrime qPrime u v uPrime vPrime k z A_t B_t A_tz B_tz
  · exact cdv_time_shift_determinant A_t B_t A_tz B_tz m mPrime k z
      hAshift hBshift hbase
  · exact hAt
  · exact hBt
  · exact hAtz
  · exact hBtz

/-- Exact diagnosis of the rejected extra-`r` formula. -/
theorem extra_r_formula_iff_degenerate (k r z : ℤ) :
    2 * k * z = 2 * k * r * z ↔ k * z * (r - 1) = 0 := by
  constructor <;> intro h <;> nlinarith

/-- The frequency numerator occurring after combining the two phases. -/
def frequencyDeterminant (p q pPrime qPrime h hPrime : ℤ) : ℤ :=
  h * pPrime * qPrime - hPrime * p * q

/-- A zero frequency determinant is impossible in the stated primitive ranges. -/
theorem frequency_determinant_ne_zero
    (p q pPrime qPrime h hPrime : ℤ)
    (hcop : IsCoprime (p * q) (pPrime * qPrime))
    (hhpos : 0 < |h|) (hhlt : |h| < p * q)
    (hhPrimePos : 0 < |hPrime|) (hhPrimeLt : |hPrime| < pPrime * qPrime) :
    frequencyDeterminant p q pPrime qPrime h hPrime ≠ 0 := by
  intro hzero
  have heq : h * (pPrime * qPrime) = hPrime * (p * q) := by
    unfold frequencyDeterminant at hzero
    nlinarith
  have hdvdProduct : p * q ∣ h * (pPrime * qPrime) := by
    use hPrime
    rw [heq]
    ring
  have hdvdH : p * q ∣ h := hcop.dvd_of_dvd_mul_left (by
    simpa [mul_comm] using hdvdProduct)
  have hz : h = 0 := Int.eq_zero_of_abs_lt_dvd hdvdH hhlt
  have hdvdPrimeProduct : pPrime * qPrime ∣ hPrime * (p * q) := by
    use h
    rw [← heq]
    ring
  have hdvdHPrime : pPrime * qPrime ∣ hPrime :=
    hcop.symm.dvd_of_dvd_mul_left (by simpa [mul_comm] using hdvdPrimeProduct)
  have hzPrime : hPrime = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvdHPrime hhPrimeLt
  have hnonzero : 0 < |h| ∧ 0 < |hPrime| := ⟨hhpos, hhPrimePos⟩
  rw [hz, hzPrime, abs_zero] at hnonzero
  omega

/-- Frequency and modulus data.  The consistency fields prevent the derived
quantities from drifting away from their displayed formulas. -/
structure PrimePairFreqData where
  p : ℤ
  q : ℤ
  pPrime : ℤ
  qPrime : ℤ
  h : ℤ
  hPrime : ℤ
  pProd : ℤ
  qProd : ℤ
  modulus : ℤ
  numerator : ℤ
  hpProd : pProd = (p : ℤ) * pPrime
  hqProd : qProd = (q : ℤ) * qPrime
  hmodulus : modulus = (pProd : ℤ) * qProd
  hnumerator : numerator = (h : ℤ) * pPrime * qPrime - hPrime * p * q

/-- A pair of integer representatives satisfying the four desired local CRT
specifications.  Inverses are represented in the corresponding `ZMod` rings. -/
structure CRTFrequencyWitness (d : PrimePairFreqData) where
  aRep : ℤ
  bRep : ℤ
  A_mod_p :
    (aRep : ZMod d.p.natAbs) =
      2 * d.h * d.pPrime * (d.q : ZMod d.p.natAbs)⁻¹
  A_mod_pPrime :
    (aRep : ZMod d.pPrime.natAbs) =
      -2 * d.hPrime * d.p * (d.qPrime : ZMod d.pPrime.natAbs)⁻¹
  B_mod_q :
    (bRep : ZMod d.q.natAbs) =
      2 * d.h * d.qPrime * (d.p : ZMod d.q.natAbs)⁻¹
  B_mod_qPrime :
    (bRep : ZMod d.qPrime.natAbs) =
      -2 * d.hPrime * d.q * (d.pPrime : ZMod d.qPrime.natAbs)⁻¹

 theorem A_mod_p_spec {d : PrimePairFreqData} (w : CRTFrequencyWitness d) :
    (w.aRep : ZMod d.p.natAbs) =
      2 * d.h * d.pPrime * (d.q : ZMod d.p.natAbs)⁻¹ := w.A_mod_p

 theorem A_mod_pprime_spec {d : PrimePairFreqData} (w : CRTFrequencyWitness d) :
    (w.aRep : ZMod d.pPrime.natAbs) =
      -2 * d.hPrime * d.p * (d.qPrime : ZMod d.pPrime.natAbs)⁻¹ := w.A_mod_pPrime

 theorem B_mod_q_spec {d : PrimePairFreqData} (w : CRTFrequencyWitness d) :
    (w.bRep : ZMod d.q.natAbs) =
      2 * d.h * d.qPrime * (d.p : ZMod d.q.natAbs)⁻¹ := w.B_mod_q

 theorem B_mod_qprime_spec {d : PrimePairFreqData} (w : CRTFrequencyWitness d) :
    (w.bRep : ZMod d.qPrime.natAbs) =
      -2 * d.hPrime * d.q * (d.pPrime : ZMod d.qPrime.natAbs)⁻¹ := w.B_mod_qPrime

/-- Local primitivity at `p` and `p'` combines into primitivity at `P = pp'`. -/
theorem A_coprime_P (A p pPrime P : ℤ)
    (hP : P = p * pPrime) (hAp : IsCoprime A p)
    (hApPrime : IsCoprime A pPrime) : IsCoprime A P := by
  rw [hP]
  exact hAp.mul_right hApPrime

/-- If both `A` and `k` are primitive at each prime factor, then `Ak` is
primitive modulo their product. -/
theorem Ak_coprime_P (A k p pPrime P : ℤ)
    (hP : P = p * pPrime)
    (hAp : IsCoprime A p) (hApPrime : IsCoprime A pPrime)
    (hkp : IsCoprime k p) (hkpPrime : IsCoprime k pPrime) :
    IsCoprime (A * k) P := by
  rw [hP]
  exact (hAp.mul_left hkp).mul_right (hApPrime.mul_left hkpPrime)

/-- The required saving splits into the two natural margins. -/
theorem saving_decomposition (a b : ℚ) :
    1 - a - 2 * b = (2 / 3 - a - b) + (1 / 3 - b) := by ring

 theorem region_high_b_no_M_over_L_saving_needed (b : ℚ)
    (hb : 1 / 3 ≤ b) : 1 / 3 - b ≤ 0 := by linarith

 theorem pascadi_saving_threshold (b : ℚ) :
    b / 6 ≥ 1 / 3 - b ↔ b ≥ 2 / 7 := by constructor <;> intro h <;> linarith

 theorem residual_strip_width : (2 / 7 : ℚ) - 5 / 18 = 1 / 126 := by norm_num

 theorem residual_endpoint_gap :
    (1 / 3 : ℚ) - 5 / 18 - (5 / 18) / 6 = 1 / 108 := by norm_num

end TwinPrimeProject.NANC.TwoPhaseCollapse
