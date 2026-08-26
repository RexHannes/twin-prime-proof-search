/-
# Gate04Root.Collisions

Root-collision determinants

  `Δ_A(e,f) = α_e m_f - α_f m_e`,   `Δ_B(e,f) = β_e m'_f - β_f m'_e`

and the collision criteria

  `t_p(e) = t_p(f) ↔ p ∣ Δ_A(e,f)`,   `t_q(e) = t_q(f) ↔ q ∣ Δ_B(e,f)`,

together with the rigidity statements:  a vanishing `Δ_A` forces equality of the
reduced base pair (and, with a jump bound, of `r`); a vanishing `Δ_B` forces
equality of the reduced shifted pair; and both vanishing forces `e = f`.
-/
import Gate04Root.CRTRoots
import Gate04Root.GCD

namespace Gate04Root

/-- The base root-collision determinant. -/
def deltaA (e f : AffineEdgeData) : ℤ := e.alpha * f.m - f.alpha * e.m

/-- The shifted root-collision determinant. -/
def deltaB (e f : AffineEdgeData) : ℤ := e.beta * f.mPrime - f.beta * e.mPrime

section Criteria

variable {p q : ℕ}

/-- **Collision criterion at `p`.** -/
theorem rootP_eq_iff_dvd_deltaA (e f : AffineEdgeData) {ime imf : ZMod p}
    (hme : (e.m : ZMod p) * ime = 1) (hmf : (f.m : ZMod p) * imf = 1) :
    rootP e.alpha ime = rootP f.alpha imf ↔ (p : ℤ) ∣ deltaA e f := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (deltaA e f) p]
  unfold rootP deltaA
  push_cast
  constructor
  · intro h
    linear_combination (-((e.m : ZMod p) * (f.m : ZMod p))) * h
      - ((e.alpha : ZMod p) * (f.m : ZMod p)) * hme
      + ((f.alpha : ZMod p) * (e.m : ZMod p)) * hmf
  · intro h
    linear_combination (-(ime * imf)) * h + ((e.alpha : ZMod p) * ime) * hmf
      - ((f.alpha : ZMod p) * imf) * hme

/-- **Collision criterion at `q`.** -/
theorem rootQ_eq_iff_dvd_deltaB (e f : AffineEdgeData) {ime imf : ZMod q}
    (hme : (e.mPrime : ZMod q) * ime = 1) (hmf : (f.mPrime : ZMod q) * imf = 1) :
    rootQ e.beta ime = rootQ f.beta imf ↔ (q : ℤ) ∣ deltaB e f := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (deltaB e f) q]
  unfold rootQ deltaB
  push_cast
  constructor
  · intro h
    linear_combination (-((e.mPrime : ZMod q) * (f.mPrime : ZMod q))) * h
      - ((e.beta : ZMod q) * (f.mPrime : ZMod q)) * hme
      + ((f.beta : ZMod q) * (e.mPrime : ZMod q)) * hmf
  · intro h
    linear_combination (-(ime * imf)) * h + ((e.beta : ZMod q) * ime) * hmf
      - ((f.beta : ZMod q) * imf) * hme

end Criteria

/-- Uniqueness of reduced fractions: `a d = c b` with both pairs coprime and
positive denominators forces the pairs to coincide. -/
theorem reduced_pair_eq {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hab : IsCoprime a b) (hcd : IsCoprime c d) (h : a * d = c * b) :
    b = d ∧ a = c := by
  have hb' : b ∣ d := by
    refine (hab.symm).dvd_of_dvd_mul_left ?_
    exact ⟨c, by linarith [h]⟩
  have hd' : d ∣ b := by
    refine (hcd.symm).dvd_of_dvd_mul_left ?_
    exact ⟨a, by linarith [h]⟩
  have hbd : b = d := Int.dvd_antisymm hb.le hd.le hb' hd'
  refine ⟨hbd, ?_⟩
  subst hbd
  exact mul_right_cancel₀ (by omega) h

/-- **`Δ_A = 0` collapses the base row.** -/
theorem deltaA_zero_eq_base_row {e f : AffineEdgeData}
    (hme : 0 < e.m) (hmf : 0 < f.m)
    (hce : IsCoprime e.alpha e.m) (hcf : IsCoprime f.alpha f.m)
    (h : deltaA e f = 0) : e.m = f.m ∧ e.alpha = f.alpha := by
  have h' : e.alpha * f.m = f.alpha * e.m := by
    have := h; unfold deltaA at this; linarith
  exact reduced_pair_eq hme hmf hce hcf h'

/-- **`Δ_B = 0` collapses the shifted row.** -/
theorem deltaB_zero_eq_shifted_row {e f : AffineEdgeData}
    (hme : 0 < e.mPrime) (hmf : 0 < f.mPrime)
    (hce : IsCoprime e.beta e.mPrime) (hcf : IsCoprime f.beta f.mPrime)
    (h : deltaB e f = 0) : e.mPrime = f.mPrime ∧ e.beta = f.beta := by
  have h' : e.beta * f.mPrime = f.beta * e.mPrime := by
    have := h; unfold deltaB at this; linarith
  exact reduced_pair_eq hme hmf hce hcf h'

/-- With the reduced base pair equal and a jump bound `|r_e - r_f| < m`, the
modulus `r` is also determined. -/
theorem r_eq_of_base_row_eq {e f : AffineEdgeData}
    (hm : e.m = f.m) (ha : e.alpha = f.alpha)
    (hcop : IsCoprime e.alpha e.m)
    (hlt : |e.r - f.r| < e.m) : e.r = f.r := by
  have h1 : e.m ∣ e.r * e.alpha - 2 := e.m_dvd_r_alpha_sub_two
  have h2 : e.m ∣ f.r * e.alpha - 2 := by
    rw [hm, ha]; exact f.m_dvd_r_alpha_sub_two
  have h3 : e.m ∣ (e.r - f.r) * e.alpha := by
    have : (e.r - f.r) * e.alpha = (e.r * e.alpha - 2) - (f.r * e.alpha - 2) := by ring
    rw [this]; exact dvd_sub h1 h2
  have h4 : e.m ∣ e.r - f.r := hcop.symm.dvd_of_dvd_mul_left (by
    simpa [mul_comm] using h3)
  have := Int.eq_zero_of_abs_lt_dvd h4 hlt
  omega

/-- Two affine edges with equal data fields are equal. -/
theorem AffineEdgeData.ext' {e f : AffineEdgeData}
    (hr : e.r = f.r) (hm : e.m = f.m) (hk : e.k = f.k) (hmp : e.mPrime = f.mPrime)
    (hw : e.w0 = f.w0) (ha : e.alpha = f.alpha) (hb : e.beta = f.beta) : e = f := by
  cases e; cases f
  simp only at hr hm hk hmp hw ha hb
  subst hr; subst hm; subst hk; subst hmp; subst hw; subst ha; subst hb
  rfl

/-- **Double vanishing determinant rigidity.**  If both collision determinants
vanish (and the reduced pairs are genuinely reduced, with positive denominators
and nonzero jump), the two rows coincide. -/
theorem double_delta_zero_row_eq {e f : AffineEdgeData}
    (hme : 0 < e.m) (hmf : 0 < f.m)
    (hmpe : 0 < e.mPrime) (hmpf : 0 < f.mPrime)
    (hce : IsCoprime e.alpha e.m) (hcf : IsCoprime f.alpha f.m)
    (hbe : IsCoprime e.beta e.mPrime) (hbf : IsCoprime f.beta f.mPrime)
    (hke : e.k ≠ 0)
    (hA : deltaA e f = 0) (hB : deltaB e f = 0) : e = f := by
  obtain ⟨hm, ha⟩ := deltaA_zero_eq_base_row hme hmf hce hcf hA
  obtain ⟨hmp, hb⟩ := deltaB_zero_eq_shifted_row hmpe hmpf hbe hbf hB
  -- the affine determinant identity gives `k_e = k_f`
  have hk : e.k = f.k := by
    have h1 := e.affine_det_eq_two_k
    have h2 := f.affine_det_eq_two_k
    rw [hm, ha, hmp, hb] at h1
    omega
  -- `m' = m + k r` then gives `r_e = r_f`
  have hr : e.r = f.r := by
    have h1 := e.mPrime_def
    have h2 := f.mPrime_def
    rw [hm, hk, hmp] at h1
    have : f.k * e.r = f.k * f.r := by omega
    exact mul_left_cancel₀ (by rw [← hk]; exact hke) this
  -- and `r α = m w₀ + 2` determines `w₀`
  have hw : e.w0 = f.w0 := by
    have h1 := e.alpha_def
    have h2 := f.alpha_def
    rw [hr, ha, hm] at h1
    have : f.m * e.w0 = f.m * f.w0 := by omega
    exact mul_left_cancel₀ (by omega) this
  exact AffineEdgeData.ext' hr hm hk hmp hw ha hb

end Gate04Root
