import RequestProject.PolynomialHalfSieve

namespace HalfSieve

noncomputable section

abbrev p7N : ℚ := 202862520
abbrev p7a1 : ℚ := 2232394
abbrev p7a3 : ℚ := 99428805
abbrev p7a5 : ℚ := 126862841
abbrev p7a7 : ℚ := -25661520

def q7Rat (u : ℚ) : ℚ :=
  (p7a1 * u + p7a3 * u ^ 3 + p7a5 * u ^ 5 + p7a7 * u ^ 7) / p7N

def p7Rat (t : ℚ) : ℚ := q7Rat (1 - 2 * t)

def p7 (t : ℝ) : ℝ :=
  ((p7a1 : ℝ) * (1 - 2 * t) + (p7a3 : ℝ) * (1 - 2 * t) ^ 3 +
    (p7a5 : ℝ) * (1 - 2 * t) ^ 5 + (p7a7 : ℝ) * (1 - 2 * t) ^ 7) / (p7N : ℝ)

lemma p7_zero : p7 0 = 1 := by
  norm_num [p7, p7N, p7a1, p7a3, p7a5, p7a7]

lemma p7_half : p7 (1 / 2) = 0 := by
  norm_num [p7, p7N, p7a1, p7a3, p7a5, p7a7]

lemma p7_base_positive {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (p7a1 : ℝ) + p7a3 * u^2 + p7a5 * u^4 + p7a7 * u^6 > 0 := by
  have hp7a1 : (p7a1 : ℝ) = 2232394 := by norm_num [p7a1]
  have hp7a3 : (p7a3 : ℝ) = 99428805 := by norm_num [p7a3]
  have hp7a5 : (p7a5 : ℝ) = 126862841 := by norm_num [p7a5]
  have hp7a7 : (p7a7 : ℝ) = -25661520 := by norm_num [p7a7]
  have hu2_nonneg : 0 ≤ u^2 := by positivity
  have hu4_nonneg : 0 ≤ u^4 := by positivity
  have hu6_nonneg : 0 ≤ u^6 := by positivity
  have hu6_le_u4 : u^6 ≤ u^4 := by
    have hu2_le1 : u^2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg u, sq_nonneg (u^2)]
  have hp7a7_neg : (p7a7 : ℝ) < 0 := by norm_num [hp7a7]
  have h6 : (p7a7 : ℝ) * u^6 ≥ (p7a7 : ℝ) * u^4 := by nlinarith
  nlinarith

lemma p7_derivative_base_positive {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (p7a1 : ℝ) + 3 * p7a3 * u^2 + 5 * p7a5 * u^4 + 7 * p7a7 * u^6 > 0 := by
  have hp7a1 : (p7a1 : ℝ) = 2232394 := by norm_num [p7a1]
  have hp7a3 : (p7a3 : ℝ) = 99428805 := by norm_num [p7a3]
  have hp7a5 : (p7a5 : ℝ) = 126862841 := by norm_num [p7a5]
  have hp7a7 : (p7a7 : ℝ) = -25661520 := by norm_num [p7a7]
  have hu2_nonneg : 0 ≤ u^2 := by positivity
  have hu4_nonneg : 0 ≤ u^4 := by positivity
  have hu6_nonneg : 0 ≤ u^6 := by positivity
  have hu6_le_u4 : u^6 ≤ u^4 := by
    have hu2_le1 : u^2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg u, sq_nonneg (u^2)]
  have hp7a7_neg : (p7a7 : ℝ) < 0 := by norm_num [hp7a7]
  nlinarith

lemma p7_nonnegative {t : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ 1 / 2) : 0 ≤ p7 t := by
  unfold p7
  have hu : 0 ≤ 1 - 2 * t ∧ 1 - 2 * t ≤ 1 := ⟨by linarith, by linarith⟩
  have hbase := p7_base_positive hu.1 hu.2
  have hp7N_pos : (0 : ℝ) < p7N := by norm_num [p7N]
  have hfactor : (p7a1 : ℝ) * (1 - 2 * t) + (p7a3 : ℝ) * (1 - 2 * t) ^ 3 +
      (p7a5 : ℝ) * (1 - 2 * t) ^ 5 + (p7a7 : ℝ) * (1 - 2 * t) ^ 7 =
      (1 - 2 * t) * ((p7a1 : ℝ) + (p7a3 : ℝ) * (1 - 2 * t) ^ 2 +
      (p7a5 : ℝ) * (1 - 2 * t) ^ 4 + (p7a7 : ℝ) * (1 - 2 * t) ^ 6) := by ring
  rw [hfactor]
  apply div_nonneg
  · apply mul_nonneg (by linarith : 0 ≤ 1 - 2 * t) (le_of_lt hbase)
  · exact le_of_lt hp7N_pos

lemma p7_deriv_formula (t : ℝ) :
    deriv p7 t = (-2 / (p7N : ℝ)) *
      ((p7a1 : ℝ) + 3 * p7a3 * (1 - 2*t)^2 + 5 * p7a5 * (1 - 2*t)^4 +
        7 * p7a7 * (1 - 2*t)^6) := by
  unfold p7
  rw [deriv_div_const]
  have h1 : HasDerivAt (fun t => 1 - 2 * t) (-2) t := by
    have hid : HasDerivAt (fun t => t) 1 t := hasDerivAt_id t
    have h2t : HasDerivAt (fun t => 2 * t) 2 t := by simpa using hid.const_mul 2
    have : HasDerivAt (fun t => (1 : ℝ) - 2 * t) (0 - 2) t := by
      exact (hasDerivAt_const t 1).sub h2t
    simpa using this
  have h2 : HasDerivAt (fun t => (1 - 2 * t) ^ 3) (3 * (1 - 2 * t) ^ 2 * (-2)) t := by
    have := (hasDerivAt_pow 3 (1 - 2 * t)).comp t h1
    simpa using this
  have h3 : HasDerivAt (fun t => (1 - 2 * t) ^ 5) (5 * (1 - 2 * t) ^ 4 * (-2)) t := by
    have := (hasDerivAt_pow 5 (1 - 2 * t)).comp t h1
    simpa using this
  have h4 : HasDerivAt (fun t => (1 - 2 * t) ^ 7) (7 * (1 - 2 * t) ^ 6 * (-2)) t := by
    have := (hasDerivAt_pow 7 (1 - 2 * t)).comp t h1
    simpa using this
  have hnum : HasDerivAt (fun t => (p7a1 : ℝ) * (1 - 2 * t) + (p7a3 : ℝ) * (1 - 2 * t) ^ 3 +
      (p7a5 : ℝ) * (1 - 2 * t) ^ 5 + (p7a7 : ℝ) * (1 - 2 * t) ^ 7)
      ((p7a1 : ℝ) * (-2) + (p7a3 : ℝ) * (3 * (1 - 2 * t) ^ 2 * (-2)) +
       (p7a5 : ℝ) * (5 * (1 - 2 * t) ^ 4 * (-2)) + (p7a7 : ℝ) * (7 * (1 - 2 * t) ^ 6 * (-2))) t := by
    apply HasDerivAt.add
    apply HasDerivAt.add
    apply HasDerivAt.add
    · exact h1.const_mul _
    · exact h2.const_mul _
    · exact h3.const_mul _
    · exact h4.const_mul _
  rw [hnum.deriv]
  ring

lemma p7_deriv_negative {t : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ 1 / 2) : deriv p7 t < 0 := by
  rw [p7_deriv_formula]
  have hu0 : 0 ≤ 1 - 2 * t := by linarith
  have hu1 : 1 - 2 * t ≤ 1 := by linarith
  have hpos := p7_derivative_base_positive hu0 hu1
  have hp7N_pos : (p7N : ℝ) > 0 := by norm_num [p7N]
  have hcoeff_neg : (-2 / (p7N : ℝ)) < 0 := by exact div_neg_of_neg_of_pos (by norm_num) hp7N_pos
  exact mul_neg_of_neg_of_pos hcoeff_neg hpos

lemma p7_strictAntiOn : StrictAntiOn p7 (Set.Icc (0 : ℝ) (1 / 2)) := by
  have hcont : ContinuousOn p7 (Set.Icc (0 : ℝ) (1 / 2)) := by
    apply Continuous.continuousOn
    unfold p7
    continuity
  have hderiv : ∀ t ∈ interior (Set.Icc (0 : ℝ) (1 / 2)), deriv p7 t < 0 := by
    simp only [interior_Icc]
    intro t ht
    exact p7_deriv_negative (le_of_lt ht.1) (le_of_lt ht.2)
  apply strictAntiOn_of_deriv_neg
  · exact convex_Icc _ _
  · exact hcont
  · exact hderiv

lemma p7_weight_nonnegative {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    0 ≤ polynomialWeight p7 t := by
  unfold polynomialWeight
  have h := p7_deriv_negative ht.1 ht.2
  linarith

end

end HalfSieve
