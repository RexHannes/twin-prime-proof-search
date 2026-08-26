import RequestProject.NANC.Gate01Switch.FixedCellConvolution

/-!
# Gate01Switch: the Q5 equation `mn + 2 = dpr`

Inserting a fixed-cell coefficient of convolution shape into the generic
switched operator produces, at each `(d, p, r)`, the inner sum over the
factorisations of `dpr - 2`.  The exact support condition is

`mn = dpr - 2`,  equivalently  `mn + 2 = dpr`.  (Q5-EQ)

All of this is finite algebra: no cancellation of any kind is proved.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open ArithmeticFunction Finset

/-- **(Q5-EQ)** — the shifted support equation. -/
theorem q5_equation {m n t : ℕ} (h2 : 2 ≤ t) : m * n = t - 2 ↔ m * n + 2 = t := by
  omega

/-- The `Q5` fibre over `t`: the ordered pairs `(m, n)` with `1 ≤ m, n ≤ K` and
`mn + 2 = t`. -/
def q5Fibre (K t : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 K) ×ˢ (Finset.Icc 1 K)).filter (fun mn => mn.1 * mn.2 + 2 = t)

theorem mem_q5Fibre {K t : ℕ} {mn : ℕ × ℕ} :
    mn ∈ q5Fibre K t ↔ (1 ≤ mn.1 ∧ mn.1 ≤ K) ∧ (1 ≤ mn.2 ∧ mn.2 ≤ K) ∧ mn.1 * mn.2 + 2 = t := by
  simp only [q5Fibre, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- The divisor antidiagonal of the shifted argument is *exactly* the `Q5`
fibre, provided `2 ≤ t ≤ K + 2`. -/
theorem divisorsAntidiagonal_shift_eq_q5Fibre {K t : ℕ} (h2 : 2 ≤ t) (hK : t ≤ K + 2) :
    (t - 2).divisorsAntidiagonal = q5Fibre K t := by
  ext mn
  rw [Nat.mem_divisorsAntidiagonal, mem_q5Fibre]
  constructor
  · rintro ⟨hprod, hne⟩
    have hm : 1 ≤ mn.1 := by
      rcases Nat.eq_zero_or_pos mn.1 with h | h
      · exact absurd (by rw [← hprod, h, Nat.zero_mul]) hne
      · exact h
    have hn : 1 ≤ mn.2 := by
      rcases Nat.eq_zero_or_pos mn.2 with h | h
      · exact absurd (by rw [← hprod, h, Nat.mul_zero]) hne
      · exact h
    have hle1 : mn.1 ≤ mn.1 * mn.2 := Nat.le_mul_of_pos_right _ hn
    have hle2 : mn.2 ≤ mn.1 * mn.2 := Nat.le_mul_of_pos_left _ hm
    obtain ⟨s, hs⟩ : ∃ s, mn.1 * mn.2 = s := ⟨_, rfl⟩
    rw [hs] at hprod hle1 hle2 ⊢
    exact ⟨⟨hm, by omega⟩, ⟨hn, by omega⟩, by omega⟩
  · rintro ⟨⟨hm, hmK⟩, ⟨hn, hnK⟩, hsum⟩
    have hpos : 1 ≤ mn.1 * mn.2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    obtain ⟨s, hs⟩ : ∃ s, mn.1 * mn.2 = s := ⟨_, rfl⟩
    rw [hs] at hsum hpos ⊢
    exact ⟨by omega, by omega⟩

/-- The shifted convolution value displayed on the `Q5` support. -/
theorem dconv_shift_eq_q5Fibre_sum (a b : ℕ → ℝ) {K t : ℕ} (h2 : 2 ≤ t) (hK : t ≤ K + 2) :
    dconv a b (t - 2) = ∑ mn ∈ q5Fibre K t, a mn.1 * b mn.2 := by
  rw [dconv, divisorsAntidiagonal_shift_eq_q5Fibre h2 hK]

/-- Multiplier-set members give arguments in the admissible range. -/
theorem multiplierSet_bounds {K q r : ℕ} (hq : 0 < q) (hr : r ∈ multiplierSet K q) :
    2 ≤ q * r ∧ q * r ≤ K + 2 :=
  ⟨((mem_multiplierSet hq).mp hr).2.1, ((mem_multiplierSet hq).mp hr).2.2⟩

/-- **The exact Q5 reindexing of the generic switched coefficient sum.**  With
`c = α * β` the generic switched main sum becomes a finite sum over
`(m, n, d, p, r)` supported exactly on `mn + 2 = dpr`, with all finite weights
retained and no cancellation asserted. -/
theorem genericSwitched_q5_expansion (Qset : Finset ℕ) (U V K : ℕ) (a b : ℕ → ℝ) :
    pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K (dconv a b)) =
      ∑ x ∈ genericPart (divisorPairs Qset U V),
        ∑ r ∈ multiplierSet K (x.1 * x.2),
          (moebius x.1 : ℝ) * Λ x.2 * ∑ mn ∈ q5Fibre K (x.1 * x.2 * r), a mn.1 * b mn.2 := by
  rw [pairSum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hq : 0 < x.1 * x.2 := Nat.pos_of_ne_zero (mem_genericPart_divisorPairs.mp hx).2.2.2.2.2
  rw [coeffWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨h2, hle⟩ := multiplierSet_bounds hq hr
  rw [dconv_shift_eq_q5Fibre_sum a b h2 hle]

/-- **Support statement.**  Every quintuple `(m, n, d, p, r)` occurring in the
expansion satisfies the Q5 equation `mn + 2 = dpr`, with `p` prime, `p ∤ d`,
`U < d`, `V < p` and `dp ∈ Qset`. -/
theorem genericSwitched_q5_support {Qset : Finset ℕ} {U V K : ℕ} {x : ℕ × ℕ} {r : ℕ}
    {mn : ℕ × ℕ} (hx : x ∈ genericPart (divisorPairs Qset U V))
    (hmn : mn ∈ q5Fibre K (x.1 * x.2 * r)) :
    mn.1 * mn.2 + 2 = x.1 * x.2 * r ∧ x.2.Prime ∧ ¬ x.2 ∣ x.1 ∧ U < x.1 ∧ V < x.2 ∧
      x.1 * x.2 ∈ Qset := by
  obtain ⟨hU, hV, hp, hnd, hmem, -⟩ := mem_genericPart_divisorPairs.mp hx
  exact ⟨(mem_q5Fibre.mp hmn).2.2, hp, hnd, hU, hV, hmem⟩

/-- With a fixed-cell coefficient of shape (C9), the generic switched operator
splits exactly into its `Q5` part and the separate error-term part.  The error
term `E_j` is kept separate; nothing is estimated. -/
theorem genericSwitched_R9_split (Qset : Finset ℕ) (U V K : ℕ) (c : ℕ → ℝ) (kappa : ℝ)
    (a b Ej : ℕ → ℝ) (hc : R9CellConvolution c kappa a b Ej) (E : ℕ → ℝ) :
    genericSwitchedOperator Qset U V K c E =
      kappa * pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K (dconv a b))
      + pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K Ej)
      - pairSum (genericPart (divisorPairs Qset U V)) (expectedWeight E) := by
  have key : pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K c) =
      kappa * pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K (dconv a b))
      + pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K Ej) := by
    rw [pairSum, pairSum, pairSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hw : coeffWeight K c x.1 x.2 =
        kappa * coeffWeight K (dconv a b) x.1 x.2 + coeffWeight K Ej x.1 x.2 := by
      simp only [coeffWeight, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => hc _
    rw [hw]; ring
  rw [genericSwitchedOperator, switchedStratum, key]

end Gate01Switch
end TwinPrimeProject
