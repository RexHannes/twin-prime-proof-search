import RequestProject.REAL1B_20261122.FMRankTwo

namespace REAL1B.FM.Ledger
open Filter Vaughan Source Analytic
noncomputable section
open Classical

def UpperLedger (a u : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  Direct.whole a x + T x ≤ (u+e)*Sb x
def BoxLower (a b : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  (b-e)*Sb x ≤ Direct.box a x
def Reserve (r : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (r-e)*Sb x ≤ T x

theorem reserve_of_outside {a κ : ℝ} (hl : Direct.LowerLedger a) (hb : Direct.BoxPayment a)
    (ho : Direct.OutsideBound a κ) : Reserve κ := Direct.reserve hl hb ho

/-- A lower bound on the physical box appears with a plus sign in the recovered saving. -/
theorem outside_of_reserve {a b u r : ℝ} (hu : UpperLedger a u) (hb : BoxLower a b)
    (hr : Reserve r) : Direct.OutsideBound a (0.317014679964+b+r-u) := by
  intro e he
  have ht : 0 < e/3 := by linarith
  filter_upwards [hu _ ht,hb _ ht,hr _ ht] with x hU hB hR
  linarith only [hU,hB,hR,Direct.source_split a x]

theorem matched_ledgers {a κ : ℝ} (hl : Direct.LowerLedger a) (hu : UpperLedger a 0.999892775499)
    (hb : Direct.BoxPayment a) (hfloor : BoxLower a 0.682878095535) :
    Direct.OutsideBound a κ ↔ Reserve κ := by
  refine ⟨reserve_of_outside hl hb,fun hr => ?_⟩
  convert outside_of_reserve hu hfloor hr using 1
  ring

/-- The one-sided numerical ledgers alone admit an explicit countermodel.
The variables are normalized scalars; this makes no assumption about the native primes. -/
theorem upper_box_insufficient : ∃ t box outside : ℝ,
    t = 0.01 ∧ t+box+outside = 0.999892775499 ∧ box ≤ 0.682878095535 ∧
    0.317014679964-0.01 < outside := by
  exact ⟨0.01,0,0.989892775499,by norm_num⟩

theorem upper_rounding : 1+goodCap+pairCap+0.000107163+tailCap+transferCap ≤ (1.000107183501:ℝ) := by
  norm_num [goodCap,pairCap,tailCap,transferCap,ε,ν,Nat.factorial]

private theorem positive_nonneg (x : ℝ) : 0 ≤ weighted actual positive x := by
  unfold weighted total
  apply Finset.sum_nonneg
  intro n _
  have ht : 0 ≤ theta (n-2) := by unfold theta; split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  have hA : 0 ≤ actual x n := by unfold actual sieve; split_ifs <;> simp [ht]
  apply mul_nonneg hA
  unfold positive
  split_ifs <;> first | exact le_max_right _ _ | rfl

/-- Gold 4.58 Part V (4.2) uses the lower side of the omitted rank-two estimate.
The proof retains the error signs in the physical covariance identity. -/
theorem upper_of_estimates {a : ℝ} (hs : ScaleLower) (h : Estimates)
    (hpair : upper (fun x => -deviation (omitted (· = 2)) x) pairCap)
    (hr : Closing.Reduction a) : UpperLedger a 1.000107183501 := by
  obtain ⟨j,hj,hB,_⟩ := h.goodMass
  intro e he
  have ht : 0 < e/8 := by linarith
  filter_upwards [geometry,comparator_pos hs,hB _ ht,hpair _ ht,h.four _ ht,h.tail _ ht,
    h.calibratedMean _ ht,powerError_small hs (output_support geometry) _ ht,h.comparator _ ht,hr _ ht]
    with x hg hx hB hpair hfour htail hmean hpow hcomp hred
  rw [Direct.whole_eq_legacy]
  have hc := mul_le_mul_of_nonneg_right upper_rounding hx.le
  have hj' := mul_le_mul_of_nonneg_right (hj.trans good_cap_rounding.le) hx.le
  linarith only [exact_ledger hg,positive_nonneg x,hc,hj',(abs_le.mp hB).2,hpair,
    (abs_le.mp hfour).1,(abs_le.mp htail).1,(abs_le.mp hmean).2,(abs_le.mp hpow).2,
    (abs_le.mp hcomp).1,(abs_le.mp hred).1]

theorem upper_of_pair_comparator {a : ℝ} (hs : ScaleLower) (h : Estimates)
    (hpair : upper (weighted compare (omitted (·=2))) pairCap) (hr : Closing.Reduction a) :
    UpperLedger a 1.000107183501 :=
  upper_of_estimates hs h (lower_pair_of_comparator hpair) hr

end
end REAL1B.FM.Ledger
#print axioms REAL1B.FM.Ledger.reserve_of_outside
#print axioms REAL1B.FM.Ledger.outside_of_reserve
#print axioms REAL1B.FM.Ledger.matched_ledgers
#print axioms REAL1B.FM.Ledger.upper_box_insufficient
#print axioms REAL1B.FM.Ledger.upper_rounding
#print axioms REAL1B.FM.Ledger.upper_of_estimates
#print axioms REAL1B.FM.Ledger.upper_of_pair_comparator
