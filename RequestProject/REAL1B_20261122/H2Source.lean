import RequestProject.REAL1B_20261122.Vaughan

namespace REAL1B.H2
open Filter Vaughan MeasureTheory
noncomputable section
open Classical

/-- k indexes the possible odd-prime factors p=k+3 of the Euler product. -/
def offset (k : ℕ) : ℝ := if (k+3).Prime then -(1 / ((k:ℝ)+2)^2) else 0
def series : ℝ := 2 * ∏' k : ℕ, (1 + offset k)

private theorem summable_offset : Summable offset := by
  have hs := (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  apply hs.of_norm_bounded
  intro k
  by_cases h : (k+3).Prime <;> (simp [offset, h, Nat.cast_add, Real.norm_eq_abs]; first | positivity | done)

theorem euler_converges : Multipliable (fun k : ℕ => 1 + offset k) :=
  Real.multipliable_one_add_of_summable summable_offset

theorem series_pos : 0 < series := by
  have hpos (k : ℕ) : 0 < 1 + offset k := by
    by_cases h : (k+3).Prime
    · have hk : 1 < ((k:ℝ)+2)^2 := by nlinarith [sq_nonneg (k:ℝ), (Nat.cast_nonneg k : 0 ≤ (k:ℝ))]
      have := (div_lt_one (by positivity : 0 < ((k:ℝ)+2)^2)).mpr hk
      simp only [offset, if_pos h]
      linarith
    · simp [offset,h]
  unfold series
  rw [← Real.rexp_tsum_eq_tprod hpos (Real.summable_log_one_add_of_summable summable_offset)]
  positivity

def N0 (X : ℝ) := series * X / Real.log X
theorem scale_pos {X : ℝ} (hx : 1 < X) : 0 < N0 X :=
  div_pos (mul_pos series_pos (by linarith)) (Real.log_pos hx)

/-- The ordered simplex has t₃=1-t₁-t₂, t₁>1/4, t₁<t₂<t₃. -/
def I3 : ℝ := ∫ t : ℝ in Set.Ioo (1/4 : ℝ) (1/3),
  ∫ u : ℝ in Set.Ioo t ((1-t)/2), 1 / (t*u*(1-t-u))
def cB : ℝ := 7/2 * Real.log 3 - 4 * Real.log 2
def rho3 : ℝ := 1 - Real.log 3 + I3
def tripleCoeff : ℝ := 10/3 * I3
def margin : ℝ := cB - 2*tripleCoeff + rho3 - 1/8
def unsigned (X : ℝ) := mass X (fun n => mu n ^ 2 * roughMask n)
def triple (X : ℝ) := mass X (classMask 3)
def gammaQ (X : ℝ) := mass X native + rho3 * N0 X

/-- All epsilons are fixed before X tends to infinity. -/
def negligible (f : ℝ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, |f X| ≤ ε * N0 X
def H1Consequence : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, (cB - ε) * N0 X ≤ unsigned X
def TripleCap : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, triple X ≤ (tripleCoeff + ε) * N0 X
def TypeICalibration := negligible (fun X => typeI X + rho3 * N0 X)
def FinalTypeII : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, typeII X ≤ (1/8 + ε) * N0 X
def GammaBound : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ X in atTop, gammaQ X ≤ (1/8 + ε) * N0 X

theorem gamma_split (X : ℝ) :
    gammaQ X - typeII X = (typeI X + rho3*N0 X) +
      lowOutput X + primeCorrection X + collar X := by
  unfold gammaQ
  rw [native_vaughan]
  ring

theorem gamma_approx (hi : TypeICalibration) (hl : negligible lowOutput)
    (hp : negligible primeCorrection) (hc : negligible collar) :
    negligible (fun X => gammaQ X - typeII X) := by
  intro ε he
  have hd : 0 < ε/4 := by linarith
  filter_upwards [hi _ hd, hl _ hd, hp _ hd, hc _ hd] with X h₁ h₂ h₃ h₄
  rw [gamma_split, abs_le]
  have a := abs_le.mp h₁
  have b := abs_le.mp h₂
  have c := abs_le.mp h₃
  have d := abs_le.mp h₄
  constructor <;> linarith

theorem gamma_of_typeII (h : negligible (fun X => gammaQ X - typeII X))
    (hs : FinalTypeII) : GammaBound := by
  intro ε he
  have hd : 0 < ε/2 := by linarith
  filter_upwards [h _ hd, hs _ hd] with X ha hb
  have := (abs_le.mp ha).2
  linarith

theorem infinite_of_gamma (hm : 0 < margin) (h₁ : H1Consequence)
    (h₃ : TripleCap) (hs : GammaBound) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  apply infinite_of_unbounded_mass
  intro B
  let δ := margin/8
  have hd : 0 < δ := by dsimp [δ]; linarith
  have ev : ∀ᶠ X : ℝ in atTop, (B : ℝ) < X ∧ 0 < mass X primeMask := by
    filter_upwards [eventually_gt_atTop (B:ℝ), eventually_gt_atTop (1:ℝ),
      h₁ _ hd, h₃ _ hd, hs _ hd] with X hb hx ha ht hg
    refine ⟨hb, ?_⟩
    have hn := mul_pos hm (scale_pos hx)
    have hi := h2_identity X
    change mass X (fun n => mu n * roughMask n) + rho3 * N0 X ≤ _ at hg
    unfold unsigned at ha
    unfold triple at ht
    dsimp [δ, margin] at hn ha ht hg
    linarith
  exact ev.exists

/-- Native Gold 4.53-B route with each analytic obligation displayed separately. -/
theorem infinite_of_vaughan (hm : 0 < margin) (h₁ : H1Consequence)
    (h₃ : TripleCap) (hi : TypeICalibration) (hl : negligible lowOutput)
    (hp : negligible primeCorrection) (hc : negligible collar) (hs : FinalTypeII) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_gamma hm h₁ h₃ (gamma_of_typeII (gamma_approx hi hl hp hc) hs)

end
end REAL1B.H2

#print axioms REAL1B.H2.euler_converges
#print axioms REAL1B.H2.series_pos
#print axioms REAL1B.H2.scale_pos
#print axioms REAL1B.H2.gamma_split
#print axioms REAL1B.H2.gamma_approx
#print axioms REAL1B.H2.gamma_of_typeII
#print axioms REAL1B.H2.infinite_of_gamma
#print axioms REAL1B.H2.infinite_of_vaughan
