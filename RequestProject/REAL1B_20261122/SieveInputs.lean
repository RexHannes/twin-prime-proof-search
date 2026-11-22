import RequestProject.REAL1B_20261122.Margin
import RequestProject.REAL1B_20261122.OutputErrors

namespace REAL1B.H2
open Filter Vaughan
noncomputable section
open Classical

/-- A fixed choice of centers and signed, finitely supported remainder
coefficients at a scale. In the paper they come from lower/upper linear sieves. -/
structure CenteredRow where
  center : ℝ
  coeff : ℕ →₀ ℝ
def CenteredRow.eval (r : CenteredRow) (n : ℕ) := r.center +
  r.coeff.sum (fun d w => w * ((if d ∣ n then 1 else 0) - (Nat.totient d : ℝ)⁻¹))

structure H1Rows where
  lower : ℝ → CenteredRow
  upper : ℝ → ℕ → CenteredRow

def markers (X : ℝ) (n : ℕ) := n.primeFactors.filter
  (fun p : ℕ => X < (p:ℝ)^7 ∧ (p:ℝ)^4 ≤ 2*X)
def lowerKernel (r : H1Rows) (X : ℝ) (n : ℕ) := if Odd n then
  (r.lower X).eval n - ∑ p ∈ markers X n, (r.upper X p).eval (n/p) else 0
def squarefreeLower (r : H1Rows) (X : ℝ) := mass X (fun n => mu n ^ 2 * lowerKernel r X n)

/-- Singleton consequences needed of the particular fixed rows. The least marker
requires a unit upper weight; all other markers require nonnegative upper weights. -/
def SingletonBounds (r : H1Rows) (X : ℝ) := ∀ n ∈ interval X, Odd n →
  (r.lower X).eval n ≤ (if X < (n.minFac:ℝ)^7 then 1 else 0) ∧
  (∀ p ∈ markers X n, 0 ≤ (r.upper X p).eval (n/p)) ∧
  (n.minFac ∈ markers X n → 1 ≤ (r.upper X n.minFac).eval (n/n.minFac))

theorem minorant {r : H1Rows} {X : ℝ} (hx : 1 ≤ X) (hs : SingletonBounds r X)
    {n : ℕ} (hn : n ∈ interval X) : lowerKernel r X n ≤ roughMask n := by
  by_cases ho : Odd n
  · obtain ⟨hl,hu,hm⟩ := hs n hn ho
    rw [lowerKernel, if_pos ho]
    have hsum := Finset.sum_nonneg hu
    by_cases hr : Rough n
    · rw [roughMask, if_pos hr]
      split_ifs at hl <;> linarith
    · rw [roughMask, if_neg hr]
      by_cases h7 : X < (n.minFac:ℝ)^7
      · have h4 : n.minFac^4 ≤ n := le_of_not_gt hr
        have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hbig := (Nat.le_floor_iff (by linarith : 0 ≤ 2*X)).mp hi.2
        have hp : n.minFac ∈ markers X n := by
          apply Finset.mem_filter.mpr
          refine ⟨Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd n,by omega⟩,h7,?_⟩
          exact (show (n.minFac:ℝ)^4 ≤ (n:ℝ) by exact_mod_cast h4).trans hbig
        have hb := Finset.single_le_sum (f := fun p => (r.upper X p).eval (n/p)) hu hp
        rw [if_pos h7] at hl
        linarith [hm hp]
      · rw [if_neg h7] at hl
        linarith
  · simp [lowerKernel,ho,roughMask]; split_ifs <;> norm_num

theorem squarefreeLower_le {r : H1Rows} {X : ℝ} (hx : 1 ≤ X) (hs : SingletonBounds r X) :
    squarefreeLower r X ≤ unsigned X := by
  unfold squarefreeLower unsigned
  rw [mass_as_sum, mass_as_sum]
  unfold total
  apply Finset.sum_le_sum
  intro n hn
  have hθ : 0 ≤ theta (n-2) := by
    unfold theta
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · rfl
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (minorant hx hs hn) (sq_nonneg _)) hθ

/-- One row family per fixed tolerance, chosen before the eventual quantifier.
H1's mean estimate and the validity of the constructed sieve rows are inputs. -/
def H1PaperInput : Prop := ∀ ε : ℝ, 0 < ε → ∃ r : H1Rows,
  ∀ᶠ X : ℝ in atTop, SingletonBounds r X ∧ (cB-ε)*N0 X ≤ squarefreeLower r X

theorem h1_consequence (hp : H1PaperInput) : H1Consequence := by
  intro ε he
  obtain ⟨r,hr⟩ := hp ε he
  filter_upwards [hr,eventually_ge_atTop (1:ℝ)] with X h hx
  exact h.2.trans (squarefreeLower_le hx h.1)

/-- Positive population of the fixed-to-relative cutoff collar. -/
def collarMass (X : ℝ) := mass X (fun n =>
  if X < (n.minFac:ℝ)^4 ∧ ¬ Rough n then 1 else 0)

theorem abs_collar_le (X : ℝ) : |collar X| ≤ collarMass X := by
  rw [collarMass, mass_as_sum]
  unfold collar total
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro n hn
  have hx := (Finset.mem_filter.mp hn).2
  have hm : |mu n| ≤ 1 := by unfold mu; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have ht : 0 ≤ theta (n-2) := by
    unfold theta
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · rfl
  simp only [abs_mul, abs_of_nonneg ht]
  apply mul_le_mul_of_nonneg_left _ ht
  by_cases hr : Rough n
  · have h4 : (n:ℝ) < (n.minFac:ℝ)^4 := by exact_mod_cast hr
    simp [native, roughMask, hr, fixed, hx.trans h4]
  · by_cases hf : X < (n.minFac:ℝ)^4 <;> simp [native, roughMask, hr, fixed, hf, hm]

theorem collar_negligible (h : negligible collarMass) : negligible collar := by
  intro ε he
  filter_upwards [h ε he] with X hx
  exact (abs_collar_le X).trans ((le_abs_self _).trans hx)

/-- An explicit conservative conditional reserve using the certified simplex bound. -/
theorem eventual_mass_lower (h₁ : H1Consequence) (h₃ : TripleCap) (hs : GammaBound) :
    ∀ᶠ X : ℝ in atTop, N0 X / 16000 < mass X primeMask := by
  have hd : (0:ℝ) < 1/32000 := by norm_num
  filter_upwards [h₁ _ hd, h₃ _ hd, hs _ hd, eventually_gt_atTop (1:ℝ)] with X ha ht hg hx
  have hm := mul_lt_mul_of_pos_right margin_floor (scale_pos hx)
  have hi := h2_identity X
  change mass X (fun n => mu n * roughMask n) + rho3 * N0 X ≤ _ at hg
  unfold unsigned at ha
  unfold triple at ht
  unfold margin at hm
  linarith

theorem infinite_of_paper_inputs (h₁ : H1PaperInput) (h₃ : TripleCap)
    (hI : TypeICalibration) (hc : negligible collarMass) (hII : FinalTypeII) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_vaughan margin_positive (h1_consequence h₁) h₃ hI low_negligible
    correction_negligible (collar_negligible hc) hII

end
end REAL1B.H2

#print axioms REAL1B.H2.minorant
#print axioms REAL1B.H2.squarefreeLower_le
#print axioms REAL1B.H2.h1_consequence
#print axioms REAL1B.H2.abs_collar_le
#print axioms REAL1B.H2.collar_negligible
#print axioms REAL1B.H2.eventual_mass_lower
#print axioms REAL1B.H2.infinite_of_paper_inputs
