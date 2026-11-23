import RequestProject.REAL1B_20261122.FMDirect

/-! Gold 4.66 Part III, (2), (4), (15). Keep the native outside profile on
both label ranges so that no pointwise output theorem is silently assumed. -/
namespace REAL1B.FM.Direct
open Filter Vaughan Source Closing
noncomputable section
open Classical

def clean (x : ℝ) (n : ℕ) : Prop :=
  n ∈ interval (x/2) ∧ ∃ q h s : ℕ, n = q*h*s ∧ q.Prime ∧ h.Prime ∧ Squarefree s ∧
    inBank x 0.4899 0.490 q ∧ inBank x 0.0199 0.020 h ∧ inBank x 0.4901 0.4902 s ∧
    Sifted (x^(0.031:ℝ)) s ∧ ∀ p : ℕ, p.Prime → p ∣ s →
      (p:ℝ) < x^(0.19999:ℝ) ∨ x^(0.20001:ℝ) < (p:ℝ)

def labelSum (x : ℝ) (k : ℕ) (pick : ℕ → Prop) : ℝ := ∑ l ∈ k.divisors,
  if l.Prime ∧ cutU x < (l:ℝ) ∧ pick l then primeRow (cutU x) (cutD x) k l else 0

def cleanSum (a x : ℝ) (pick : ℕ → Prop) := total (x/2) (fun n =>
  if clean x n then sieve (roughW a x) (n-2) * mu (n-2)^2 * labelSum x (n-2) pick *
    outsideProfile x n else 0)
def lowLabel (a x : ℝ) := cleanSum a x (fun l => (l:ℝ) ≤ x^(0.2697:ℝ))
def unpaid (a x : ℝ) := largeSum a x (fun n => if clean x n then 0 else outsideProfile x n) +
  cleanSum a x (fun l => x^(0.2697:ℝ) < (l:ℝ))

theorem outside_label_split (a x : ℝ) : outside a x = unpaid a x + lowLabel a x := by
  have split (k : ℕ) : coeff (cutU x) (cutD x) k =
      labelSum x k (fun l => x^(0.2697:ℝ) < (l:ℝ)) +
      labelSum x k (fun l => (l:ℝ) ≤ x^(0.2697:ℝ)) := by
    unfold coeff labelSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hp : l.Prime <;> by_cases hu : cutU x < (l:ℝ) <;>
      by_cases h : x^(0.2697:ℝ) < (l:ℝ) <;> simp [hp, hu, h, not_le.mpr, le_of_not_gt]
  unfold outside unpaid lowLabel cleanSum largeSum total
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : clean x n
  · simp only [if_pos h, mul_zero, zero_add, split]
    ring
  · simp [h]

def LowLabelEstimate (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  |lowLabel a x| ≤ e * Sb x

theorem outside_iff_unpaid {a κ : ℝ} (hlo : LowLabelEstimate a) :
    OutsideBound a κ ↔ ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
      unpaid a x ≤ (0.317014679964-κ+e)*Sb x := by
  constructor <;> intro h e he
  · have hε : 0 < e/2 := by linarith
    filter_upwards [h _ hε, hlo _ hε] with x hO hL
    rw [outside_label_split] at hO
    linarith only [hO,(abs_le.mp hL).1]
  · have hε : 0 < e/2 := by linarith
    filter_upwards [h _ hε, hlo _ hε] with x hU hL
    rw [outside_label_split]
    linarith only [hU,(abs_le.mp hL).2]

end
end REAL1B.FM.Direct
#print axioms REAL1B.FM.Direct.outside_label_split
#print axioms REAL1B.FM.Direct.outside_iff_unpaid
