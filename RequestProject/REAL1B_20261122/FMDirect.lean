import RequestProject.REAL1B_20261122.FMClosing

/-! Gold 4.65 Parts I–II and Gold 4.66 Part I. Fixed parameters precede the limit.
The good set is the paper's strict assignment on actual ordered prime factors. -/
namespace REAL1B.FM.Direct
open Filter Vaughan Source
noncomputable section
open Classical

def lowerEdge : ℝ := 1/5 - ε
def upperEdge : ℝ := 1/2 + ε

def tinyCost (t : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then t else max (t - r * upperEdge) 0

def rankTest {N : ℕ} (t : Fin N → ℝ) : Prop :=
  ∃ r : Fin N → ℕ, ∑ i, r i ≤ 5 ∧
    (∀ i, 0 < r i → r i * lowerEdge < t i) ∧ ∑ i, tinyCost (t i) (r i) < ε

def good (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime ∧
  rankTest (fun i : Fin n.primeFactorsList.length =>
    Real.log (n.primeFactorsList.get i) / Real.log n)

def F (x : ℝ) (n : ℕ) : ℝ :=
  if n ∈ interval (x/2) ∧ Squarefree n ∧ ¬ Direct.good n ∧ Sifted (z x) n ∧ retained n
  then kernelH n - kernelK (x/2) n else 0
def G (x : ℝ) (n : ℕ) : ℝ :=
  if n ∈ interval (x/2) ∧ Squarefree n ∧ Direct.good n then max (-kernelH n) 0 else 0
def phi (x : ℝ) (n : ℕ) := F x n - G x n
def psi (x : ℝ) (n : ℕ) := if Closing.boxes n then phi x n else 0
def outsideProfile (x : ℝ) (n : ℕ) := phi x n - psi x n

def largeSum (a x : ℝ) (f : ℕ → ℝ) := total (x/2) (fun n =>
  sieve (Closing.roughW a x) (n-2) * mu (n-2)^2 *
    Closing.coeff (Closing.cutU x) (Closing.cutD x) (n-2) * f n)
def whole (a x : ℝ) := largeSum a x (phi x)
def box (a x : ℝ) := largeSum a x (psi x)
def outside (a x : ℝ) := largeSum a x (outsideProfile x)
def primeBox (x : ℝ) := total (x/2) (fun n => actual x n * psi x n)

theorem source_split (a x : ℝ) : whole a x = box a x + outside a x := by
  unfold whole box outside largeSum total outsideProfile
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem outside_eq_mask (x : ℝ) (n : ℕ) :
    outsideProfile x n = if Closing.boxes n then 0 else phi x n := by
  by_cases h : Closing.boxes n <;> simp [outsideProfile, psi, h]

/- Ordered four-dimensional integral of (B7); the fifth coordinate is dependent. -/
def boxDomain (t : Fin 4 → ℝ) : Prop :=
  ∃ b : Fin 4 → ℕ, Closing.admissible (b 0) (b 1) (b 2) (b 3) ∧
    ∀ i, (b i : ℝ)/100 < t i ∧ t i < ((b i : ℝ)+1)/100

def face (t s : ℝ) : ℝ :=
  (if 1/2 + (if 1/5 < t then 2 else 1) * ε ≤ s then 1 else 0) +
    (if 1/2 - ε < s then 1 else 0)

def profileH (t : Fin 4 → ℝ) : ℝ :=
  2 + face (t 2) (t 0 + t 1 + t 3) + face (t 3) (t 0 + t 1 + t 2)

def J : ℝ := ∫ t : Fin 4 → ℝ, if boxDomain t then
  profileH t / ((∏ i, t i) * (1 - ∑ i, t i)) else 0

def cStar : ℝ := 17/5 * 1.000081
def enclosure : ℝ := 28449989344325252602 / 10^20

theorem splice_arithmetic :
    cStar = 3.4002754 ∧ (cStar-1)*enclosure = 0.682878095534460334193665908 ∧
    (0.682878095534460334193665908 : ℝ) < 0.682878095535 ∧
    (0.999892775499 : ℝ) - 0.682878095535 = 0.317014679964 := by
  norm_num [cStar, enclosure]

theorem five_factor_rounding (h : J ≤ enclosure) :
    (cStar-1)*J ≤ 0.682878095534460334193665908 := by
  rw [← splice_arithmetic.2.1]
  exact mul_le_mul_of_nonneg_left h (by norm_num [cStar])

def Calibration (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  |box a x - (primeBox x - J * Sb x)| ≤ e * Sb x
def ProfileUpper : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  primeBox x ≤ (cStar*J + e) * Sb x
def BoxPayment (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  box a x ≤ (0.682878095535 + e) * Sb x
def LowerLedger (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  (0.999892775499-e) * Sb x ≤ whole a x + T x
def OutsideBound (a κ : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  outside a x ≤ (0.317014679964-κ+e) * Sb x

theorem box_payment {a : ℝ} (hc : Calibration a) (hp : ProfileUpper)
    (hj : J ≤ enclosure) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) : BoxPayment a := by
  intro e he
  have h : 0 < e/2 := by linarith
  filter_upwards [hc _ h, hp _ h, hs] with x hC hP hS
  have hbound := mul_le_mul_of_nonneg_right
    ((five_factor_rounding hj).trans splice_arithmetic.2.2.1.le) hS.le
  linarith only [(abs_le.mp hC).2, hP, hbound]

theorem reserve {a κ : ℝ} (hl : LowerLedger a) (hb : BoxPayment a)
    (ho : OutsideBound a κ) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (κ-e)*Sb x ≤ T x := by
  intro e he
  have h : 0 < e/3 := by linarith
  filter_upwards [hl _ h, hb _ h, ho _ h] with x hL hB hO
  rw [source_split] at hL
  linarith only [hL, hB, hO]

theorem eventual_positive {a κ : ℝ} (hk : 0 < κ) (hl : LowerLedger a)
    (hb : BoxPayment a) (ho : OutsideBound a κ) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    ∀ᶠ x : ℝ in atTop, 0 < T x := by
  filter_upwards [reserve hl hb ho (κ/2) (by linarith), hs] with x ht hS
  exact (mul_pos (by linarith : 0 < κ-κ/2) hS).trans_le ht

theorem infinite_of_direct {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hk : 0 < κ)
    (hl : LowerLedger a) (hb : BoxPayment a) (ho : OutsideBound a κ)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  apply infinite_of_unbounded_mass
  intro M
  obtain ⟨x,hx,hT⟩ := ((eventually_gt_atTop (2*(M:ℝ))).and
    (eventual_positive hk hl hb ho hs)).exists
  exact ⟨x/2, by linarith, hT.trans_le (T_le_native x)⟩

end
end REAL1B.FM.Direct

#print axioms REAL1B.FM.Direct.source_split
#print axioms REAL1B.FM.Direct.outside_eq_mask
#print axioms REAL1B.FM.Direct.splice_arithmetic
#print axioms REAL1B.FM.Direct.five_factor_rounding
#print axioms REAL1B.FM.Direct.box_payment
#print axioms REAL1B.FM.Direct.reserve
#print axioms REAL1B.FM.Direct.eventual_positive
#print axioms REAL1B.FM.Direct.infinite_of_direct
