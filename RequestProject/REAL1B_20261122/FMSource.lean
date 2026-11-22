import RequestProject.REAL1B_20261122.Vaughan
import RequestProject.REAL1B_20261122.FMResidual

/-! Gold 4.53-FM §1 and the literal Gold 4.48-FM Appendix H divisor kernels. -/
namespace REAL1B.FM.Source
open ArithmeticFunction Filter Vaughan
noncomputable section
open Classical

def ε : ℝ := 1 / 10^9
def ν : ℝ := 1/5 - 2*ε
def β : ℝ := 1/2 - 2*ε
def γ : ℝ := 1/2 - ε
def y (x : ℝ) := Real.exp ((Real.log x) ^ (1/20 : ℝ))
def z (x : ℝ) := x ^ (1/400000000000 : ℝ)
def markCut (X : ℝ) := Real.exp (Real.log X / (Real.log (Real.log X))^10)
def density (x : ℝ) := ∏ p ∈ (Finset.range (⌊y x⌋₊+1)).filter Nat.Prime, (1 - (1:ℝ)/p)
def actual (x : ℝ) (n : ℕ) := sieve (y x) n * theta (n-2)
def compare (x : ℝ) (n : ℕ) := sieve (y x) n * sieve (y x) (n-2) / density x

def profile (n : ℕ) (ps : List ℕ) := ps.map (fun p => Real.log p / Real.log n)
def g0 : List ℝ → ℝ
  | [] => 1
  | [t] => if 1/5 < t ∧ t ≤ 1/2 then -1 else 0
  | [t,u] => if 1/5 < t ∧ 1/5 < u ∧ t+u < 1/2 then 1 else 0
  | _ => 0

def divisorCoefficient (n d : ℕ) : ℝ :=
  let small := d.primeFactorsList.filter (fun p : ℕ => decide ((p:ℝ) < (n:ℝ)^ν))
  let big := d.primeFactorsList.filter (fun p : ℕ => decide ((n:ℝ)^ν ≤ (p:ℝ)))
  let ts := profile n big
  if (d:ℝ) ≤ (n:ℝ)^γ ∧ ts.sum ≤ β then mu small.prod * g0 ts else 0
def kernelH (n : ℕ) := ∑ d ∈ n.divisors, divisorCoefficient n d

/-- Coagulation groups coordinates of a fundamental vector into nonempty blocks.
The forbidden closed interval applies to every nonempty proper subsum. -/
def fundamental (v : List ℝ) : Prop :=
  v.sum = 1 ∧ (∀ t ∈ v, 0 < t ∧ t < 1 - γ) ∧
  ∀ u : List ℝ, u.Sublist v → u ≠ [] → u.length < v.length →
    u.sum < ε ∨ ε + ν < u.sum
def good (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∃ blocks : List (List ℝ),
    (∀ b ∈ blocks, b ≠ []) ∧ fundamental blocks.flatten ∧
    (blocks.map List.sum).Perm (profile n n.primeFactorsList)

def inBank (X a b : ℝ) (k : ℕ) : Prop := X^a < (k:ℝ) ∧ (k:ℝ) ≤ X^b
def labels (X : ℝ) (d : ℕ) : ℕ :=
  ∑ u ∈ d.divisors, ∑ v ∈ (d/u).divisors, ∑ w ∈ (d/u/v).divisors,
    if u.Prime ∧ v.Prime ∧ w.Prime ∧ inBank X 0.0265 0.028 u ∧
      inBank X 0.0105 0.0115 v ∧ inBank X 0.0115 0.0125 w ∧
      inBank X 0.463 0.465 (d/u/v/w) then 1 else 0
def kernelK (X : ℝ) (n : ℕ) :=
  mu n ^ 2 * sieve (markCut X) n *
    ∑ d ∈ n.divisors, mu d * ((labels X d : ℝ) / 64^3) *
      (1 - (Real.log d)^2 / (Real.log n)^2)

def retained (n : ℕ) : Prop := cardFactors n = 3 ∨
  (5 ≤ cardFactors n ∧ cardFactors n ≤ 255)
def residual (x : ℝ) := total (x/2) (fun n =>
  if Squarefree n ∧ ¬ good n ∧ Sifted (z x) n ∧ retained n then
    (actual x n - compare x n) * (kernelH n - kernelK (x/2) n) else 0)
def companion (x : ℝ) := total (x/2) (fun n =>
  if Squarefree n ∧ good n then actual x n * max (-kernelH n) 0 else 0)
def T (x : ℝ) := total (x/2) (fun n => actual x n * primeMask n)
def Sb (x : ℝ) := total (x/2) (fun n => compare x n * primeMask n)

private theorem theta_nonneg (t : ℕ) : 0 ≤ theta t := by
  unfold theta
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · rfl

theorem companion_nonneg (x : ℝ) : 0 ≤ companion x := by
  unfold companion total
  apply Finset.sum_nonneg
  intro n _
  unfold actual sieve
  have ht := theta_nonneg (n-2)
  split_ifs <;> positivity

theorem T_le_native (x : ℝ) : T x ≤ mass (x/2) primeMask := by
  rw [mass_as_sum]
  unfold T total
  apply Finset.sum_le_sum
  intro n _
  simp only [actual, sieve]
  by_cases h : Sifted (y x) n
  · simp [h]
  · simp [h, primeMask]
    split_ifs <;> simp [theta_nonneg]

/-- Quantified one-sided comparison and residual hypotheses from 4.53-FM §1. -/
def Lower : Prop := ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
  (0.361755018 - (10:ℝ)⁻¹^58) * Sb x + companion x - residual x - η * Sb x ≤ T x
def ResidualBound : Prop := ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
  residual x - companion x ≤ (0.359892818 + η) * Sb x

theorem infinite_of_source_residual (hL : Lower) (hR : ResidualBound)
    (hS : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  apply infinite_of_unbounded_mass
  intro B
  have he : (0:ℝ) < 0.0001 := by norm_num
  obtain ⟨x,hb,hl,hr,hs⟩ := (Filter.Eventually.and (eventually_gt_atTop (2*(B:ℝ)))
    ((hL _ he).and ((hR _ he).and hS))).exists
  refine ⟨x/2, by linarith, ?_⟩
  have h := REAL1B.FM.current_margin (T x) (Sb x) (companion x) (residual x)
    (0.0001 * Sb x) (0.0001 * Sb x) hl (by linarith)
  have hc : (0:ℝ) < 0.0018622 - (10:ℝ)⁻¹^58 - 2*0.0001 := by norm_num
  linarith only [mul_pos hc hs, h, T_le_native x]

end
end REAL1B.FM.Source

#print axioms REAL1B.FM.Source.companion_nonneg
#print axioms REAL1B.FM.Source.T_le_native
#print axioms REAL1B.FM.Source.infinite_of_source_residual
