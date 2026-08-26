/-
NANC V5 — EPSILON LEDGER AND THE UNIFORMITY FIREWALL.

The exact rational ε-arithmetic is the V4 ledger and is re-exported, not
re-proved.  What is new here is the distinction

    "an N₂ bound holds for each admissible ε"
                    ⇏
    "the N₂ constant is bounded uniformly in ε",

which is proved as a genuine separation (a family of constants that blows up as
ε ↓ 0 satisfies the first and fails the second).
-/
import Mathlib
import RequestProject.NANC.V5.N2Geometry

namespace NANC.V5

open NANC.V4

/-- The admissible ε-range of the bank: `0 < ε < 11/60000`, i.e. exactly the range
in which the shrunk exponent `1/6 - 2ε` still exceeds the published threshold. -/
def EpsAdmissible (eps : ℚ) : Prop := 0 < eps ∧ eps < 11 / 60000

/-- On the admissible range the shrunk exponent exceeds the published threshold
(re-export of the V4 arithmetic). -/
theorem epsAdmissible_shrunk_gt_threshold {eps : ℚ} (h : EpsAdmissible eps) :
    fmThreshold < (shrinkParams eps).2.2 :=
  shrunk_nu_gt_threshold_of_eps_small h.1 h.2

/-- Re-export: on the admissible range, `θ(ε) + ν(ε) = 1/6 - ε`. -/
theorem epsAdmissible_theta_add_nu (eps : ℚ) :
    (shrinkParams eps).2.1 + (shrinkParams eps).2.2 = 1 / 6 - eps :=
  shrunk_theta_add_nu eps

/-- A family of `N₂` constants indexed by the shrinking parameter. -/
abbrev N2ConstantFamily := ℚ → ℝ

/-- "For each admissible ε there is an `N₂` bound with constant `F ε`". -/
def N2UpperForEachEpsilon (F : N2ConstantFamily) (Q : ℚ → ℝ) : Prop :=
  ∀ eps : ℚ, EpsAdmissible eps → Q eps ≤ F eps

/-- **Uniformity in ε (UNINHABITED).**  The `N₂` constant stays bounded as ε
decreases through the admissible range.  This is what the endgame splice needs;
it is strictly stronger than a bound for each fixed ε. -/
def N2UniformInEpsilon (F : N2ConstantFamily) : Prop :=
  ∃ K : ℝ, ∀ eps : ℚ, EpsAdmissible eps → F eps ≤ K

/-- **Firewall (genuine separation).**  A bound for each admissible ε does *not*
imply ε-uniformity: the family `F ε = 1/ε` bounds the quantity `Q ≡ 0` for every
admissible ε, yet is unbounded on the admissible range. -/
theorem n2ForEachEpsilon_not_uniformInEpsilon :
    ∃ (F : N2ConstantFamily) (Q : ℚ → ℝ),
      N2UpperForEachEpsilon F Q ∧ ¬ N2UniformInEpsilon F := by
  refine ⟨fun eps => 1 / (eps : ℝ), fun _ => 0, ?_, ?_⟩
  · intro eps h
    have h0 : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast h.1
    positivity
  · rintro ⟨K, hK⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (max K 60000)
    have hn60000 : (60000 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hnK : K < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hnQ : (60000 : ℚ) < (n : ℚ) := by exact_mod_cast hn60000
    have hnpos : (0 : ℚ) < (n : ℚ) := by linarith
    have hadm : EpsAdmissible (1 / (n : ℚ)) := by
      constructor
      · positivity
      · have h1 : 1 / (n : ℚ) < 1 / 60000 :=
          one_div_lt_one_div_of_lt (by norm_num) hnQ
        linarith
    have hthis : 1 / ((1 / (n : ℚ) : ℚ) : ℝ) ≤ K := hK (1 / (n : ℚ)) hadm
    have hcast : ((1 / (n : ℚ) : ℚ) : ℝ) = 1 / (n : ℝ) := by push_cast; ring
    rw [hcast, one_div_one_div] at hthis
    linarith

/-- Provenance: ε-uniformity of the `N₂` constant is an open analytic requirement. -/
def epsUniformityProvenance : Provenance where
  status := AuditStatus.uninhabited
  sourceName := "ε-uniformity of the N₂ upper-sieve constant"
  sourceVersion := "NANC V5"
  scope := "the admissible range 0 < ε < 11/60000"
  notes := "Essential for the endgame splice; a bound for each fixed ε is not enough."

theorem epsUniformityProvenance_not_leanEvidence :
    Provenance.IsLeanEvidence epsUniformityProvenance = false := rfl

end NANC.V5
