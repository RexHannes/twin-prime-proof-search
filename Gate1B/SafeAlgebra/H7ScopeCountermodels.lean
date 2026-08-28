/-
# Gate 1B v8.5 — countermodels: do not promote the complement

**Status: PROVED_FINITE (four explicit finite/logical countermodels).**

A. A statement proved under `beta < 4/9` cannot be applied at `beta = 1/2`.
B. A packet bound on `H7ShortShort` does not imply a bound on
   `HighPrimeComplement`.
C. Common-sequence decomposition is load-bearing: an arbitrary `p`-dependent
   coefficient family need not admit a bounded-rank commonisation.
D. A CAPACITY margin is not by itself an analytic theorem: an unspecified
   constant destroys a fixed negative exponent at any fixed scale.
-/
import Mathlib
import Gate1B.SafeAlgebra.H7ScopeFirewall

namespace Gate1B.SafeAlgebra

/-! ## A. `beta = 1/2` is not in the short-short scope -/

/-- The hypothesis `beta < 4/9` simply fails at `beta = 1/2`: any theorem whose
statement carries that hypothesis is vacuous there. -/
theorem countermodelA_half_not_shortShort : ¬ ((1 : ℚ) / 2 < 4 / 9) := by norm_num

/-- Consequently a conditional statement `beta < 4/9 → Claim beta` gives no
information at `beta = 1/2`: the antecedent is false, so both `Claim (1/2)` and
its negation remain compatible with the implication. -/
theorem countermodelA_no_transport (Claim : ℚ → Prop) :
    ((∀ beta : ℚ, beta < 4 / 9 → Claim beta) →
      (Claim (1 / 2) ∨ ¬ Claim (1 / 2))) := by
  intro _; exact em _

/-- Concretely: a predicate that holds exactly on the short-short range
satisfies the short-short conditional but fails at `1/2`. -/
theorem countermodelA_witness :
    ∃ Claim : ℚ → Prop, (∀ beta : ℚ, beta < 4 / 9 → Claim beta) ∧ ¬ Claim (1 / 2) := by
  refine ⟨fun beta => beta < 4 / 9, fun _ h => h, by norm_num⟩

/-! ## B. A bound on one node is not a bound on the other -/

/-- A "packet size" function may be bounded on the short-short node and large on
the high-prime complement: the two nodes carry independent information. -/
theorem countermodelB_no_node_transport :
    ∃ f : H7Region → ℝ, f H7Region.H7ShortShort ≤ 1 ∧ ¬ (f H7Region.HighPrimeComplement ≤ 1) := by
  refine ⟨fun r => match r with
    | H7Region.H7ShortShort => 0
    | H7Region.HighPrimeComplement => 2, by norm_num, by norm_num⟩

/-! ## C. Commonisation is load-bearing -/

/-- The `2 × 2` identity family admits no rank-one common-sequence
decomposition, so "there is a bounded-rank common sequence" is a genuine extra
source hypothesis. -/
theorem countermodelC_commonSequence_load_bearing :
    ¬ ∃ (l : Fin 2 → ℂ) (t : Fin 2 → ℂ),
        ∀ p c : Fin 2, (if p = c then (1 : ℂ) else 0) = l p * t c := by
  rintro ⟨l, t, h⟩
  have h00 : l 0 * t 0 = 1 := by simpa using (h 0 0).symm
  have h01 : l 0 * t 1 = 0 := by simpa using (h 0 1).symm
  have h11 : l 1 * t 1 = 1 := by simpa using (h 1 1).symm
  have hl0 : l 0 ≠ 0 := by intro h0; rw [h0, zero_mul] at h00; exact zero_ne_one h00
  have ht1 : t 1 = 0 := by
    rcases mul_eq_zero.mp h01 with h | h
    · exact absurd h hl0
    · exact h
  rw [ht1, mul_zero] at h11
  exact zero_ne_one h11

/-! ## D. A capacity margin is not an analytic theorem -/

/-- A negative *exponent* margin does not produce a numerical bound: with an
unspecified constant `C` the quantity `C · Y^(-1/2)` can exceed the target at any
fixed scale. -/
theorem countermodelD_capacity_is_not_analytic :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧ ¬ (C * (1 / Real.sqrt Y) ≤ 1) := by
  refine ⟨2, 1, by norm_num, le_refl 1, ?_⟩
  rw [Real.sqrt_one]
  norm_num

/-- Nor does an exponent inequality by itself say anything at a *fixed* scale:
`17/2 < 9` in ℚ, yet `2 · Y^(17/2) ≤ Y⁹` fails at `Y = 1`. -/
theorem countermodelD_exponent_not_scale : (17 : ℚ) / 2 < 9 ∧ ¬ ((2:ℝ) * 1 ≤ 1) := by
  constructor
  · norm_num
  · norm_num

end Gate1B.SafeAlgebra
