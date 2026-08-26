/-
# Gate 1B safe extension — the C₂ lower-floor RETRACTION GUARD

The retracted route used an unsupported *lower* floor

    C₂ ≫ Q log^{-O(1)}

for a quadratic coefficient energy `C₂` on a family of size `Q`.  This file
banks the permanent logical guard: a quadratic energy can vanish while the
ambient family size is positive, so **an upper bound `C₂ ≤ C·Q` never yields a
lower bound `C₂ ≥ c·Q`**, and `U/Q` must never be derived from `C₂` unless a
source-specific lower bound for `C₂` is proved separately.

This is a LOGICAL GUARD only: nothing here asserts that the actual Gate source
has `C₂ = 0`.
-/
import Universal.SafeAlgebra.Homogeneity

namespace Gate1B.SafeExtensions

open Universal.SafeAlgebra

/-- The zero coefficient family has zero quadratic energy. -/
theorem zeroCoefficient_energy_zero (Q : ℕ) :
    quadraticEnergy (Finset.univ : Finset (Fin Q)) (fun _ => (0 : ℂ)) = 0 :=
  zeroEnergy_counterexample _

/-- **No automatic `C₂` lower mass.**  For every positive family size `Q` and
every claimed floor constant `c > 0` there is a coefficient family of that size
whose energy is `0 < c · Q`. -/
theorem noAutomaticC2LowerMass (Q : ℕ) (hQ : 0 < Q) (c : ℝ) (hc : 0 < c) :
    ∃ a : Fin Q → ℂ, quadraticEnergy (Finset.univ : Finset (Fin Q)) a = 0 ∧
      ¬ (c * (Q : ℝ) ≤ quadraticEnergy (Finset.univ : Finset (Fin Q)) a) := by
  refine ⟨fun _ => 0, zeroCoefficient_energy_zero Q, ?_⟩
  rw [zeroCoefficient_energy_zero Q]
  have : 0 < c * (Q : ℝ) := by
    have : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    positivity
  exact not_le.mpr this

/-- **The retraction guard.**  An upper bound `C₂ ≤ C·Q` carries no lower-bound
information: the implication "`C₂ ≤ C·Q` ⟹ `C₂ ≥ c·Q`" fails for every pair of
positive constants. -/
theorem c2Floor_not_formal_from_upperBound (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ¬ ∀ (Q : ℕ) (a : Fin Q → ℂ), 0 < Q →
        quadraticEnergy (Finset.univ : Finset (Fin Q)) a ≤ C * (Q : ℝ) →
        c * (Q : ℝ) ≤ quadraticEnergy (Finset.univ : Finset (Fin Q)) a := by
  intro h
  have hQ : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
  have hupper : quadraticEnergy (Finset.univ : Finset (Fin 1)) (fun _ => (0 : ℂ))
      ≤ C * ((1 : ℕ) : ℝ) := by
    rw [zeroCoefficient_energy_zero 1]
    positivity
  have := h 1 (fun _ => 0) Nat.one_pos hupper
  rw [zeroCoefficient_energy_zero 1] at this
  nlinarith

end Gate1B.SafeExtensions
