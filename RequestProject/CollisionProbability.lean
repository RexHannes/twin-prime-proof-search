import Mathlib
import RequestProject.EnergySpectrumExact

/-!
# Normalized Collision Probability and Entropy Deficit

## Overview

We formalize the normalized collision probability identity:

  `CP(Q) = #Collisions / 2^(2k) = 2^(-k) * (1 + Σ_s E_s(Q) * 2^(-s))`

and equivalently in rational arithmetic (avoiding real logs):

  `#Collisions = 2^k * (1 + Σ_s E_s(Q) * 2^(-s))`
  `#Collisions * 1 = 2^k + Σ_s E_s(Q) * 2^(k-s)`

We also define the weighted energy sum and state the entropy-deficit
corollary as a theorem about rationals (avoiding logs).

## Definitions

- `totalWeightedEnergy k q` — `Σ_s E_s(Q) * 2^(-s)` as a rational number
- `collisionProbability k q` — `CP(Q) = #Collisions / 4^k` as a rational number
-/

open Finset BigOperators Fintype

noncomputable section

/-- The total weighted energy: `Σ_{s ∈ range(k+1)} E_s(Q) / 2^s`.
    This is the quantity `Z(Q) - 1` where `Z(Q) = Σ_s E_s * 2^{-s}`.
    We compute as a rational number. -/
def totalWeightedEnergy (k : ℕ) (q : Fin k → ℕ) : ℚ :=
  ∑ s ∈ Finset.range (k + 1), (energyAtSupport k q s : ℚ) / 2 ^ s

/-- The collision probability: `CP(Q) = #Collisions / 4^k`. -/
def collisionProbability (k : ℕ) (q : Fin k → ℕ) : ℚ :=
  (collisionPairs k q).card / (4 : ℚ) ^ k

/-- The deficit proxy: `Z(Q) = 1 + totalWeightedEnergy`.
    The entropy deficit is `D(Q) = log₂ Z(Q)` (not formalized as log here). -/
def deficitProxy (k : ℕ) (q : Fin k → ℕ) : ℚ :=
  1 + totalWeightedEnergy k q

/-! ## Key Identity: CP = 2^(-k) * Z(Q) -/

/-
The collision count equals `2^k * Z(Q)` where `Z(Q) = 1 + Σ E_s * 2^{-s}`.
    Equivalently: `#Collisions = 2^k + Σ_s E_s * 2^{k-s}`.

    This is the same as `collisionPairs_card_eq_diagonal_add_energy`, but we
    also prove the rational form `#Collisions / 4^k = Z(Q) / 2^k`.
-/
theorem collisionProbability_eq (k : ℕ) (q : Fin k → ℕ) (hq : ∀ i, q i ≠ 0) :
    collisionProbability k q = deficitProxy k q / 2 ^ k := by
  rw [ collisionProbability, deficitProxy, collisionPairs_card_eq_diagonal_add_energy ];
  · unfold totalWeightedEnergy;
    rw [ show ( 4 : ℚ ) ^ k = 2 ^ k * 2 ^ k by rw [ ← mul_pow ] ; norm_num ];
    field_simp;
    norm_num [ mul_add, Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun x hx => by rw [ mul_div, eq_div_iff ( by positivity ) ] ; rw [ mul_assoc, ← pow_add, Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hx ) ] ; ring;
  · assumption

/-! ## Properties of the Deficit Proxy -/

/-- If there are no nonzero kernel vectors (all subset sums distinct),
    then `Z(Q) = 1` and `CP(Q) = 2^(-k)`. -/
theorem deficitProxy_eq_one_of_no_collisions (k : ℕ) (q : Fin k → ℕ)
    (h : ∀ s, energyAtSupport k q s = 0) :
    deficitProxy k q = 1 := by
  simp [deficitProxy, totalWeightedEnergy, h]

/-
The deficit proxy is at least 1.
-/
theorem one_le_deficitProxy (k : ℕ) (q : Fin k → ℕ) :
    1 ≤ deficitProxy k q := by
  exact le_add_of_nonneg_right <| Finset.sum_nonneg fun _ _ => by positivity;

end