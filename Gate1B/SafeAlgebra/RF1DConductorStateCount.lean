/-
# Gate 1B v8.4 — RF1D conductor state-count repair

**Status: PROVED_ALGEBRAIC.**

Pure bookkeeping for the RF1D conductor decomposition `q = c * e`:

* `c` ranges over conductor moduli of size `C`;
* for each `c` there are (at most) `C` primitive characters;
* the inducing cofactor `e` ranges over `Q / C` values.

The repaired count is therefore

  `C * C * (Q / C) = Q * C`,

not `Q / C`.  This file proves that identity in ℕ (under `C ∣ Q`) and records
the exponent form in ℚ.  **No analytic statement is made here**: `C`, `Q` are
abstract cardinalities and the "state count" is a capacity bookkeeping figure.

FIREWALL.  `Q / C` is *not* the state count once the character family is also
summed: `conductorStateCount_ne_cofactorCount` exhibits `Q = C = 4`, where the
cofactor count is `1` but the state count is `16`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-! ## Natural-number state count -/

/-- **Repaired RF1D state count.**  With `C` conductor moduli, `C` primitive
characters per modulus and `Q / C` inducing cofactors, the total number of
`(c, χ, e)` states is `Q * C`. -/
theorem conductorStateCount_capacity {C Q : ℕ} (hdvd : C ∣ Q) :
    C * C * (Q / C) = Q * C := by
  have h : C * (Q / C) = Q := Nat.mul_div_cancel' hdvd
  calc C * C * (Q / C) = C * (C * (Q / C)) := by ring
    _ = C * Q := by rw [h]
    _ = Q * C := Nat.mul_comm _ _

/-- The same count with the three factors named. -/
theorem conductorStateCount_factors {C Q modCount charCount cofCount : ℕ}
    (hmod : modCount = C) (hchar : charCount = C) (hcof : cofCount = Q / C)
    (hdvd : C ∣ Q) :
    modCount * charCount * cofCount = Q * C := by
  subst hmod; subst hchar; subst hcof; exact conductorStateCount_capacity hdvd

/-! ## Exponent form

Writing `C = X ^ γ` and `Q = X ^ ω`, the state-count exponent is `ω + γ`, and
the (erroneous) cofactor-only exponent is `ω - γ`.  They differ by `2 γ`. -/

/-- Exponent bookkeeping for the state count: `γ + γ + (ω - γ) = ω + γ`. -/
theorem betaCharacterStateExponent (gamma omega : ℚ) :
    gamma + gamma + (omega - gamma) = omega + gamma := by ring

/-- The repaired exponent exceeds the cofactor-only exponent by exactly `2 γ`. -/
theorem betaCharacterStateExponent_gap (gamma omega : ℚ) :
    (omega + gamma) - (omega - gamma) = 2 * gamma := by ring

/-! ## Firewall countermodel -/

/-- **Firewall.**  The cofactor count `Q / C` is *not* the state count when the
character family is summed as well: at `Q = C = 4` the cofactor count is `1`
while the state count is `16`. -/
theorem conductorStateCount_ne_cofactorCount :
    (4 : ℕ) / 4 ≠ 4 * 4 := by decide

end Gate1B.SafeAlgebra
