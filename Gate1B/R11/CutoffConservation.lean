/-
# Gate1B / R11 : `KT = B` cutoff conservation and the hybrid `min` lemma

Two independent, purely elementary blocks.

**(a) Exponent conservation.**  With `A = X^a`, `B = X^{1-a}`, `d = X^u`, `k = X^{1-u}` and
the transfer scale `T = X^{u-a}`, the four conservation laws `AT = D`, `KT = B`, `DK = X`,
`AB = X` are exactly the four rational exponent identities

```
a + (u−a) = u,   (1−u) + (u−a) = 1−a,   u + (1−u) = 1,   a + (1−a) = 1.
```

Both the exponent-level identities and their real-power form (for `X > 0`, via `rpow`) are
kernel-proved.

**(b) The hybrid `min` lemma.**  For `α, β > 0` and positive `K, T, B` with `K·T = B`,

```
min (T^{-α}, K^{-β}) ≤ B^{-αβ/(α+β)}.
```

No analytic number theory is involved anywhere in this file.
-/
import Mathlib

namespace Gate1B.R11

open Real

/-! ## 1. Rational exponent conservation -/

/-- `a + (u − a) = u`: the `AT = D` law at the exponent level. -/
theorem exponent_AT_eq_D (a u : ℚ) : a + (u - a) = u := by ring

/-- `(1 − u) + (u − a) = 1 − a`: the `KT = B` law at the exponent level. -/
theorem exponent_KT_eq_B (a u : ℚ) : (1 - u) + (u - a) = 1 - a := by ring

/-- `u + (1 − u) = 1`: the `DK = X` law at the exponent level. -/
theorem exponent_DK_eq_X (u : ℚ) : u + (1 - u) = 1 := by ring

/-- `a + (1 − a) = 1`: the `AB = X` law at the exponent level. -/
theorem exponent_AB_eq_X (a : ℚ) : a + (1 - a) = 1 := by ring

/-- All four conservation laws at once. -/
theorem exponent_conservation (a u : ℚ) :
    a + (u - a) = u ∧ (1 - u) + (u - a) = 1 - a ∧ u + (1 - u) = 1 ∧ a + (1 - a) = 1 :=
  ⟨exponent_AT_eq_D a u, exponent_KT_eq_B a u, exponent_DK_eq_X u, exponent_AB_eq_X a⟩

/-! ## 2. The same conservation laws as exact real-power identities -/

variable {X : ℝ}

/-- `A · T = D` for real powers of a positive base. -/
theorem rpow_AT_eq_D (hX : 0 < X) (a u : ℝ) : X ^ a * X ^ (u - a) = X ^ u := by
  rw [← Real.rpow_add hX]
  ring_nf

/-- `K · T = B` for real powers of a positive base. -/
theorem rpow_KT_eq_B (hX : 0 < X) (a u : ℝ) : X ^ (1 - u) * X ^ (u - a) = X ^ (1 - a) := by
  rw [← Real.rpow_add hX]
  ring_nf

/-- `D · K = X` for real powers of a positive base. -/
theorem rpow_DK_eq_X (hX : 0 < X) (u : ℝ) : X ^ u * X ^ (1 - u) = X := by
  rw [← Real.rpow_add hX]
  simp

/-- `A · B = X` for real powers of a positive base. -/
theorem rpow_AB_eq_X (hX : 0 < X) (a : ℝ) : X ^ a * X ^ (1 - a) = X := by
  rw [← Real.rpow_add hX]
  simp

/-- **Cutoff conservation ledger.**  All four real-power laws simultaneously, for the
matched data `A = X^a`, `B = X^{1-a}`, `D = X^u`, `K = X^{1-u}`, `T = X^{u-a}`. -/
theorem rpow_conservation (hX : 0 < X) (a u : ℝ) :
    X ^ a * X ^ (u - a) = X ^ u ∧ X ^ (1 - u) * X ^ (u - a) = X ^ (1 - a) ∧
      X ^ u * X ^ (1 - u) = X ∧ X ^ a * X ^ (1 - a) = X :=
  ⟨rpow_AT_eq_D hX a u, rpow_KT_eq_B hX a u, rpow_DK_eq_X hX u, rpow_AB_eq_X hX a⟩

/-! ## 3. The hybrid `min` lemma -/

/-- **Hybrid `min` lemma.**  If `K · T = B` with `K, T, B > 0` and `α, β > 0`, then

```
min (T^{-α}, K^{-β}) ≤ B^{-αβ/(α+β)}.
```

Elementary: raise the two branches to the powers `β` and `α` and multiply. -/
theorem hybrid_min_le {a b K T B : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 < K) (hT : 0 < T)
    (hB : 0 < B) (hKT : K * T = B) :
    min (T ^ (-a)) (K ^ (-b)) ≤ B ^ (-(a * b) / (a + b)) := by
  set m := min (T ^ (-a)) (K ^ (-b)) with hm
  have hab : 0 < a + b := by linarith
  have hmpos : 0 < m := lt_min (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hK _)
  have h1 : m ≤ T ^ (-a) := min_le_left _ _
  have h2 : m ≤ K ^ (-b) := min_le_right _ _
  -- raise the two branches
  have e1 : m ^ b ≤ T ^ (-(a * b)) := by
    calc m ^ b ≤ (T ^ (-a)) ^ b := Real.rpow_le_rpow hmpos.le h1 hb.le
      _ = T ^ (-(a * b)) := by rw [← Real.rpow_mul hT.le]; ring_nf
  have e2 : m ^ a ≤ K ^ (-(a * b)) := by
    calc m ^ a ≤ (K ^ (-b)) ^ a := Real.rpow_le_rpow hmpos.le h2 ha.le
      _ = K ^ (-(a * b)) := by rw [← Real.rpow_mul hK.le]; ring_nf
  have key : m ^ (a + b) ≤ B ^ (-(a * b)) := by
    have hprod : m ^ (a + b) = m ^ a * m ^ b := by rw [Real.rpow_add hmpos]
    have hBsplit : B ^ (-(a * b)) = K ^ (-(a * b)) * T ^ (-(a * b)) := by
      rw [← hKT, Real.mul_rpow hK.le hT.le]
    rw [hprod, hBsplit]
    exact mul_le_mul e2 e1 (Real.rpow_nonneg hmpos.le _)
      (Real.rpow_nonneg hK.le _)
  -- take the `(a+b)`-th root
  have hpow : (m ^ (a + b)) ^ (1 / (a + b)) ≤ (B ^ (-(a * b))) ^ (1 / (a + b)) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hmpos.le _) key (by positivity)
  rwa [← Real.rpow_mul hmpos.le, ← Real.rpow_mul hB.le,
    mul_one_div_cancel (ne_of_gt hab), Real.rpow_one,
    show -(a * b) * (1 / (a + b)) = -(a * b) / (a + b) by ring] at hpow

end Gate1B.R11
