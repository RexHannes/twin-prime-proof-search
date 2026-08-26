/-
# Gate-1A: the all-mode one-`q` centred dual-lift incidence identity (Section 5)

The one-`q` operator is

```
Y_q(b) = (H/q) ∑_{s ∈ (ZMod q)ˣ} A_q(s) · psi(b · w · s⁻¹)
```

(`w` plays the role of the fixed unit `2r`; `b = t·u` with `u = r^{-2}`).
This formula is used for **all** `b`, principal and nonprincipal alike; the
`b = 0` mode is not excluded, and is exactly the `t = 0` Fourier mode that the
centring removes.

The dual lift is

```
Z_q(k) = ∑_{t mod q} psi(-t·c) · Y_q(t·u),      c = m + r k.
```

The theorems below give:

* the exact **uncentred** all-mode reconstruction
  `Z_q(k) = H ∑_s A_q(s) · 1_{c s = u w}`;
* the exact **`t = 0` (Ramanujan / principal) mode** `= (H/q) ∑_s A_q(s)`;
* the exact **centred** identity
  `Z_q°(k) = H ∑_s A_q(s) (1_{c s = u w} − 1/q)`,

which is precisely `1_{q | (m + rk)s − 2} − 1/q` in the source normalization
(`u w = 2`).
-/
import Mathlib

namespace Gate1A

open Finset

namespace CenteredIncidence

variable {q : ℕ} [Fact (Nat.Prime q)]

theorem cast_q_ne_zero : ((q : ℂ)) ≠ 0 := by
  exact_mod_cast (Fact.out : Nat.Prime q).pos.ne'

/-- The one-`q` operator, defined for **all** modes `b` (including `b = 0`). -/
noncomputable def oneQOperator (psi : AddChar (ZMod q) ℂ) (A : (ZMod q)ˣ → ℂ)
    (Hc : ℂ) (w : (ZMod q)ˣ) (b : ZMod q) : ℂ :=
  (Hc / q) * ∑ s : (ZMod q)ˣ, A s *
    psi (b * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- The full (uncentred) dual lift. -/
noncomputable def dualLift (psi : AddChar (ZMod q) ℂ) (A : (ZMod q)ˣ → ℂ)
    (Hc : ℂ) (w u : (ZMod q)ˣ) (c : ZMod q) : ℂ :=
  ∑ t : ZMod q, psi (-(t * c)) * oneQOperator psi A Hc w (t * (u : ZMod q))

/-- The centred dual lift: the `t = 0` mode is removed. -/
noncomputable def centeredDualLift (psi : AddChar (ZMod q) ℂ) (A : (ZMod q)ˣ → ℂ)
    (Hc : ℂ) (w u : (ZMod q)ˣ) (c : ZMod q) : ℂ :=
  ∑ t ∈ (univ : Finset (ZMod q)).erase 0,
    psi (-(t * c)) * oneQOperator psi A Hc w (t * (u : ZMod q))

/-- Term-by-term rearrangement of the dual lift over the `t`-variable. -/
theorem dualLift_term (psi : AddChar (ZMod q) ℂ) (A : (ZMod q)ˣ → ℂ)
    (Hc : ℂ) (w u : (ZMod q)ˣ) (c : ZMod q) (t : ZMod q) :
    psi (-(t * c)) * oneQOperator psi A Hc w (t * (u : ZMod q))
      = (Hc / q) * ∑ s : (ZMod q)ˣ, A s *
          psi (t * ((u : ZMod q) * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q) - c)) := by
  rw [oneQOperator, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show psi (-(t * c)) * (A s * psi (t * (u : ZMod q) * (w : ZMod q) *
        ((s⁻¹ : (ZMod q)ˣ) : ZMod q)))
      = A s * (psi (-(t * c)) * psi (t * (u : ZMod q) * (w : ZMod q) *
        ((s⁻¹ : (ZMod q)ˣ) : ZMod q))) from by ring,
    ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- **The `t = 0` (Ramanujan / principal) mode.** -/
theorem dualLift_zero_mode (psi : AddChar (ZMod q) ℂ) (A : (ZMod q)ˣ → ℂ)
    (Hc : ℂ) (w u : (ZMod q)ˣ) (c : ZMod q) :
    psi (-((0 : ZMod q) * c)) * oneQOperator psi A Hc w ((0 : ZMod q) * (u : ZMod q))
      = (Hc / q) * ∑ s : (ZMod q)ˣ, A s := by
  rw [dualLift_term]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [zero_mul, AddChar.map_zero_eq_one, mul_one]

/-- **Uncentred all-mode reconstruction.**
`Z_q(k) = H ∑_s A_q(s) · 1_{c s = u w}`. -/
theorem dual_lift_incidence (psi : AddChar (ZMod q) ℂ) (hp : psi.IsPrimitive)
    (A : (ZMod q)ˣ → ℂ) (Hc : ℂ) (w u : (ZMod q)ˣ) (c : ZMod q) :
    dualLift psi A Hc w u c
      = Hc * ∑ s : (ZMod q)ˣ, A s *
          (if c * (s : ZMod q) = ((u * w : (ZMod q)ˣ) : ZMod q) then 1 else 0) := by
  classical
  have hq : ((q : ℂ)) ≠ 0 := cast_q_ne_zero
  rw [dualLift, Finset.sum_congr rfl (fun t _ => dualLift_term psi A Hc w u c t),
    ← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs : ((s⁻¹ : (ZMod q)ˣ) : ZMod q) * (s : ZMod q) = 1 := Units.inv_mul s
  have hinner : (∑ t : ZMod q, A s *
      psi (t * ((u : ZMod q) * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q) - c)))
      = A s * (if (u : ZMod q) * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q) - c = 0
          then (q : ℂ) else 0) := by
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ hp]
    by_cases h : (u : ZMod q) * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q) - c = 0
    · rw [if_pos h, if_pos h, ZMod.card q]
    · rw [if_neg h, if_neg h]; simp
  rw [hinner]
  have hcond : ((u : ZMod q) * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q) - c = 0)
      ↔ c * (s : ZMod q) = ((u * w : (ZMod q)ˣ) : ZMod q) := by
    rw [sub_eq_zero]
    constructor
    · intro h
      rw [← h, Units.val_mul]
      calc (u : ZMod q) * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q) * (s : ZMod q)
          = (u : ZMod q) * (w : ZMod q) *
              (((s⁻¹ : (ZMod q)ˣ) : ZMod q) * (s : ZMod q)) := by ring
        _ = (u : ZMod q) * (w : ZMod q) := by rw [hs, mul_one]
    · intro h
      have hmul : (u : ZMod q) * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q) * (s : ZMod q)
          = c * (s : ZMod q) := by
        calc (u : ZMod q) * (w : ZMod q) * ((s⁻¹ : (ZMod q)ˣ) : ZMod q) * (s : ZMod q)
            = (u : ZMod q) * (w : ZMod q) *
                (((s⁻¹ : (ZMod q)ˣ) : ZMod q) * (s : ZMod q)) := by ring
          _ = ((u * w : (ZMod q)ˣ) : ZMod q) := by rw [hs, mul_one, Units.val_mul]
          _ = c * (s : ZMod q) := h.symm
      exact mul_right_cancel₀ (IsUnit.ne_zero ⟨s, rfl⟩) hmul
  by_cases h : c * (s : ZMod q) = ((u * w : (ZMod q)ˣ) : ZMod q)
  · rw [if_pos (hcond.mpr h), if_pos h]
    field_simp
  · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
    ring

/-- **`centered_dual_lift_incidence`.**  The centred one-`q` dual lift is
exactly the centred incidence sum

`Z_q°(k) = H ∑_s A_q(s) · (1_{c s = u w} − 1/q)`.

In the source normalization `u w = 2` and `c = m + r k`, this is
`H ∑_s A_q(s) (1_{q | (m + rk)s − 2} − 1/q)`.  The common frequency `t` has
been eliminated, principal and nonprincipal modes are treated together, and
the `b = 0` mode enters only through the `−1/q` centring term. -/
theorem centered_dual_lift_incidence (psi : AddChar (ZMod q) ℂ) (hp : psi.IsPrimitive)
    (A : (ZMod q)ˣ → ℂ) (Hc : ℂ) (w u : (ZMod q)ˣ) (c : ZMod q) :
    centeredDualLift psi A Hc w u c
      = Hc * ∑ s : (ZMod q)ˣ, A s *
          ((if c * (s : ZMod q) = ((u * w : (ZMod q)ˣ) : ZMod q) then 1 else 0)
            - 1 / (q : ℂ)) := by
  classical
  have hsplit := Finset.add_sum_erase (univ : Finset (ZMod q))
    (fun t => psi (-(t * c)) * oneQOperator psi A Hc w (t * (u : ZMod q)))
    (Finset.mem_univ (0 : ZMod q))
  have hcent : centeredDualLift psi A Hc w u c
      = dualLift psi A Hc w u c - (Hc / q) * ∑ s : (ZMod q)ˣ, A s := by
    rw [centeredDualLift, dualLift, ← hsplit]
    dsimp only
    rw [dualLift_zero_mode]
    ring
  rw [hcent, dual_lift_incidence psi hp A Hc w u c, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

end CenteredIncidence

end Gate1A
