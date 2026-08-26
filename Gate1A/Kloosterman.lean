/-
# Gate-1A: the finite additive-character / Kloosterman layer (Section 3)

Everything is exact and finite: `q` is a prime, `psi` is an additive character
of `ZMod q` valued in `ℂ`, and

```
S_q(U,V) = ∑_{x ∈ (ZMod q)ˣ} psi (U x + V x⁻¹).
```

Normalization dictionary: `psi` is an arbitrary `AddChar (ZMod q) ℂ`; the
theorems that need nondegeneracy carry the explicit hypothesis
`psi.IsPrimitive` (equivalently, `psi.mulShift a ≠ 1` for all `a ≠ 0`).
No `2π i / q` convention is baked in: all statements are convention-free in
terms of `psi`.
-/
import Mathlib

namespace Gate1A

open Finset

namespace Kloosterman

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- Sums over the units of `ZMod q` (`q` prime) versus sums over all residues. -/
theorem sum_units_eq (F : ZMod q → ℂ) :
    ∑ x : (ZMod q)ˣ, F (x : ZMod q) = (∑ x : ZMod q, F x) - F 0 := by
  classical
  have himg : (univ : Finset (ZMod q)).erase 0
      = Finset.image (fun u : (ZMod q)ˣ => (u : ZMod q)) univ := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_univ, true_and, Finset.mem_image, and_true]
    exact ⟨fun hy => ⟨Units.mk0 y hy, rfl⟩, by rintro ⟨u, rfl⟩; exact u.ne_zero⟩
  have hinj : Set.InjOn (fun u : (ZMod q)ˣ => (u : ZMod q)) ↑(univ : Finset (ZMod q)ˣ) :=
    fun x _ y _ h => Units.ext h
  have h2 := Finset.sum_image (f := F) hinj
  rw [← himg] at h2
  rw [← h2, Finset.sum_erase_eq_sub (Finset.mem_univ (0 : ZMod q))]

/-- The exact finite Kloosterman-type sum
`S_q(U,V) = ∑_{x ∈ (ZMod q)ˣ} psi (U x + V x⁻¹)`. -/
noncomputable def kloosterman (psi : AddChar (ZMod q) ℂ) (U V : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ, psi (U * (x : ZMod q) + V * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

variable (psi : AddChar (ZMod q) ℂ)

/-! ### K1. Sign involution -/

/-- **K1 (sign involution).** `S_q(U,V) = S_q(-U,-V)`, via the unit bijection
`x ↦ -x`. -/
theorem kloosterman_neg_neg (U V : ZMod q) :
    kloosterman psi U V = kloosterman psi (-U) (-V) := by
  simp only [kloosterman]
  refine (Fintype.sum_equiv (Equiv.neg ((ZMod q)ˣ)) _ _ ?_).symm
  intro x
  congr 1
  have h1 : ((-x : (ZMod q)ˣ) : ZMod q) = -((x : (ZMod q)ˣ) : ZMod q) := Units.val_neg x
  have h2 : (((-x : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q)
      = -(((x⁻¹ : (ZMod q)ˣ)) : ZMod q) := by
    rw [inv_neg, Units.val_neg]
  simp only [Equiv.neg_apply, h1, h2]
  ring

/-! ### K2. Axis identities -/

/-- **K2 (origin).** `S_q(0,0) = q - 1`. -/
theorem kloosterman_zero_zero : kloosterman psi 0 0 = (q : ℂ) - 1 := by
  simp only [kloosterman, zero_mul, add_zero, AddChar.map_zero_eq_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [ZMod.card_units q]
  have hq : 1 ≤ q := (Fact.out : Nat.Prime q).one_lt.le
  push_cast [Nat.cast_sub hq]
  ring

/-- **K2 (horizontal axis).** For `U ≠ 0`, `S_q(U,0) = -1`. -/
theorem kloosterman_axis_left (hp : psi.IsPrimitive) {U : ZMod q} (hU : U ≠ 0) :
    kloosterman psi U 0 = -1 := by
  classical
  have hstep : kloosterman psi U 0 = ∑ x : (ZMod q)ˣ, psi ((x : ZMod q) * U) := by
    simp only [kloosterman, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  rw [hstep, sum_units_eq (fun x => psi (x * U)), AddChar.sum_mulShift U hp]
  simp [hU]

/-- **K2 (vertical axis).** For `V ≠ 0`, `S_q(0,V) = -1`. -/
theorem kloosterman_axis_right (hp : psi.IsPrimitive) {V : ZMod q} (hV : V ≠ 0) :
    kloosterman psi 0 V = -1 := by
  classical
  have hstep : kloosterman psi 0 V = ∑ x : (ZMod q)ˣ, psi ((x : ZMod q) * V) := by
    simp only [kloosterman, zero_mul, zero_add]
    refine (Fintype.sum_equiv (Equiv.inv ((ZMod q)ˣ)) _ _ ?_).symm
    intro x
    congr 1
    simp [mul_comm]
  rw [hstep, sum_units_eq (fun x => psi (x * V)), AddChar.sum_mulShift V hp]
  simp [hV]

/-! ### K3. Complete local correlation -/

/-- **K3 (complete local correlation).**
`∑_{V mod q} S_q(U,V) · conj S_q(U',V) = q² · 1_{U = U'} - q`.

Derived from scratch by opening the two unit sums and using additive-character
orthogonality; no external Kloosterman input is assumed. -/
theorem kloosterman_local_correlation (hp : psi.IsPrimitive) (U U' : ZMod q) :
    (∑ V : ZMod q, kloosterman psi U V * (starRingEnd ℂ) (kloosterman psi U' V))
      = (if U = U' then (q : ℂ) ^ 2 else 0) - (q : ℂ) := by
  classical
  -- Step 1: open the two unit sums.
  have hexp : ∀ V : ZMod q,
      kloosterman psi U V * (starRingEnd ℂ) (kloosterman psi U' V)
        = ∑ x : (ZMod q)ˣ, ∑ y : (ZMod q)ˣ,
            psi (U * (x : ZMod q) - U' * (y : ZMod q)) *
              psi (V * (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - ((y⁻¹ : (ZMod q)ˣ) : ZMod q))) := by
    intro V
    rw [kloosterman, kloosterman, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun V _ => hexp V), Finset.sum_comm]
  -- Step 2: perform the `V` sum (additive-character orthogonality).
  have horth : ∀ x y : (ZMod q)ˣ,
      (∑ V : ZMod q, psi (U * (x : ZMod q) - U' * (y : ZMod q)) *
          psi (V * (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - ((y⁻¹ : (ZMod q)ˣ) : ZMod q))))
        = psi (U * (x : ZMod q) - U' * (y : ZMod q)) *
            (if x = y then (q : ℂ) else 0) := by
    intro x y
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ hp]
    congr 1
    have hiff : (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - ((y⁻¹ : (ZMod q)ˣ) : ZMod q) = 0)
        ↔ x = y := by
      rw [sub_eq_zero]
      constructor
      · intro h
        have : x⁻¹ = y⁻¹ := Units.ext h
        simpa using congrArg (fun u : (ZMod q)ˣ => u⁻¹) this
      · rintro rfl; rfl
    by_cases h : x = y
    · rw [if_pos (hiff.mpr h), if_pos h, ZMod.card q]
    · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
      simp
  have hswap : ∀ x : (ZMod q)ˣ,
      (∑ V : ZMod q, ∑ y : (ZMod q)ˣ,
        psi (U * (x : ZMod q) - U' * (y : ZMod q)) *
          psi (V * (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - ((y⁻¹ : (ZMod q)ˣ) : ZMod q))))
        = psi ((U - U') * (x : ZMod q)) * (q : ℂ) := by
    intro x
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun y _ => horth x y)]
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl]
      congr 2
      ring
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun x _ => hswap x)]
  -- Step 3: the remaining `x` sum.
  rw [← Finset.sum_mul]
  have hUU : (∑ x : (ZMod q)ˣ, psi ((U - U') * (x : ZMod q)))
      = (if U = U' then (q : ℂ) else 0) - 1 := by
    have hc : (∑ x : (ZMod q)ˣ, psi ((U - U') * (x : ZMod q)))
        = ∑ x : (ZMod q)ˣ, psi ((x : ZMod q) * (U - U')) :=
      Finset.sum_congr rfl fun x _ => by rw [mul_comm]
    rw [hc, sum_units_eq (fun x => psi (x * (U - U'))), AddChar.sum_mulShift _ hp]
    by_cases h : U = U'
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h, ZMod.card q]
      simp
    · rw [if_neg (fun hc0 => h (sub_eq_zero.mp hc0)), if_neg h]
      simp
  rw [hUU]
  by_cases h : U = U'
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

end Kloosterman

end Gate1A
