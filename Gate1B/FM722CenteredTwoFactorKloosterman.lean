import Gate1B.FM722CenteredOneFactorCompletion

/-!
# Gate 1B · FM722 · the centred **two-factor completion** and the complete
Kloosterman sum

**Exact finite algebra over `ZMod q`.  No analytic bound is proved, assumed or
attached anywhere in this module.**  In particular *no* Weil bound and *no*
square-root cancellation is claimed for `kloostermanSum`.

## Contents

* §1 sums over the unit sector (`sum_ite_isUnit`), the pointwise form of the
  unit-sector principal model, and the unit-sector character sum in Ramanujan
  form;
* §2 the **complete Kloosterman sum**
  `S(a,b;q) = ∑_{z mod q} [z unit] e_q(az + b z⁻¹)`;
* §3 the exact indicator evaluation producing the Kloosterman sum;
* §4 the **centred Kloosterman kernel**
  `K_q(k,j;π) = S(k, −2 j π⁻¹; q) − c_q(k) c_q(j)/φ(q)`
  and the two-factor centred completion identity
  (**FM722-TWOFACTOR-CENTERED-KLOOSTERMAN45**, kernel form).

The `2`-adic hypothesis `IsUnit (2 : ZMod q)` is stated explicitly wherever it
is used; the shift is the fixed shift `2`, never averaged.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier
open TwinPrimeProject.CurrentProgramme.HStarCentered

variable {q : ℕ} [NeZero q]

/-! ## 1. The unit sector -/

/-- The unit group of `ZMod q` as the subtype of unit elements. -/
noncomputable def unitsEquivIsUnitSub (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ {x : ZMod q // IsUnit x} where
  toFun u := ⟨(u : ZMod q), u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := by simp
  right_inv x := by apply Subtype.ext; simp [IsUnit.unit_spec]

/-- A sum over `ZMod q` cut down to the unit sector is a sum over `(ZMod q)ˣ`. -/
theorem sum_ite_isUnit (f : ZMod q → ℂ) :
    (∑ z : ZMod q, if IsUnit z then f z else 0) = ∑ u : (ZMod q)ˣ, f (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter,
    Finset.sum_subtype (p := fun x : ZMod q => IsUnit x) _ (fun x => by simp) f]
  exact (Equiv.sum_comp (unitsEquivIsUnitSub q)
    (fun x : {x : ZMod q // IsUnit x} => f (x : ZMod q))).symm

/-- Pointwise form of the unit-sector principal model. -/
theorem unitPrincipal_eq_ite (n : ZMod q) :
    unitPrincipal q n = if IsUnit n then (1 / (q.totient : ℂ)) else 0 := by
  classical
  unfold unitPrincipal
  by_cases h : IsUnit n
  · rw [if_pos h, Finset.sum_eq_single h.unit]
    · simp [IsUnit.unit_spec]
    · intro b _ hb
      have : (b : ZMod q) ≠ n := by
        intro hbn
        exact hb (Units.ext (by simpa [IsUnit.unit_spec] using hbn))
      simp [this]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun a _ => ?_
    have : (a : ZMod q) ≠ n := fun hh => h (hh ▸ a.isUnit)
    simp [this]

/-- The unit-sector character sum is the Ramanujan sum. -/
theorem sum_unitSector_eM (k : ZMod q) :
    (∑ A : ZMod q, if IsUnit A then eM q (k * A) else 0) = ramanujanSum q k := by
  classical
  rw [sum_ite_isUnit]
  have h : ∀ u : (ZMod q)ˣ, eM q (k * (u : ZMod q)) = eM q (-((-k) * (u : ZMod q))) := by
    intro u; congr 1; ring
  rw [Finset.sum_congr rfl fun u _ => h u]
  rw [show (∑ u : (ZMod q)ˣ, eM q (-((-k) * (u : ZMod q)))) = ramanujanSum q (-k) from rfl,
    ramanujanSum_neg]

/-! ## 2. The complete Kloosterman sum -/

/-- **The complete Kloosterman sum**
`S(a,b;q) = ∑_{z mod q, z unit} e_q(a z + b z⁻¹)`.  No analytic bound is
attached to this definition anywhere in the bank. -/
noncomputable def kloostermanSum (q : ℕ) [NeZero q] (a b : ZMod q) : ℂ :=
  ∑ z : ZMod q, if IsUnit z then eM q (a * z + b * z⁻¹) else 0

/-- The Kloosterman sum as a sum over the unit group. -/
theorem kloostermanSum_eq_units (a b : ZMod q) :
    kloostermanSum q a b
      = ∑ u : (ZMod q)ˣ, eM q (a * (u : ZMod q) + b * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  classical
  rw [kloostermanSum, sum_ite_isUnit]
  exact Finset.sum_congr rfl fun u _ => by rw [ZMod.inv_coe_unit]

/-- `S(a,0;q) = c_q(−a) = c_q(a)`. -/
theorem kloostermanSum_zero_right (a : ZMod q) :
    kloostermanSum q a 0 = ramanujanSum q a := by
  classical
  rw [kloostermanSum]
  rw [show (∑ z : ZMod q, if IsUnit z then eM q (a * z + 0 * z⁻¹) else 0)
      = ∑ z : ZMod q, if IsUnit z then eM q (a * z) else 0 from
    Finset.sum_congr rfl fun z _ => by simp]
  exact sum_unitSector_eM a

/-- `S(0,b;q) = c_q(−b) = c_q(b)`: inversion is a bijection of the unit
sector. -/
theorem kloostermanSum_zero_left (b : ZMod q) :
    kloostermanSum q 0 b = ramanujanSum q b := by
  classical
  rw [kloostermanSum_eq_units]
  have h : ∀ u : (ZMod q)ˣ,
      eM q (0 * (u : ZMod q) + b * ((u⁻¹ : (ZMod q)ˣ) : ZMod q))
        = eM q (b * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
    intro u; simp
  rw [Finset.sum_congr rfl fun u _ => h u]
  rw [← Equiv.sum_comp (Equiv.inv (ZMod q)ˣ)
    (fun u : (ZMod q)ˣ => eM q (b * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)))]
  have h2 : ∀ u : (ZMod q)ˣ,
      eM q (b * (((Equiv.inv (ZMod q)ˣ u)⁻¹ : (ZMod q)ˣ) : ZMod q))
        = eM q (-((-b) * (u : ZMod q))) := by
    intro u
    simp only [Equiv.inv_apply, inv_inv]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun u _ => h2 u]
  rw [show (∑ u : (ZMod q)ˣ, eM q (-((-b) * (u : ZMod q)))) = ramanujanSum q (-b) from rfl,
    ramanujanSum_neg]

/-! ## 3. The exact indicator evaluation -/

/-- **The determinant indicator produces the complete Kloosterman sum.**
For `2` a unit mod `q` and `π` a unit,

```
  ∑_{A,C} [A C π = −2] e_q(kA) e_q(jC) = S(k, −2 j π⁻¹; q).
```
-/
theorem indicator_double_sum (h2 : IsUnit (2 : ZMod q)) (k j : ZMod q) (pi : (ZMod q)ˣ) :
    (∑ A : ZMod q, ∑ C : ZMod q,
        (if A * C * (pi : ZMod q) = -2 then eM q (k * A) * eM q (j * C) else 0))
      = kloostermanSum q k (-2 * j * ((pi⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  classical
  set pinv : ZMod q := ((pi⁻¹ : (ZMod q)ˣ) : ZMod q) with hpinv
  have hpp : pinv * (pi : ZMod q) = 1 := by
    rw [hpinv, ← Units.val_mul]; simp
  rw [kloostermanSum]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases hA : IsUnit A
  · rw [if_pos hA]
    have hAA : A * A⁻¹ = 1 := ZMod.mul_inv_of_unit A hA
    set C0 : ZMod q := -2 * A⁻¹ * pinv with hC0
    rw [Finset.sum_eq_single C0]
    · have hval : A * C0 * (pi : ZMod q) = -2 := by
        have h1 : A * C0 * (pi : ZMod q) = (A * A⁻¹) * (pinv * (pi : ZMod q)) * (-2) := by
          rw [hC0]; ring
        rw [h1, hAA, hpp]; ring
      rw [if_pos hval, ← eM_add]
      congr 1
      rw [hC0]; ring
    · intro C _ hC
      have hne : A * C * (pi : ZMod q) ≠ -2 := by
        intro h
        apply hC
        have hcalc : (A⁻¹ * pinv) * (A * C * (pi : ZMod q)) = C := by
          have h1 : (A⁻¹ * pinv) * (A * C * (pi : ZMod q))
              = (A * A⁻¹) * (pinv * (pi : ZMod q)) * C := by ring
          rw [h1, hAA, hpp]; ring
        rw [h] at hcalc
        rw [← hcalc, hC0]; ring
      simp [hne]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  · rw [if_neg hA]
    refine Finset.sum_eq_zero fun C _ => ?_
    have hne : A * C * (pi : ZMod q) ≠ -2 := by
      intro h
      apply hA
      have h2' : IsUnit ((-2 : ZMod q)) := h2.neg
      rw [← h] at h2'
      exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h2')
    simp [hne]

/-- The principal (main-term) part of the two-factor sum factorises into two
Ramanujan sums. -/
theorem principal_double_sum (k j : ZMod q) (pi : (ZMod q)ˣ) :
    (∑ A : ZMod q, ∑ C : ZMod q,
        eM q (k * A) * eM q (j * C) * unitPrincipal q (A * C * (pi : ZMod q)))
      = ramanujanSum q k * ramanujanSum q j / (q.totient : ℂ) := by
  classical
  have hunit : ∀ A C : ZMod q,
      IsUnit (A * C * (pi : ZMod q)) ↔ (IsUnit A ∧ IsUnit C) := by
    intro A C
    constructor
    · intro h
      have h' : IsUnit (A * C) := isUnit_of_mul_isUnit_left h
      exact ⟨isUnit_of_mul_isUnit_left h', isUnit_of_mul_isUnit_right h'⟩
    · rintro ⟨hA, hC⟩
      exact (hA.mul hC).mul pi.isUnit
  have step : ∀ A : ZMod q,
      (∑ C : ZMod q, eM q (k * A) * eM q (j * C) * unitPrincipal q (A * C * (pi : ZMod q)))
        = (if IsUnit A then eM q (k * A) else 0) *
            ((∑ C : ZMod q, if IsUnit C then eM q (j * C) else 0) * (1 / (q.totient : ℂ))) := by
    intro A
    by_cases hA : IsUnit A
    · rw [if_pos hA]
      have hterm : ∀ C : ZMod q,
          eM q (k * A) * eM q (j * C) * unitPrincipal q (A * C * (pi : ZMod q))
            = eM q (k * A) *
                ((if IsUnit C then eM q (j * C) else 0) * (1 / (q.totient : ℂ))) := by
        intro C
        rw [unitPrincipal_eq_ite]
        by_cases hC : IsUnit C
        · rw [if_pos ((hunit A C).2 ⟨hA, hC⟩), if_pos hC]; ring
        · rw [if_neg (fun h => hC ((hunit A C).1 h).2), if_neg hC]; ring
      rw [Finset.sum_congr rfl fun C _ => hterm C, ← Finset.mul_sum, ← Finset.sum_mul]
    · rw [if_neg hA, zero_mul]
      refine Finset.sum_eq_zero fun C _ => ?_
      rw [unitPrincipal_eq_ite, if_neg (fun h => hA ((hunit A C).1 h).1)]
      ring
  rw [Finset.sum_congr rfl fun A _ => step A, ← Finset.sum_mul,
    sum_unitSector_eM, sum_unitSector_eM]
  field_simp

/-! ## 4. The centred Kloosterman kernel and the two-factor completion -/

/-- **The centred Kloosterman kernel**

```
  K_q(k,j;π) = S(k, −2 j π⁻¹; q) − c_q(k) c_q(j)/φ(q).
```
-/
noncomputable def centeredKloostermanKernel (q : ℕ) [NeZero q] (k j : ZMod q)
    (pi : (ZMod q)ˣ) : ℂ :=
  kloostermanSum q k (-2 * j * ((pi⁻¹ : (ZMod q)ˣ) : ZMod q))
    - ramanujanSum q k * ramanujanSum q j / (q.totient : ℂ)

/-- The exact two-frequency centred transform:
`∑_{A,C} e_q(kA) e_q(jC) Δ_q(ACπ) = K_q(k,j;π)`. -/
theorem centered_twoFrequency_transform (h2 : IsUnit (2 : ZMod q)) (k j : ZMod q)
    (pi : (ZMod q)ˣ) :
    (∑ A : ZMod q, ∑ C : ZMod q,
        eM q (k * A) * eM q (j * C) * centeredProjector q (A * C * (pi : ZMod q)))
      = centeredKloostermanKernel q k j pi := by
  classical
  have hsplit : ∀ A C : ZMod q,
      eM q (k * A) * eM q (j * C) * centeredProjector q (A * C * (pi : ZMod q))
        = (if A * C * (pi : ZMod q) = -2 then eM q (k * A) * eM q (j * C) else 0)
          - eM q (k * A) * eM q (j * C) * unitPrincipal q (A * C * (pi : ZMod q)) := by
    intro A C
    rw [centeredProjector, mul_sub]
    congr 1
    by_cases h : A * C * (pi : ZMod q) = -2 <;> simp [h]
  rw [Finset.sum_congr rfl fun A _ =>
    Finset.sum_congr rfl fun C _ => hsplit A C]
  simp only [Finset.sum_sub_distrib]
  rw [indicator_double_sum h2 k j pi, principal_double_sum k j pi,
    centeredKloostermanKernel]

/-- Reordering of the four finite sums. -/
theorem sum_comm4 (F : ZMod q → ZMod q → ZMod q → ZMod q → ℂ) :
    (∑ A, ∑ C, ∑ k, ∑ j, F A C k j) = ∑ k, ∑ j, ∑ A, ∑ C, F A C k j := by
  have h1 : (∑ A, ∑ C, ∑ k, ∑ j, F A C k j)
      = ∑ x : ZMod q × ZMod q, ∑ y : ZMod q × ZMod q, F x.1 x.2 y.1 y.2 := by
    simp [Fintype.sum_prod_type]
  have h2 : (∑ k, ∑ j, ∑ A, ∑ C, F A C k j)
      = ∑ y : ZMod q × ZMod q, ∑ x : ZMod q × ZMod q, F x.1 x.2 y.1 y.2 := by
    simp [Fintype.sum_prod_type]
  rw [h1, h2, Finset.sum_comm]

/-- **FM722-TWOFACTOR-CENTERED-KLOOSTERMAN45 (kernel form).**

For finite `alpha, gamma` mod `q`, a unit `π` and `2` invertible mod `q`,

```
  ∑_{A,C} alpha(A) gamma(C) Δ_q(A C π)
      = (1/q²) ∑_{k,j} hatAlpha(k) hatGamma(j) K_q(k,j;π).
```

This is the formal statement that the two-factor centred completion produces a
**complete Kloosterman sum** (`COMPLETE-KLOOSTERMAN-PRODUCED45`); no analytic
bound on `K_q` is claimed. -/
theorem twoFactor_centered_completion (h2 : IsUnit (2 : ZMod q))
    (alpha gamma : ZMod q → ℂ) (pi : (ZMod q)ˣ) :
    (∑ A : ZMod q, ∑ C : ZMod q,
        alpha A * gamma C * centeredProjector q (A * C * (pi : ZMod q)))
      = ((q : ℂ) ^ 2)⁻¹ * ∑ k : ZMod q, ∑ j : ZMod q,
          dftHat q alpha k * dftHat q gamma j * centeredKloostermanKernel q k j pi := by
  classical
  have hq := cast_card_ne_zero q
  have expand : ∀ A C : ZMod q,
      alpha A * gamma C * centeredProjector q (A * C * (pi : ZMod q))
        = ((q : ℂ) ^ 2)⁻¹ * ∑ k : ZMod q, ∑ j : ZMod q,
            (dftHat q alpha k * dftHat q gamma j *
              (eM q (k * A) * eM q (j * C) * centeredProjector q (A * C * (pi : ZMod q)))) := by
    intro A C
    have h1 : (∑ k : ZMod q, ∑ j : ZMod q,
        dftHat q alpha k * dftHat q gamma j *
          (eM q (k * A) * eM q (j * C) * centeredProjector q (A * C * (pi : ZMod q))))
        = ((∑ k : ZMod q, dftHat q alpha k * eM q (k * A)) *
            (∑ j : ZMod q, dftHat q gamma j * eM q (j * C))) *
          centeredProjector q (A * C * (pi : ZMod q)) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1]
    conv_lhs => rw [fourier_inversion alpha A, fourier_inversion gamma C]
    ring
  rw [Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun C _ => expand A C]
  simp only [← Finset.mul_sum]
  congr 1
  rw [sum_comm4 (fun A C k j =>
    dftHat q alpha k * dftHat q gamma j *
      (eM q (k * A) * eM q (j * C) * centeredProjector q (A * C * (pi : ZMod q))))]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have hin : ∀ A : ZMod q,
      (∑ C : ZMod q, dftHat q alpha k * dftHat q gamma j *
        (eM q (k * A) * eM q (j * C) * centeredProjector q (A * C * (pi : ZMod q))))
        = dftHat q alpha k * dftHat q gamma j *
          ∑ C : ZMod q, (eM q (k * A) * eM q (j * C) *
            centeredProjector q (A * C * (pi : ZMod q))) := by
    intro A; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun A _ => hin A, ← Finset.mul_sum,
    centered_twoFrequency_transform h2 k j pi]

end FM722
end CurrentProgramme
end TwinPrimeProject
