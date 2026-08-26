import RequestProject.NANC.Gate01Consolidation.CRTCentering

/-!
# BANK J — the product-mode (ANOVA) obstruction

Finite product model of the two coprime coordinates: `y = (y₁, y₂)` with
`y₁ ∈ {0, …, d−1}`, `y₂ ∈ {0, …, p−1}`, and natural centering in each
coordinate,

`f(y₁, y₂) = ρ_d(y₁) ρ_p(y₂)`,   `ρ_d(y₁) = 1_{y₁ = 0} − 1/d`.

(Under the CRT this is exactly the double-centered mixed mode
`ρ_d(y) ρ_p(y)` of `CRTCentering`.)

Proved:

* every one-coordinate projection of `f` vanishes
  (`sum_mixedMode_fst`, `sum_mixedMode_snd`);
* **ANOVA** the normalised square mass is `(1/d − 1/d²)(1/p − 1/p²)`
  (`mixedMode_l2`), which is strictly positive for `d, p > 1`.

Formal consequence (`zero_projections_not_imply_zero_mixed_mode`):

```text
zero one-coordinate projections do NOT imply a zero mixed product mode
```

so

```text
TYPE-I-IN-d + TYPE-I-IN-p  DOES NOT FORMALLY IMPLY  DOUBLE-CENTERED PRODUCT CONTROL.
```

This refutes only the *formal implication*.  It is **not** a no-go theorem for
analytic iterated dispersion, and nothing of the sort is stated here.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-- One-coordinate natural centering on `{0, …, d−1}`. -/
noncomputable def coordCentering (d : ℕ) (y : ℕ) : ℝ := (if y = 0 then (1 : ℝ) else 0) - 1 / d

/-- The double-centered mixed product mode on the finite product space. -/
noncomputable def mixedMode (d p : ℕ) (y : ℕ × ℕ) : ℝ :=
  coordCentering d y.1 * coordCentering p y.2

/-- The one-coordinate centering has mean zero. -/
theorem sum_coordCentering {d : ℕ} (hd : 0 < d) :
    ∑ y ∈ Finset.range d, coordCentering d y = 0 := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  unfold coordCentering
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range d) 0 (fun _ => (1 : ℝ))]
  rw [if_pos (Finset.mem_range.mpr hd), Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one_div, div_self hdR, sub_self]

/-- The square mass of the one-coordinate centering. -/
theorem sum_sq_coordCentering {d : ℕ} (hd : 0 < d) :
    ∑ y ∈ Finset.range d, (coordCentering d y) ^ 2 = 1 - 1 / d := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsplit : ∀ y ∈ Finset.range d,
      (coordCentering d y) ^ 2
        = (if y = 0 then (1 : ℝ) else 0) * (1 - 2 / d) + 1 / (d : ℝ) ^ 2 := by
    intro y _
    unfold coordCentering
    by_cases hy : y = 0
    · simp only [if_pos hy]; field_simp; ring
    · simp only [if_neg hy]; field_simp; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_ite_eq' (Finset.range d) 0 (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_range.mpr hd), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- Every projection onto the first coordinate vanishes. -/
theorem sum_mixedMode_fst {d p : ℕ} (hd : 0 < d) (y₂ : ℕ) :
    ∑ y₁ ∈ Finset.range d, mixedMode d p (y₁, y₂) = 0 := by
  unfold mixedMode
  simp only []
  rw [← Finset.sum_mul, sum_coordCentering hd, zero_mul]

/-- Every projection onto the second coordinate vanishes. -/
theorem sum_mixedMode_snd {d p : ℕ} (hp : 0 < p) (y₁ : ℕ) :
    ∑ y₂ ∈ Finset.range p, mixedMode d p (y₁, y₂) = 0 := by
  unfold mixedMode
  simp only []
  rw [← Finset.mul_sum, sum_coordCentering hp, mul_zero]

/-- **ANOVA.**  The normalised square mass of the mixed mode. -/
theorem mixedMode_l2 {d p : ℕ} (hd : 0 < d) (hp : 0 < p) :
    (1 / ((d : ℝ) * p)) * ∑ y ∈ Finset.range d ×ˢ Finset.range p, (mixedMode d p y) ^ 2
      = (1 / d - 1 / (d : ℝ) ^ 2) * (1 / p - 1 / (p : ℝ) ^ 2) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hprod : ∑ y ∈ Finset.range d ×ˢ Finset.range p, (mixedMode d p y) ^ 2
      = (∑ y₁ ∈ Finset.range d, (coordCentering d y₁) ^ 2)
        * (∑ y₂ ∈ Finset.range p, (coordCentering p y₂) ^ 2) := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y₁ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y₂ _ => ?_)
    unfold mixedMode
    ring
  rw [hprod, sum_sq_coordCentering hd, sum_sq_coordCentering hp]
  field_simp

/-- **Kill 3.**  Zero one-coordinate projections do not imply a vanishing mixed
product mode: for `d, p > 1` the mixed mode has all projections zero yet
strictly positive square mass. -/
theorem zero_projections_not_imply_zero_mixed_mode {d p : ℕ} (hd : 1 < d) (hp : 1 < p) :
    (∀ y₂, ∑ y₁ ∈ Finset.range d, mixedMode d p (y₁, y₂) = 0) ∧
    (∀ y₁, ∑ y₂ ∈ Finset.range p, mixedMode d p (y₁, y₂) = 0) ∧
    0 < (1 / ((d : ℝ) * p)) * ∑ y ∈ Finset.range d ×ˢ Finset.range p, (mixedMode d p y) ^ 2 := by
  have hd0 : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_one hd.le
  have hp0 : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le
  refine ⟨fun y₂ => sum_mixedMode_fst hd0 y₂, fun y₁ => sum_mixedMode_snd hp0 y₁, ?_⟩
  rw [mixedMode_l2 hd0 hp0]
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have h1 : 0 < 1 / (d : ℝ) - 1 / (d : ℝ) ^ 2 := by
    have hd0R : (0 : ℝ) < d := lt_trans zero_lt_one hdR
    have := one_div_lt_one_div_of_lt hd0R (show (d : ℝ) < (d : ℝ) ^ 2 by nlinarith)
    linarith
  have h2 : 0 < 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 := by
    have hp0R : (0 : ℝ) < p := lt_trans zero_lt_one hpR
    have := one_div_lt_one_div_of_lt hp0R (show (p : ℝ) < (p : ℝ) ^ 2 by nlinarith)
    linarith
  exact mul_pos h1 h2

end Gate01Consolidation
end TwinPrimeProject
