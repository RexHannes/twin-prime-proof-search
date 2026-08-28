import Mathlib.Tactic

/-!
# Phase B · exact `2|2` model split (`ENDPOINT-2x2-MODEL-SPLIT45`)

**Exact finite algebra.**  No asymptotics, no injectivity assumption, no
multiplicity hand-waving: repeated factors are counted exactly as the finite
sums count them.

For four finitely supported coefficient functions `f₁,…,f₄` on a commutative
monoid `M` (in the application `M = ℤ`, multiplicatively) put

  `α(m) = ∑_{x₁x₂ = m} f₁(x₁) f₂(x₂)`,
  `γ(r) = ∑_{x₃x₄ = r} f₃(x₃) f₄(x₄)`,
  `a₄(u) = ∑_{x₁x₂x₃x₄ = u} f₁(x₁)f₂(x₂)f₃(x₃)f₄(x₄)`.

`conv4_eq_conv2_conv2` proves exactly

  `a₄(u) = ∑_{m r = u} α(m) γ(r)`.

The only hypotheses are *support-coverage* hypotheses: the finsets `Pm`, `Pr`
over which the outer convolution runs must contain the products `x₁x₂` and
`x₃x₄`.  Those are load-bearing — see `coverage_is_load_bearing`.

`sum_conv2_weight` is the companion rewriting lemma used downstream: a weighted
sum of `a₄` over a covering finset is exactly the double sum of `α γ` against
the weight evaluated at `m r`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace TwoByTwo

open Finset

variable {M : Type*} [CommMonoid M] [DecidableEq M]

/-! ## 1. The generic exact grouping lemma -/

omit [CommMonoid M] in
/-- **Generic exact grouping.**  If the value finset `Pm` covers the image of
`p` on `I`, then grouping `w` by the values of `p` and testing against an
arbitrary weight `G` is exact.  No injectivity of `p` is assumed, so repeated
values (repeated factorisations) are counted with their exact multiplicity. -/
theorem sum_group_one {ι : Type*} (I : Finset ι) (p : ι → M) (w : ι → ℂ)
    (Pm : Finset M) (hp : ∀ i ∈ I, p i ∈ Pm) (G : M → ℂ) :
    ∑ m ∈ Pm, (∑ i ∈ I, if p i = m then w i else 0) * G m
      = ∑ i ∈ I, w i * G (p i) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq Pm (p i) (fun m => w i * G m), if_pos (hp i hi)]

/-! ## 2. Two- and four-factor convolutions -/

/-- The exact finite two-factor convolution supported on `S ×ˢ T`. -/
noncomputable def conv2 (S T : Finset M) (f g : M → ℂ) (m : M) : ℂ :=
  ∑ x ∈ S, ∑ y ∈ T, if x * y = m then f x * g y else 0

/-- The exact finite four-factor coefficient `a₄`. -/
noncomputable def conv4 (S₁ S₂ S₃ S₄ : Finset M) (f₁ f₂ f₃ f₄ : M → ℂ) (u : M) : ℂ :=
  ∑ x₁ ∈ S₁, ∑ x₂ ∈ S₂, ∑ x₃ ∈ S₃, ∑ x₄ ∈ S₄,
    if x₁ * x₂ * (x₃ * x₄) = u then f₁ x₁ * f₂ x₂ * (f₃ x₃ * f₄ x₄) else 0

/-- `conv2` as a single sum over the product finset. -/
theorem conv2_eq_sum_product (S T : Finset M) (f g : M → ℂ) (m : M) :
    conv2 S T f g m
      = ∑ z ∈ S ×ˢ T, if z.1 * z.2 = m then f z.1 * g z.2 else 0 := by
  rw [Finset.sum_product]
  rfl

/-- **Weighted rewriting.**  For any weight `F`, a sum of a two-factor
convolution against `F` over a covering finset equals the exact double sum. -/
theorem sum_conv2_weight (Pm Pr Us : Finset M) (α γ : M → ℂ) (F : M → ℂ)
    (hcov : ∀ m ∈ Pm, ∀ r ∈ Pr, m * r ∈ Us) :
    ∑ u ∈ Us, conv2 Pm Pr α γ u * F u
      = ∑ m ∈ Pm, ∑ r ∈ Pr, α m * γ r * F (m * r) := by
  classical
  have hp : ∀ z ∈ Pm ×ˢ Pr, z.1 * z.2 ∈ Us := by
    intro z hz
    rw [Finset.mem_product] at hz
    exact hcov z.1 hz.1 z.2 hz.2
  have h := sum_group_one (M := M) (Pm ×ˢ Pr) (fun z => z.1 * z.2)
      (fun z => α z.1 * γ z.2) Us hp F
  rw [Finset.sum_congr rfl (fun u _ => by rw [conv2_eq_sum_product]), h,
    Finset.sum_product]

/-- **`ENDPOINT-2x2-MODEL-SPLIT45`.**  The exact `2|2` factorisation of the
four-factor coefficient: `a₄(u) = ∑_{m r = u} α(m) γ(r)`, with exact
multiplicity. -/
theorem conv4_eq_conv2_conv2 (S₁ S₂ S₃ S₄ Pm Pr : Finset M) (f₁ f₂ f₃ f₄ : M → ℂ)
    (hPm : ∀ x₁ ∈ S₁, ∀ x₂ ∈ S₂, x₁ * x₂ ∈ Pm)
    (hPr : ∀ x₃ ∈ S₃, ∀ x₄ ∈ S₄, x₃ * x₄ ∈ Pr) (u : M) :
    conv4 S₁ S₂ S₃ S₄ f₁ f₂ f₃ f₄ u
      = conv2 Pm Pr (conv2 S₁ S₂ f₁ f₂) (conv2 S₃ S₄ f₃ f₄) u := by
  classical
  have hp₁ : ∀ z ∈ S₁ ×ˢ S₂, z.1 * z.2 ∈ Pm := by
    intro z hz; rw [Finset.mem_product] at hz; exact hPm z.1 hz.1 z.2 hz.2
  have hp₂ : ∀ z ∈ S₃ ×ˢ S₄, z.1 * z.2 ∈ Pr := by
    intro z hz; rw [Finset.mem_product] at hz; exact hPr z.1 hz.1 z.2 hz.2
  -- step 1 : group the `r`-side, for each fixed `m`
  have step_r : ∀ m : M,
      ∑ r ∈ Pr, conv2 S₃ S₄ f₃ f₄ r * (if m * r = u then (1 : ℂ) else 0)
        = ∑ z ∈ S₃ ×ˢ S₄, (f₃ z.1 * f₄ z.2) *
            (if m * (z.1 * z.2) = u then (1 : ℂ) else 0) := by
    intro m
    have := sum_group_one (M := M) (S₃ ×ˢ S₄) (fun z => z.1 * z.2)
        (fun z => f₃ z.1 * f₄ z.2) Pr hp₂ (fun r => if m * r = u then (1 : ℂ) else 0)
    rw [← this]
    exact Finset.sum_congr rfl fun r _ => by rw [conv2_eq_sum_product]
  -- step 2 : group the `m`-side, for each fixed `(x₃, x₄)`
  have step_m : ∀ z : M × M,
      ∑ m ∈ Pm, conv2 S₁ S₂ f₁ f₂ m * ((f₃ z.1 * f₄ z.2) *
          (if m * (z.1 * z.2) = u then (1 : ℂ) else 0))
        = ∑ y ∈ S₁ ×ˢ S₂, (f₁ y.1 * f₂ y.2) * ((f₃ z.1 * f₄ z.2) *
            (if (y.1 * y.2) * (z.1 * z.2) = u then (1 : ℂ) else 0)) := by
    intro z
    have := sum_group_one (M := M) (S₁ ×ˢ S₂) (fun y => y.1 * y.2)
        (fun y => f₁ y.1 * f₂ y.2) Pm hp₁
        (fun m => (f₃ z.1 * f₄ z.2) * (if m * (z.1 * z.2) = u then (1 : ℂ) else 0))
    rw [← this]
    exact Finset.sum_congr rfl fun m _ => by rw [conv2_eq_sum_product]
  have hite : ∀ (c : Prop) [Decidable c] (A : ℂ), (if c then A else 0) = A * (if c then 1 else 0) := by
    intro c _ A; by_cases h : c <;> simp [h]
  calc conv4 S₁ S₂ S₃ S₄ f₁ f₂ f₃ f₄ u
      = ∑ y ∈ S₁ ×ˢ S₂, ∑ z ∈ S₃ ×ˢ S₄, (f₁ y.1 * f₂ y.2) * ((f₃ z.1 * f₄ z.2) *
          (if (y.1 * y.2) * (z.1 * z.2) = u then (1 : ℂ) else 0)) := by
        rw [conv4, Finset.sum_product]
        refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => ?_
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun x₃ _ => Finset.sum_congr rfl fun x₄ _ => ?_
        rw [hite]
        ring
    _ = ∑ z ∈ S₃ ×ˢ S₄, ∑ m ∈ Pm, conv2 S₁ S₂ f₁ f₂ m * ((f₃ z.1 * f₄ z.2) *
          (if m * (z.1 * z.2) = u then (1 : ℂ) else 0)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun z _ => (step_m z).symm
    _ = ∑ m ∈ Pm, conv2 S₁ S₂ f₁ f₂ m *
          (∑ z ∈ S₃ ×ˢ S₄, (f₃ z.1 * f₄ z.2) *
            (if m * (z.1 * z.2) = u then (1 : ℂ) else 0)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
    _ = ∑ m ∈ Pm, conv2 S₁ S₂ f₁ f₂ m *
          (∑ r ∈ Pr, conv2 S₃ S₄ f₃ f₄ r * (if m * r = u then (1 : ℂ) else 0)) := by
        exact Finset.sum_congr rfl fun m _ => by rw [step_r m]
    _ = conv2 Pm Pr (conv2 S₁ S₂ f₁ f₂) (conv2 S₃ S₄ f₃ f₄) u := by
        rw [conv2]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        split_ifs <;> ring


/-! ## 4. Conjugated form (used by the centered rewriting) -/

/-- The conjugate of a two-factor convolution is the convolution of the
conjugates. -/
theorem conv2_conj (S T : Finset M) (f g : M → ℂ) (m : M) :
    (starRingEnd ℂ) (conv2 S T f g m)
      = conv2 S T (fun x => (starRingEnd ℂ) (f x))
          (fun y => (starRingEnd ℂ) (g y)) m := by
  classical
  unfold conv2
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : x * y = m <;> simp [h]

/-- **Conjugated weighted rewriting.**  The companion of `sum_conv2_weight` for
the conjugated factor of a bilinear/energy expression. -/
theorem sum_conv2_conj_weight (Pm Pr Us : Finset M) (α γ : M → ℂ) (F : M → ℂ)
    (hcov : ∀ m ∈ Pm, ∀ r ∈ Pr, m * r ∈ Us) :
    ∑ u ∈ Us, (starRingEnd ℂ) (conv2 Pm Pr α γ u) * F u
      = ∑ m ∈ Pm, ∑ r ∈ Pr, (starRingEnd ℂ) (α m * γ r) * F (m * r) := by
  classical
  rw [Finset.sum_congr rfl (fun u (_ : u ∈ Us) => by rw [conv2_conj]),
    sum_conv2_weight Pm Pr Us _ _ F hcov]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul]

/-! ## 5. Counterguard : coverage is load-bearing -/

/-- **Counterguard.**  Without the coverage hypotheses the `2|2` split is false:
if `Pm` misses a product, mass is lost.  Witness in `M = ℕ` (multiplicative):
`S₁ = S₂ = S₃ = S₄ = {1}`, all `f ≡ 1`, `u = 1`, but `Pm = ∅`. -/
theorem coverage_is_load_bearing :
    conv4 ({1} : Finset ℕ) {1} {1} {1} (fun _ => 1) (fun _ => 1) (fun _ => 1)
        (fun _ => 1) 1
      ≠ conv2 (∅ : Finset ℕ) {1} (conv2 {1} {1} (fun _ => 1) (fun _ => 1))
          (conv2 {1} {1} (fun _ => 1) (fun _ => 1)) 1 := by
  norm_num [conv4, conv2]

end TwoByTwo
end CurrentProgramme
end TwinPrimeProject
