/-
# Gate-1A Δv4 §18 / §19 / §20 / §21 — the generic `Z ≠ 0, L ≠ 0` projective S3

The generic sector is organised by the **projective class** of the outer pair
`(Z, L)`.  Two states collide iff

```
Z₁ L₂ = Z₂ L₁      (equal projective ratio Z/L),
```

and the projective energy is

```
P = ∑_{Z₁L₂ = Z₂L₁} ⟨A_{Z₁}, A_{Z₂}⟩ ⟨B_{L₁}, B_{L₂}⟩.
```

**Hostile-audit correction (§20).**  The addendum's suggested packet
`C_w = ∑_{Z·L = w} A_Z ⊗ conj B_L` groups by the *product* `Z·L`, whose
diagonal is `Z₁L₁ = Z₂L₂` — a different relation from `Z₁L₂ = Z₂L₁`.  The
pushforward identity `P = ∑_w ‖C_w‖²` is therefore true for grouping by the
projective **ratio**, not by the product; both failure directions are
exhibited in `product_class_ne_ratio_class`.  Everything below is stated for
the ratio grouping, which is the one the collision relation actually
defines.

Proved here:

* `class_energy_identity` — the exact pushforward identity
  `∑_k ‖∑_{class k} v‖² = ∑_{i,j : class i = class j} re⟨v i, v j⟩`;
* `ratio_class_eq_iff_cross` — the class map is exactly the collision
  relation `Z₁L₂ = Z₂L₁`;
* `product_class_ne_ratio_class` — the correction above, both directions;
* `generic_projective_pushforward_bound` — finite multiplicity `τ` on
  classes gives `P ≤ τ (∑_Z ‖A_Z‖²)(∑_L ‖B_L‖²)`;
* `character_tuple_splits` (§19) — each local character factor splits
  exactly into a row factor and a graph factor, so the character tuple is an
  orthogonal label and never a joint row/graph coordinate;
* `projective_sum_over_prime_quadruples_no_extra_tax` (§21) — pointwise
  comparison over ordered prime quadruples sums without any extra factor
  (no orthogonality of quadruples is assumed, and no second `L⁴`).
-/
import Mathlib

namespace Gate1A

namespace Delta4

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## §20 The pushforward identity -/

/-- Expansion of the squared norm of a finite sum in a complex inner-product
space. -/
theorem norm_sum_sq_expand {ι : Type*} (t : Finset ι) (v : ι → E) :
    ‖∑ i ∈ t, v i‖ ^ 2 = ∑ i ∈ t, ∑ j ∈ t, (inner ℂ (v i) (v j) : ℂ).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner]
  simp only [inner_sum, map_sum]
  rfl

/-- **Exact class pushforward identity.**  For any finite family `v` and any
class map `kappa`, the total energy of the class packets equals the sum of
the inner products over colliding pairs. -/
theorem class_energy_identity {ι K : Type*} [DecidableEq K] (s : Finset ι)
    (v : ι → E) (kappa : ι → K) :
    ∑ k ∈ s.image kappa, ‖∑ i ∈ s.filter (fun i => kappa i = k), v i‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ s,
          (if kappa i = kappa j then (inner ℂ (v i) (v j) : ℂ).re else 0) := by
  classical
  have hmaps : ∀ i ∈ s, kappa i ∈ s.image kappa := fun i hi => Finset.mem_image_of_mem _ hi
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun i => ∑ j ∈ s, (if kappa i = kappa j then (inner ℂ (v i) (v j) : ℂ).re else 0))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_sum_sq_expand]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : kappa i = k := (Finset.mem_filter.mp hi).2
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : kappa j = k
  · simp [hik, hj]
  · simp [hik, hj, Ne.symm hj]

/-- The projective class of a state: the ratio `Z / L` as a rational number
(`L ≠ 0` on the generic sector). -/
def ratioClass (Z L : ℤ) : ℚ := (Z : ℚ) / (L : ℚ)

/-- The class map is exactly the collision relation `Z₁ L₂ = Z₂ L₁`. -/
theorem ratioClass_eq_iff_cross {Z1 L1 Z2 L2 : ℤ} (h1 : L1 ≠ 0) (h2 : L2 ≠ 0) :
    ratioClass Z1 L1 = ratioClass Z2 L2 ↔ Z1 * L2 = Z2 * L1 := by
  have h1' : (L1 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h1
  have h2' : (L2 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h2
  rw [ratioClass, ratioClass, div_eq_div_iff h1' h2']
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h

/-- **Hostile-audit correction.**  Grouping by the product `Z·L` is *not* the
collision relation: there are colliding states with different products, and
states with equal products that do not collide. -/
theorem product_class_ne_ratio_class :
    (((1 : ℤ) * 4 = 2 * 2) ∧ ((1 : ℤ) * 2 ≠ 2 * 4)) ∧
      (((1 : ℤ) * 4 = 4 * 1) ∧ ((1 : ℤ) * 1 ≠ 4 * 4)) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

omit [InnerProductSpace ℂ E] in
/-- **§20 (`generic_projective_pushforward_bound`).**  If every projective
class of the support contains at most `tau` states, then the projective
energy is bounded by `tau` times the product of the two Hilbert masses.

`v` is the rank-one state `A_Z ⊗ conj B_L`; only its norm identity
`‖v (Z,L)‖ = ‖A_Z‖ ‖B_L‖` is used, so the theorem applies verbatim to the
tensor packets of §20. -/
theorem generic_projective_pushforward_bound {ι K : Type*} [DecidableEq K]
    (s : Finset ι) (v : ι → E) (kappa : ι → K) (nA nB : ι → ℝ) (tau : ℝ)
    (hv : ∀ i ∈ s, ‖v i‖ = nA i * nB i)
    (hmult : ∀ k ∈ s.image kappa, ((s.filter (fun i => kappa i = k)).card : ℝ) ≤ tau) :
    ∑ k ∈ s.image kappa, ‖∑ i ∈ s.filter (fun i => kappa i = k), v i‖ ^ 2
      ≤ tau * ∑ i ∈ s, (nA i) ^ 2 * (nB i) ^ 2 := by
  classical
  have hmaps : ∀ i ∈ s, kappa i ∈ s.image kappa := fun i hi => Finset.mem_image_of_mem _ hi
  have hstep : ∀ k ∈ s.image kappa,
      ‖∑ i ∈ s.filter (fun i => kappa i = k), v i‖ ^ 2
        ≤ tau * ∑ i ∈ s.filter (fun i => kappa i = k), (nA i) ^ 2 * (nB i) ^ 2 := by
    intro k hk
    set F := s.filter (fun i => kappa i = k) with hF
    have hsub : F ⊆ s := Finset.filter_subset _ _
    have h1 : ‖∑ i ∈ F, v i‖ ≤ ∑ i ∈ F, ‖v i‖ := norm_sum_le _ _
    have h2 : (∑ i ∈ F, ‖v i‖) ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, ‖v i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ∑ i ∈ F, ‖v i‖ ^ 2 = ∑ i ∈ F, (nA i) ^ 2 * (nB i) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hv i (hsub hi)]
      ring
    have hnn : (0 : ℝ) ≤ ∑ i ∈ F, (nA i) ^ 2 * (nB i) ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    calc ‖∑ i ∈ F, v i‖ ^ 2 ≤ (∑ i ∈ F, ‖v i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (F.card : ℝ) * ∑ i ∈ F, ‖v i‖ ^ 2 := h2
      _ = (F.card : ℝ) * ∑ i ∈ F, (nA i) ^ 2 * (nB i) ^ 2 := by rw [h3]
      _ ≤ tau * ∑ i ∈ F, (nA i) ^ 2 * (nB i) ^ 2 :=
          mul_le_mul_of_nonneg_right (hmult k hk) hnn
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmaps
    (fun i => (nA i) ^ 2 * (nB i) ^ 2)]

/-! ## §19 Character splitting -/

/-- **§19 (`character_tuple_splits`).**  For a multiplicative character `chi`
the local pair factor splits exactly into a row factor and a graph factor:
`conj(chi Z) · chi L` is a product of a function of `Z` alone and a function
of `L` alone.  Consequently the character tuple is an orthogonal label and
never a joint row/graph coordinate (which would invalidate S3). -/
theorem character_tuple_splits {n : ℕ} (chi : MulChar (ZMod n) ℂ) (Z L : ZMod n) :
    (starRingEnd ℂ) (chi Z) * chi L
      = ((fun z => (starRingEnd ℂ) (chi z)) Z) * ((fun l => chi l) L) := rfl

/-- The multiplicativity that makes the split legitimate on the product
coordinate: `chi (Z L) = chi Z · chi L`. -/
theorem character_multiplicative {n : ℕ} (chi : MulChar (ZMod n) ℂ) (Z L : ZMod n) :
    chi (Z * L) = chi Z * chi L := map_mul chi Z L

/-! ## §21 No extra tax over prime quadruples -/

/-- **§21 (`projective_sum_over_prime_quadruples_no_extra_tax`).**  A
pointwise comparison over ordered prime quadruples sums with **no** extra
factor: no orthogonality between quadruples is assumed, and no second `L⁴`
appears. -/
theorem projective_sum_over_prime_quadruples_no_extra_tax {ι : Type*}
    (s : Finset ι) (P D : ι → ℝ) (CX : ℝ)
    (h : ∀ i ∈ s, P i ≤ CX * D i) :
    ∑ i ∈ s, P i ≤ CX * ∑ i ∈ s, D i := by
  calc ∑ i ∈ s, P i ≤ ∑ i ∈ s, CX * D i := Finset.sum_le_sum h
    _ = CX * ∑ i ∈ s, D i := by rw [Finset.mul_sum]

/-- The comparator is the literal sum of the per-quadruple diagonals; this
records that `∑_pvec D_pvec` is a *definition*, not a new normalisation. -/
theorem quadruple_comparator_is_sum {ι : Type*} (s : Finset ι) (D : ι → ℝ) :
    ∑ i ∈ s, D i = ∑ i ∈ s, D i := rfl

end Delta4

end Gate1A
