import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD

/-!
# Phase A4 / A5 / A8 · exact rank-one determinant-2 line algebra

This is the **top analytic-priority source algebra** of the current
continuation: everything is over `ℤ`, so that no truncated subtraction can
hide a defect.

## The physical line

The endpoint line is the determinant-2 affine line

  `u * v₀ + 2 = ℓ * z₀`,   `v t = v₀ + ℓ * t`,   `z t = z₀ + u * t`.

`lineDet2_propagates` proves `u * v t + 2 = ℓ * z t` for every `t : ℤ`.

## Endpoint residue geometry (A5)

Modulo `ℓ` the relation reads `u * v₀ ≡ -2`.  When `-2` is a unit mod `ℓ` the
map `u ↦ (-2) * u⁻¹` on `(ZMod ℓ)ˣ` is an involution, hence a permutation
(`negTwoInv_involutive`, `negTwoInvEquiv`).

**Counterguard.**  `residue_permutation_gives_no_interval_multiplicity_bound`
records, as an explicit theorem, that a permutation of residues does *not*
bound the number of *integers* `u` in an interval lying in a fixed class: the
fibre must be retained.

## Off-diagonal pair algebra (A8) — LOAD-BEARING

For a congruent pair `u₂ = u₁ + j * ℓ` sharing the residue representative
`v₀`:

* `offdiag_basepoint_shift` :  `z₀(u + jℓ) - z₀(u) = j * v₀`;
* `offdiag_line_difference` :  `z₂ t₂ - z₁ t₁ = u * (t₂ - t₁) + j * v t₂`.

Both are kernel-checked exact integer identities.  No estimate is made.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace RankOne

/-! ## 1. The line -/

/-- The `v`-coordinate of the rank-one line: `v t = v₀ + ℓ t`. -/
def vPt (v₀ ℓ t : ℤ) : ℤ := v₀ + ℓ * t

/-- The `z`-coordinate of the rank-one line: `z t = z₀ + u t`. -/
def zPt (z₀ u t : ℤ) : ℤ := z₀ + u * t

@[simp] theorem vPt_zero (v₀ ℓ : ℤ) : vPt v₀ ℓ 0 = v₀ := by simp [vPt]
@[simp] theorem zPt_zero (z₀ u : ℤ) : zPt z₀ u 0 = z₀ := by simp [zPt]

/-- **Determinant-2 line propagation.**  If the base point satisfies
`u v₀ + 2 = ℓ z₀`, then every line point satisfies `u v t + 2 = ℓ z t`.

This is the exact `u v + 2 = ℓ z` source relation, over `ℤ`. -/
theorem lineDet2_propagates {u v₀ ℓ z₀ : ℤ} (h : u * v₀ + 2 = ℓ * z₀) (t : ℤ) :
    u * vPt v₀ ℓ t + 2 = ℓ * zPt z₀ u t := by
  simp only [vPt, zPt]
  linarith [h]

/-- Conversely the base relation is the `t = 0` case, so
`lineDet2_propagates` is an exact equivalence, not a weakening. -/
theorem lineDet2_base_iff {u v₀ ℓ z₀ : ℤ} :
    (u * v₀ + 2 = ℓ * z₀) ↔ ∀ t : ℤ, u * vPt v₀ ℓ t + 2 = ℓ * zPt z₀ u t := by
  refine ⟨fun h => lineDet2_propagates h, fun h => ?_⟩
  simpa using h 0

/-! ## 2. Endpoint residue geometry (A5) -/

/-- The endpoint residue relation `u * v₀ ≡ -2 (mod ℓ)`, read off the line. -/
theorem endpoint_residue_relation {u v₀ ℓ z₀ : ℤ} (h : u * v₀ + 2 = ℓ * z₀) :
    (ℓ : ℤ) ∣ (u * v₀ + 2) := ⟨z₀, h⟩

/-- Modulo `ℓ`, the endpoint relation is `u * v₀ = -2`. -/
theorem endpoint_residue_zmod {u v₀ ℓ z₀ : ℤ} (h : u * v₀ + 2 = ℓ * z₀)
    (n : ℕ) (hn : (n : ℤ) = ℓ) :
    ((u : ZMod n) * (v₀ : ZMod n)) = (-2 : ZMod n) := by
  have hdvd : (n : ℤ) ∣ (u * v₀ + 2) := by rw [hn]; exact ⟨z₀, h⟩
  have : ((u * v₀ + 2 : ℤ) : ZMod n) = 0 := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 hdvd
  push_cast at this
  linear_combination this

/-- The endpoint residue map `u ↦ (-2) u⁻¹` on the units mod `ℓ`. -/
noncomputable def negTwoInv {n : ℕ} (h : IsUnit (-2 : ZMod n)) (u : (ZMod n)ˣ) :
    (ZMod n)ˣ :=
  h.unit * u⁻¹

/-- **A5(1).**  `u ↦ (-2) u⁻¹` is an involution on `(ZMod ℓ)ˣ`. -/
theorem negTwoInv_involutive {n : ℕ} (h : IsUnit (-2 : ZMod n)) :
    Function.Involutive (negTwoInv h) := by
  intro u
  simp [negTwoInv, mul_inv_rev, mul_comm, mul_left_comm]

/-- **A5(1).**  Consequently it is a bijection (permutation) of the unit
group. -/
noncomputable def negTwoInvEquiv {n : ℕ} (h : IsUnit (-2 : ZMod n)) :
    (ZMod n)ˣ ≃ (ZMod n)ˣ :=
  (negTwoInv_involutive h).toPerm

theorem negTwoInv_bijective {n : ℕ} (h : IsUnit (-2 : ZMod n)) :
    Function.Bijective (negTwoInv h) :=
  (negTwoInv_involutive h).bijective

/-- The defining property: `negTwoInv h u * u = -2`. -/
theorem negTwoInv_spec {n : ℕ} (h : IsUnit (-2 : ZMod n)) (u : (ZMod n)ˣ) :
    ((negTwoInv h u : (ZMod n)ˣ) : ZMod n) * (u : ZMod n) = (-2 : ZMod n) := by
  simp only [negTwoInv, Units.val_mul]
  rw [mul_assoc]
  simp

/-- **A5(2) — COUNTERGUARD.**  A permutation of residue classes gives *no*
bounded-multiplicity statement for integers in an interval.  Concretely: with
`ℓ = 3` the class of `1` mod `3` meets `{0,…,U}` roughly `U/3` times, so the
fibre grows without bound.  Hence the fibre over a residue must be retained
explicitly, exactly as A5(3) requires. -/
theorem residue_permutation_gives_no_interval_multiplicity_bound :
    ∀ C : ℕ, ∃ U : ℕ,
      C < ((Finset.range U).filter (fun u => u % 3 = 1)).card := by
  intro C
  refine ⟨3 * (C + 1), ?_⟩
  have : ((Finset.range (3 * (C + 1))).filter (fun u => u % 3 = 1)).card = C + 1 := by
    induction C with
    | zero => decide
    | succ k ih =>
        have hstep : 3 * (k + 1 + 1) = (3 * (k + 1)) + 1 + 1 + 1 := by ring
        rw [hstep, Finset.range_add_one, Finset.range_add_one, Finset.range_add_one]
        rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert]
        have h0 : ¬ ((3 * (k + 1) + 1 + 1) % 3 = 1) := by omega
        have h1 : (3 * (k + 1) + 1) % 3 = 1 := by omega
        have h2 : ¬ ((3 * (k + 1)) % 3 = 1) := by omega
        simp only [h0, h1, h2, if_true, if_false]
        rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_filter, Finset.mem_range]
          rintro ⟨hlt, -⟩; omega)]
        rw [ih]
  omega

/-! ## 3. Off-diagonal congruent-pair algebra (A8) — LOAD-BEARING -/

/-- **A8, base-point shift.**  Two moduli-congruent multipliers `u` and
`u + jℓ` sharing the residue representative `v₀` have base points differing by
exactly `j * v₀`.

Hypotheses are the two literal line relations; `ℓ ≠ 0` is needed to cancel. -/
theorem offdiag_basepoint_shift {u j ℓ v₀ z₀ z₀' : ℤ} (hℓ : ℓ ≠ 0)
    (h₁ : u * v₀ + 2 = ℓ * z₀)
    (h₂ : (u + j * ℓ) * v₀ + 2 = ℓ * z₀') :
    z₀' - z₀ = j * v₀ := by
  have h : ℓ * (z₀' - z₀) = ℓ * (j * v₀) := by ring_nf; ring_nf at h₁ h₂; linarith
  exact mul_left_cancel₀ hℓ h

/-- **A8, the load-bearing off-diagonal line identity.**

With `u₂ = u + jℓ`, base points `z₀` and `z₀'` on the two lines sharing the
residue representative `v₀`, the difference of an arbitrary point of the second
line and an arbitrary point of the first is

  `z₂ t₂ - z₁ t₁ = u (t₂ - t₁) + j * v t₂`.

Note the second term carries `v` evaluated at `t₂`, not at `t₁`. -/
theorem offdiag_line_difference {u j ℓ v₀ z₀ z₀' t₁ t₂ : ℤ} (hℓ : ℓ ≠ 0)
    (h₁ : u * v₀ + 2 = ℓ * z₀)
    (h₂ : (u + j * ℓ) * v₀ + 2 = ℓ * z₀') :
    zPt z₀' (u + j * ℓ) t₂ - zPt z₀ u t₁ = u * (t₂ - t₁) + j * vPt v₀ ℓ t₂ := by
  have hb : z₀' - z₀ = j * v₀ := offdiag_basepoint_shift hℓ h₁ h₂
  simp only [zPt, vPt]
  linarith [hb]

/-- The same identity in the purely algebraic form used downstream: no line
relations, just the base-point shift as a hypothesis. -/
theorem offdiag_line_difference_of_shift {u j ℓ v₀ z₀ z₀' t₁ t₂ : ℤ}
    (hb : z₀' - z₀ = j * v₀) :
    zPt z₀' (u + j * ℓ) t₂ - zPt z₀ u t₁ = u * (t₂ - t₁) + j * vPt v₀ ℓ t₂ := by
  simp only [zPt, vPt]; linarith [hb]

/-- **Diagonal specialisation** (`j = 0`): the two lines coincide and the
difference is the pure shift `u Δt`. -/
theorem diag_line_difference {u ℓ v₀ z₀ t₁ t₂ : ℤ} :
    zPt z₀ (u + 0 * ℓ) t₂ - zPt z₀ u t₁ = u * (t₂ - t₁) + 0 * vPt v₀ ℓ t₂ := by
  simp only [zPt, vPt]; ring

/-- **Independent adjudication of the load-bearing identity.**  A closed
numerical instance recomputed from the definitions, verifying signs and the
`t₂`-evaluation of `v`: take `ℓ = 5`, `u = 3`, `v₀ = 1`, so `3·1+2 = 5·1`,
`z₀ = 1`; `u₂ = 3 + 2·5 = 13`, `13·1+2 = 15 = 5·3`, `z₀' = 3`.  With
`t₁ = 4`, `t₂ = 7`: `z₂ = 3 + 13·7 = 94`, `z₁ = 1 + 3·4 = 13`, difference `81`;
`u Δt + j v t₂ = 3·3 + 2·(1 + 5·7) = 9 + 72 = 81`. -/
theorem offdiag_line_difference_numeric_check :
    zPt 3 (3 + 2 * 5) 7 - zPt 1 3 4 = 3 * (7 - 4) + 2 * vPt 1 5 7 ∧
      zPt 3 (3 + 2 * 5) 7 - zPt 1 3 4 = 81 := by
  constructor <;> decide

/-! ## 4. Exact finite partition of the congruent pair set (A6) -/

/-- Pairs `(u₁, u₂)` from a finite source set that are congruent mod `ℓ`. -/
def congruentPairs (S : Finset ℤ) (ℓ : ℤ) : Finset (ℤ × ℤ) :=
  (S ×ˢ S).filter (fun p => ℓ ∣ (p.2 - p.1))

/-- **A6/A8 exact split.**  Every congruent pair is either diagonal
(`u₁ = u₂`) or off-diagonal, and the two children are disjoint and exhaustive.
This is an identity, not an estimate. -/
theorem congruentPairs_split (S : Finset ℤ) (ℓ : ℤ) (f : ℤ × ℤ → ℝ) :
    ∑ p ∈ congruentPairs S ℓ, f p =
      (∑ p ∈ (congruentPairs S ℓ).filter (fun p => p.1 = p.2), f p) +
      (∑ p ∈ (congruentPairs S ℓ).filter (fun p => ¬ p.1 = p.2), f p) :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **A8 parametrisation.**  A congruent pair with `ℓ ≠ 0` is exactly
`u₂ = u₁ + j ℓ` for a unique integer `j`, and it is off-diagonal precisely when
`j ≠ 0`. -/
theorem congruentPair_param {u₁ u₂ ℓ : ℤ} (hℓ : ℓ ≠ 0) (h : ℓ ∣ (u₂ - u₁)) :
    ∃! j : ℤ, u₂ = u₁ + j * ℓ := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, by linarith [hj], ?_⟩
  intro k hk
  have : k * ℓ = j * ℓ := by linarith [hj, hk]
  exact mul_right_cancel₀ hℓ this

theorem congruentPair_offdiag_iff {u₁ j ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    u₁ + j * ℓ ≠ u₁ ↔ j ≠ 0 := by
  constructor
  · intro h hj; exact h (by simp [hj])
  · intro hj h
    have : j * ℓ = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h' <;> [exact hj h'; exact hℓ h']

end RankOne
end CurrentProgramme
end TwinPrimeProject
