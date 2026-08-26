/-
# Gate-1A: the two finite countermodels (Sections 10 and 11)

Both models live on `X = Fin S × Fin N` with family `P = Fin S`, and use the
same fibre maps: `π p` crushes the block `B_p = {p} × Fin N` to a single point
and is the identity elsewhere.

* `moving_blocks_counterexample` (Section 10): amplitudes supported on the
  moving block only.  Pair-collision multiplicity is `≤ 1`, yet the collision
  energy is `S · N²`, i.e. there is **no** family-size saving.

* `common_envelope_not_diagonal_saving` (Section 11): amplitudes identically
  `1`, hence completely common across `p`.  Pair-collision multiplicity is
  again `≤ 1`, the off-diagonal collision energy is `S · N · (N-1)` while the
  diagonal mass is `S² · N`; so for `N ≍ S` the off-diagonal is **not** smaller
  than the diagonal by a factor `S⁻¹`.
-/
import Gate1A.MovingFamily

namespace Gate1A

open Finset

namespace Countermodel

variable {S N : ℕ} [NeZero N]

/-- The fibre map: crush the block `{p} × Fin N` to the point `(p, 0)`,
identity elsewhere. -/
def blockPr (p : Fin S) : Fin S × Fin N → Fin S × Fin N :=
  fun x => if x.1 = p then (p, 0) else x

/-- Section 10 amplitudes: the indicator of the moving block `B_p`. -/
def blockV (p : Fin S) : Fin S × Fin N → ℂ := fun x => if x.1 = p then 1 else 0

/-- Section 11 amplitudes: the constant common envelope. -/
def flatV (_p : Fin S) : Fin S × Fin N → ℂ := fun _ => 1

/-! ### Basic cardinalities -/

omit [NeZero N] in
theorem filter_fst_eq (p : Fin S) :
    (univ.filter (fun x : Fin S × Fin N => x.1 = p))
      = ({p} : Finset (Fin S)) ×ˢ (univ : Finset (Fin N)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    Finset.mem_singleton, and_true]

omit [NeZero N] in
theorem card_fst_eq (p : Fin S) :
    (univ.filter (fun x : Fin S × Fin N => x.1 = p)).card = N := by
  rw [filter_fst_eq]; simp

omit [NeZero N] in
theorem filter_fst_ne (p : Fin S) :
    (univ.filter (fun x : Fin S × Fin N => x.1 ≠ p))
      = ((univ : Finset (Fin S)).erase p) ×ˢ (univ : Finset (Fin N)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    Finset.mem_erase, and_true]

omit [NeZero N] in
theorem card_fst_ne (p : Fin S) :
    (univ.filter (fun x : Fin S × Fin N => x.1 ≠ p)).card = (S - 1) * N := by
  rw [filter_fst_ne, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ p)]
  simp

/-! ### Collision multiplicity: at most one family member -/

/-- `blockPr p x = blockPr p y` for `x ≠ y` forces `x.1 = y.1 = p`. -/
theorem blockPr_collide_iff {x y : Fin S × Fin N} (hxy : x ≠ y) (p : Fin S) :
    blockPr p x = blockPr p y ↔ (x.1 = p ∧ y.1 = p) := by
  constructor
  · intro h
    simp only [blockPr] at h
    by_cases hx : x.1 = p
    · by_cases hy : y.1 = p
      · exact ⟨hx, hy⟩
      · rw [if_pos hx, if_neg hy] at h
        exact absurd (congrArg Prod.fst h).symm hy
    · by_cases hy : y.1 = p
      · rw [if_neg hx, if_pos hy] at h
        exact absurd (congrArg Prod.fst h) hx
      · rw [if_neg hx, if_neg hy] at h
        exact absurd h hxy
  · rintro ⟨hx, hy⟩
    simp [blockPr, hx, hy]

/-- **Bounded pair-collision multiplicity.** For any two distinct points there
is at most one family member at which they collide. -/
theorem blockPr_collision_card_le_one (x y : Fin S × Fin N) (hxy : x ≠ y) :
    ((univ.filter (fun p : Fin S => blockPr p x = blockPr p y)).card : ℝ) ≤ 1 := by
  have hsub : univ.filter (fun p : Fin S => blockPr p x = blockPr p y) ⊆ {x.1} := by
    intro p hp
    rw [Finset.mem_filter, blockPr_collide_iff hxy p] at hp
    simp [hp.2.1]
  have h := Finset.card_le_card hsub
  rw [Finset.card_singleton] at h
  exact_mod_cast h

/-! ### Fibres of `blockPr` -/

theorem blockPr_fibre_base (p : Fin S) :
    (univ.filter (fun x : Fin S × Fin N => blockPr p x = (p, 0)))
      = univ.filter (fun x : Fin S × Fin N => x.1 = p) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockPr]
  by_cases hx : x.1 = p
  · simp [hx]
  · rw [if_neg hx]
    exact ⟨fun h => absurd (congrArg Prod.fst h) hx, fun h => absurd h hx⟩

theorem blockPr_fibre_other (p : Fin S) (xi : Fin S × Fin N) (hxi : xi ≠ (p, 0)) :
    (univ.filter (fun x : Fin S × Fin N => blockPr p x = xi))
      = univ.filter (fun x : Fin S × Fin N => x.1 ≠ p ∧ x = xi) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockPr]
  by_cases hx : x.1 = p
  · rw [if_pos hx]
    exact ⟨fun h => absurd h.symm hxi, fun h => absurd hx h.1⟩
  · rw [if_neg hx]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

/-- The block-indicator sums to `N` over the crushed fibre and to `0` elsewhere. -/
theorem blockV_fibre_sum (p : Fin S) (xi : Fin S × Fin N) :
    (∑ x ∈ univ.filter (fun x : Fin S × Fin N => blockPr p x = xi), blockV p x)
      = if xi = (p, 0) then (N : ℂ) else 0 := by
  by_cases h : xi = (p, 0)
  · subst h
    rw [blockPr_fibre_base, if_pos rfl]
    have hone : ∀ x ∈ univ.filter (fun x : Fin S × Fin N => x.1 = p), blockV p x = (1 : ℂ) :=
      fun x hx => by simp only [blockV, if_pos (Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, card_fst_eq, nsmul_eq_mul, mul_one]
  · rw [blockPr_fibre_other p xi h, if_neg h]
    refine Finset.sum_eq_zero fun x hx => ?_
    simp [blockV, (Finset.mem_filter.mp hx).2.1]

/-- The flat envelope sums to `N` over the crushed fibre and to `1` on each
singleton fibre `{ξ}` with `ξ.1 ≠ p` (and `0` on empty fibres). -/
theorem flatV_fibre_sum (p : Fin S) (xi : Fin S × Fin N) :
    (∑ x ∈ univ.filter (fun x : Fin S × Fin N => blockPr p x = xi), flatV p x)
      = if xi = (p, 0) then (N : ℂ) else if xi.1 ≠ p then 1 else 0 := by
  by_cases h : xi = (p, 0)
  · subst h
    rw [blockPr_fibre_base, if_pos rfl]
    simp only [flatV, Finset.sum_const, card_fst_eq, nsmul_eq_mul, mul_one]
  · rw [blockPr_fibre_other p xi h, if_neg h]
    by_cases h1 : xi.1 = p
    · rw [if_neg (by simpa using h1)]
      refine Finset.sum_eq_zero fun x hx => ?_
      exfalso
      obtain ⟨hne, heq⟩ := (Finset.mem_filter.mp hx).2
      exact hne (by rw [heq, h1])
    · rw [if_pos (by simpa using h1)]
      have hset : (univ.filter (fun x : Fin S × Fin N => x.1 ≠ p ∧ x = xi)) = {xi} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact h1, h⟩⟩
      rw [hset]
      simp [flatV]

/-! ### Section 10: the disjoint-moving-block countermodel -/

/-- **Disjoint-moving-block countermodel.**  The collision energy is `S · N²`,
even though every distinct pair collides for at most one family member.  Hence
bounded pair-collision multiplicity does **not** imply a family-size saving for
arbitrarily moving support. -/
theorem moving_blocks_counterexample :
    collisionEnergy (P := Fin S) (X := Fin S × Fin N) (E := ℂ)
        (Xi := fun _ => Fin S × Fin N) blockV blockPr = (S : ℝ) * (N : ℝ) ^ 2 := by
  simp only [collisionEnergy]
  have hp : ∀ p : Fin S,
      (∑ xi : Fin S × Fin N,
        ‖∑ x ∈ univ.filter (fun x : Fin S × Fin N => blockPr p x = xi), blockV p x‖ ^ 2)
        = (N : ℝ) ^ 2 := by
    intro p
    rw [Finset.sum_congr rfl (fun xi _ => by rw [blockV_fibre_sum p xi])]
    rw [Finset.sum_eq_single (p, 0)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun p _ => hp p)]
  simp [Finset.sum_const, nsmul_eq_mul]

omit [NeZero N] in
/-- The Section-10 diagonal mass is `S · N`. -/
theorem moving_blocks_diagonal :
    (∑ p : Fin S, ∑ x : Fin S × Fin N, ‖blockV (N := N) p x‖ ^ 2) = (S : ℝ) * (N : ℝ) := by
  have hp : ∀ p : Fin S, (∑ x : Fin S × Fin N, ‖blockV (N := N) p x‖ ^ 2) = (N : ℝ) := by
    intro p
    have hval : ∀ x : Fin S × Fin N, ‖blockV (N := N) p x‖ ^ 2
        = if x.1 = p then (1 : ℝ) else 0 := by
      intro x; by_cases h : x.1 = p <;> simp [blockV, h]
    rw [Finset.sum_congr rfl (fun x _ => hval x), Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, card_fst_eq]
    simp
  rw [Finset.sum_congr rfl (fun p _ => hp p)]
  simp [Finset.sum_const, nsmul_eq_mul]

/-! ### Section 11: the common-envelope normalization countermodel -/

/-- Total collision energy of the flat (completely common) envelope. -/
theorem common_envelope_energy :
    collisionEnergy (P := Fin S) (X := Fin S × Fin N) (E := ℂ)
        (Xi := fun _ => Fin S × Fin N) flatV blockPr
      = (S : ℝ) * (N : ℝ) ^ 2 + (S : ℝ) * ((S : ℝ) - 1) * (N : ℝ) := by
  simp only [collisionEnergy]
  have hp : ∀ p : Fin S,
      (∑ xi : Fin S × Fin N,
        ‖∑ x ∈ univ.filter (fun x : Fin S × Fin N => blockPr p x = xi), flatV p x‖ ^ 2)
        = (N : ℝ) ^ 2 + ((S : ℝ) - 1) * (N : ℝ) := by
    intro p
    have hS : 0 < S := lt_of_le_of_lt (Nat.zero_le p.val) p.isLt
    rw [Finset.sum_congr rfl (fun xi _ => by rw [flatV_fibre_sum p xi])]
    have hsplit : ∀ xi : Fin S × Fin N,
        ‖(if xi = (p, 0) then (N : ℂ) else if xi.1 ≠ p then 1 else 0)‖ ^ 2
          = (if xi = (p, 0) then (N : ℝ) ^ 2 else 0)
            + (if xi.1 ≠ p then (1 : ℝ) else 0) := by
      intro xi
      by_cases h : xi = (p, 0)
      · subst h; simp
      · by_cases h1 : xi.1 = p <;> simp [h, h1]
    rw [Finset.sum_congr rfl (fun xi _ => hsplit xi), Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_ite_eq' univ (p, 0) (fun _ => (N : ℝ) ^ 2)]; simp
    · rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, card_fst_ne]
      simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero, Nat.cast_mul]
      rw [Nat.cast_sub hS, Nat.cast_one]
  rw [Finset.sum_congr rfl (fun p _ => hp p), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

omit [NeZero N] in
/-- The ordinary diagonal mass of the flat envelope is `S² · N`. -/
theorem common_envelope_diagonal :
    (∑ _p : Fin S, ∑ _x : Fin S × Fin N, ‖flatV (S := S) (N := N) _p _x‖ ^ 2)
      = (S : ℝ) ^ 2 * (N : ℝ) := by
  simp [flatV, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Common-envelope normalization countermodel.**  With completely common
amplitudes and pair-collision multiplicity `≤ 1`, the off-diagonal collision
energy is exactly `S · N · (N - 1)`, while the diagonal mass is `S² · N`. -/
theorem common_envelope_not_diagonal_saving :
    collisionEnergy (P := Fin S) (X := Fin S × Fin N) (E := ℂ)
        (Xi := fun _ => Fin S × Fin N) flatV blockPr
      - (∑ _p : Fin S, ∑ _x : Fin S × Fin N, ‖flatV (S := S) (N := N) _p _x‖ ^ 2)
      = (S : ℝ) * (N : ℝ) * ((N : ℝ) - 1) := by
  rw [common_envelope_energy, common_envelope_diagonal]
  ring

omit [NeZero N] in
/-- The conservative ℓ¹ scale of the flat envelope is `S · (S N)²`.  This is why
an `S⁻¹` gain relative to the absolute scale `T_abs` is not the same as an
`S⁻¹` gain relative to the diagonal/TF4 scale `S² N`. -/
theorem absolute_scale_vs_diagonal_scale_example :
    TAbs (P := Fin S) (X := Fin S × Fin N) (E := ℂ) flatV
      = (S : ℝ) * ((S : ℝ) * (N : ℝ)) ^ 2 := by
  simp [TAbs, flatV, Finset.sum_const, nsmul_eq_mul]

/-- Numerical witness: at `S = N = 4` the off-diagonal collision energy is
`4·4·3 = 48`, which exceeds `S⁻¹` times the diagonal mass `16·4/4 = 16`.
So "common envelope ⇒ `S⁻¹` diagonal saving" is false. -/
theorem common_envelope_refutes_diagonal_saving :
    ¬ (∀ S N : ℕ, 0 < S → 0 < N →
        (S : ℝ) * (N : ℝ) * ((N : ℝ) - 1)
          ≤ (S : ℝ)⁻¹ * ((S : ℝ) ^ 2 * (N : ℝ))) := by
  intro h
  have h4 := h 4 4 (by norm_num) (by norm_num)
  norm_num at h4

end Countermodel

end Gate1A
