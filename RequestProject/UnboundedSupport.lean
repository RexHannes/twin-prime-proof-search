import Mathlib

/-!
# Unbounded Primitive Support for (2,3)-Smooth Reciprocal Identities

## Main result

We construct an explicit infinite family of primitive reciprocal identities
among distinct (2,3)-smooth composite integers with support `3 + 2t` for each `t ≥ 0`.
This disproves the naive conjecture that primitive support is bounded.

## Construction

The **core local refinement identity** is:
  `1/n = 1/(2n) + 1/(3n) + 1/(6n)`    for any nonzero `n`.

Starting from the base identity `1/6 = 1/8 + 1/24`, we define a family of
denominator sets `B_t` by repeatedly applying the refinement to the frontier
element:

- `B_0 = {8, 24}`
- `B_{t+1}` = `B_t` with frontier `24·6^t` replaced by `{48·6^t, 72·6^t, 24·6^{t+1}}`

Equivalently, `B_t = {8} ∪ {48·6^i : i < t} ∪ {72·6^i : i < t} ∪ {24·6^t}`.

The identity `{6}` vs `B_t` has:
- all elements distinct, (2,3)-smooth, and composite
- reciprocal sum = 1/6
- total support = 1 + |B_t| = 3 + 2t → ∞
- primitive (all RHS terms positive, so no proper subset achieves 1/6)
-/

open Finset BigOperators

/-! ## 1. The Core Local Refinement Identity -/

/-- For any nonzero `n : ℚ`, we have `1/n = 1/(2n) + 1/(3n) + 1/(6n)`. -/
theorem refinement_identity (n : ℚ) (hn : n ≠ 0) :
    1 / n = 1 / (2 * n) + 1 / (3 * n) + 1 / (6 * n) := by
  field_simp; ring

/-! ## 2. The Chain Sum Equals 1/6

We define the reciprocal sum of `B_t` and prove it equals `1/6` for all `t`.
-/

/-- The reciprocal sum of the `B_t` denominator family:
    `chainSum t = 1/8 + Σ_{i<t} (1/(48·6^i) + 1/(72·6^i)) + 1/(24·6^t)`. -/
noncomputable def chainSum (t : ℕ) : ℚ :=
  1 / 8 + ∑ i ∈ Finset.range t, (1 / (48 * (6 : ℚ) ^ i) + 1 / (72 * (6 : ℚ) ^ i)) +
  1 / (24 * (6 : ℚ) ^ t)

/-- Base case: `chainSum 0 = 1/6`. -/
theorem chainSum_zero : chainSum 0 = 1 / 6 := by
  simp [chainSum]
  norm_num

/-
Key step: applying the refinement identity to the frontier element shows
    `chainSum (t+1) = chainSum t`.
-/
theorem chainSum_succ (t : ℕ) : chainSum (t + 1) = chainSum t := by
  unfold chainSum; norm_num [ pow_succ, Finset.sum_range_succ ] ; ring;

/-- The chain sum equals `1/6` for all `t ≥ 0`. -/
theorem chainSum_eq_sixth (t : ℕ) : chainSum t = 1 / 6 := by
  induction t with
  | zero => exact chainSum_zero
  | succ t ih => rw [chainSum_succ, ih]

/-! ## 3. Primitivity via Positivity

The identity `{6}` vs `B_t` is primitive because all reciprocals `1/q` for `q ∈ B_t`
are positive. Any proper nonempty subset of `B_t` has reciprocal sum strictly less
than `1/6`, so the only way to achieve `R(A) = R(B)` with `A ⊆ {6}`, `B ⊆ B_t` is
the full pair `({6}, B_t)`.
-/

/-
If `f` is positive on a finite set `S`, then any proper subset has strictly
    smaller sum. This is the key to primitivity.
-/
theorem Finset.sum_lt_of_proper_subset {ι : Type*} [DecidableEq ι]
    {S T : Finset ι} {f : ι → ℚ}
    (hpos : ∀ i ∈ S, 0 < f i)
    (hT : T ⊆ S) (hproper : T ≠ S) :
    ∑ i ∈ T, f i < ∑ i ∈ S, f i := by
  rw [ ← Finset.sum_sdiff hT ];
  exact lt_add_of_pos_left _ ( Finset.sum_pos ( fun i hi => hpos i ( Finset.mem_sdiff.mp hi |>.1 ) ) ( Finset.nonempty_of_ne_empty ( by contrapose! hproper; aesop ) ) )

/-! ## 4. Concrete Instances of the Family

We verify the identity `1/6 = Σ_{q ∈ B_t} 1/q` for `t = 0, 1, 2, 3, 4, 5`. -/

/-- `t = 0`: `B_0 = {8, 24}`, support 3. -/
theorem family_t0 : (1 : ℚ) / 6 = 1 / 8 + 1 / 24 := by norm_num

/-- `t = 1`: `B_1 = {8, 48, 72, 144}`, support 5. -/
theorem family_t1 : (1 : ℚ) / 6 = 1 / 8 + 1 / 48 + 1 / 72 + 1 / 144 := by norm_num

/-- `t = 2`: `B_2 = {8, 48, 72, 288, 432, 864}`, support 7. -/
theorem family_t2 :
    (1 : ℚ) / 6 = 1 / 8 + 1 / 48 + 1 / 72 + 1 / 288 + 1 / 432 + 1 / 864 := by norm_num

/-- `t = 3`: `B_3 = {8, 48, 72, 288, 432, 1728, 2592, 5184}`, support 9. -/
theorem family_t3 :
    (1 : ℚ) / 6 = 1 / 8 + 1 / 48 + 1 / 72 + 1 / 288 + 1 / 432 +
    1 / 1728 + 1 / 2592 + 1 / 5184 := by norm_num

/-- `t = 4`: `B_4 = {8, 48, 72, 288, 432, 1728, 2592, 10368, 15552, 31104}`, support 11. -/
theorem family_t4 :
    (1 : ℚ) / 6 = 1 / 8 + 1 / 48 + 1 / 72 + 1 / 288 + 1 / 432 +
    1 / 1728 + 1 / 2592 + 1 / 10368 + 1 / 15552 + 1 / 31104 := by norm_num

/-- `t = 5`: support 13. -/
theorem family_t5 :
    (1 : ℚ) / 6 = 1 / 8 + 1 / 48 + 1 / 72 + 1 / 288 + 1 / 432 +
    1 / 1728 + 1 / 2592 + 1 / 10368 + 1 / 15552 +
    1 / 62208 + 1 / 93312 + 1 / 186624 := by norm_num

/-! ## 5. Smoothness: All Elements Are (2,3)-Smooth

Every element of `B_t` is a product of powers of 2 and 3 only:
- `8 = 2³`
- `48 · 6^i = 2^{4+i} · 3^{1+i}`
- `72 · 6^i = 2^{3+i} · 3^{2+i}`
- `24 · 6^t = 2^{3+t} · 3^{1+t}`
-/

/-
`48 · 6^i = 2^(4+i) · 3^(1+i)`
-/
theorem factorization_48_6pow (i : ℕ) : 48 * 6 ^ i = 2 ^ (4 + i) * 3 ^ (1 + i) := by
  ring;
  norm_num [ ← mul_pow ]

/-
`72 · 6^i = 2^(3+i) · 3^(2+i)`
-/
theorem factorization_72_6pow (i : ℕ) : 72 * 6 ^ i = 2 ^ (3 + i) * 3 ^ (2 + i) := by
  ring_nf;
  norm_num [ ← mul_pow ]

/-
`24 · 6^t = 2^(3+t) · 3^(1+t)`
-/
theorem factorization_24_6pow (t : ℕ) : 24 * 6 ^ t = 2 ^ (3 + t) * 3 ^ (1 + t) := by
  ring_nf;
  norm_num [ ← mul_pow ]

/-- `8 = 2^3 · 3^0` -/
theorem factorization_8 : 8 = 2 ^ 3 * 3 ^ 0 := by norm_num

/-! ## 6. Compositeness: All Elements Are Composite

Every element of `B_t` is ≥ 8 and has a nontrivial factorization, hence is composite. -/

/-
All elements `48 · 6^i` are composite (= 2 · (24 · 6^i)).
-/
theorem composite_48_6pow (i : ℕ) : ¬ Nat.Prime (48 * 6 ^ i) := by
  norm_num [ Nat.prime_mul_iff ]

/-
All elements `72 · 6^i` are composite (= 2 · (36 · 6^i)).
-/
theorem composite_72_6pow (i : ℕ) : ¬ Nat.Prime (72 * 6 ^ i) := by
  norm_num [ Nat.prime_mul_iff ]

/-
All elements `24 · 6^t` are composite.
-/
theorem composite_24_6pow (t : ℕ) : ¬ Nat.Prime (24 * 6 ^ t) := by
  norm_num [ Nat.prime_mul_iff ]

/-- `8` is composite. -/
theorem composite_8 : ¬ Nat.Prime 8 := by decide

/-! ## 7. Cardinality of `B_t`

The set `B_t` has exactly `2 + 2t` elements. We verify for small cases. -/

example : ({8, 24} : Finset ℕ).card = 2 := by decide
example : ({8, 48, 72, 144} : Finset ℕ).card = 4 := by decide
example : ({8, 48, 72, 288, 432, 864} : Finset ℕ).card = 6 := by decide
example : ({8, 48, 72, 288, 432, 1728, 2592, 5184} : Finset ℕ).card = 8 := by decide

/-! ## 8. Formal Definition of B_t and Cardinality -/

/-- The denominator set `B_t` as a Finset.
    `B_t = {8} ∪ {48·6^i : i < t} ∪ {72·6^i : i < t} ∪ {24·6^t}`. -/
def Bt (t : ℕ) : Finset ℕ :=
  {8} ∪ ((Finset.range t).biUnion (fun i => {48 * 6 ^ i, 72 * 6 ^ i})) ∪ {24 * 6 ^ t}

/-- `48 * 6^i ≥ 48` for all `i`. -/
theorem le_48_mul_6pow (i : ℕ) : 48 ≤ 48 * 6 ^ i := Nat.le_mul_of_pos_right 48 (Nat.pos_of_ne_zero (by positivity))

/-- `72 * 6^i ≥ 72` for all `i`. -/
theorem le_72_mul_6pow (i : ℕ) : 72 ≤ 72 * 6 ^ i := Nat.le_mul_of_pos_right 72 (Nat.pos_of_ne_zero (by positivity))

/-- `24 * 6^t ≥ 24` for all `t`. -/
theorem le_24_mul_6pow (t : ℕ) : 24 ≤ 24 * 6 ^ t := Nat.le_mul_of_pos_right 24 (Nat.pos_of_ne_zero (by positivity))

/-
Key distinctness: `48 * 6^i ≠ 72 * 6^j` for all `i, j`.
-/
theorem ne_48_72_6pow (i j : ℕ) : 48 * 6 ^ i ≠ 72 * 6 ^ j := by
  intro h; have := congr_arg ( · % 5 ) h; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;

/-
`24 * 6^t ≠ 48 * 6^i` when `i < t`.
-/
theorem ne_24_48_6pow {t i : ℕ} (hi : i < t) : 24 * 6 ^ t ≠ 48 * 6 ^ i := by
  by_contra h_eq;
  have h_div : 6 ^ (t - i) = 2 := by
    exact mul_left_cancel₀ ( pow_ne_zero i ( by decide : ( 6 : ℕ ) ≠ 0 ) ) ( by rw [ ← pow_add, Nat.add_sub_of_le hi.le ] ; linarith );
  linarith [ Nat.pow_le_pow_right ( show 1 ≤ 6 by norm_num ) ( show t - i ≥ 1 by exact Nat.sub_pos_of_lt hi ) ]

/-
`24 * 6^t ≠ 72 * 6^i` when `i < t`.
-/
theorem ne_24_72_6pow {t i : ℕ} (hi : i < t) : 24 * 6 ^ t ≠ 72 * 6 ^ i := by
  by_cases h : t - i ≥ 2;
  · exact ne_of_gt ( by rw [ show 6 ^ t = 6 ^ i * 6 ^ ( t - i ) by rw [ ← pow_add, Nat.add_sub_of_le hi.le ] ] ; nlinarith [ pow_pos ( show 0 < 6 by decide ) i, pow_le_pow_right₀ ( show 1 ≤ 6 by decide ) h ] );
  · rw [ show t = i + 1 by omega ] ; ring_nf; norm_num;

/-
The card of `B_t` is `2 + 2*t`.
-/
theorem Bt_card_eq (t : ℕ) : (Bt t).card = 2 + 2 * t := by
  unfold Bt;
  rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> norm_num;
  · rw [ Finset.card_biUnion ] <;> norm_num [ Finset.disjoint_left ] ; ring;
    intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
    grind +suggestions;
  · grind;
  · exact ⟨ by linarith [ pow_pos ( by decide : 0 < 6 ) t ], fun x hx => ⟨ fun h => by have := ne_24_48_6pow hx; aesop, fun h => by have := ne_24_72_6pow hx; aesop ⟩ ⟩

/-
For every `m`, there exists `t` such that `|B_t| ≥ m`.
-/
theorem Bt_card_unbounded : ∀ m : ℕ, ∃ t : ℕ, m ≤ (Bt t).card := by
  intro m;
  exact ⟨ m, by linarith [ Bt_card_eq m ] ⟩

/-
The identity support (counting `{6}` on the LHS plus `B_t` on the RHS)
    grows without bound. Combined with `chainSum_eq_sixth`, this shows
    primitive reciprocal identity support is unbounded.
-/
theorem support_unbounded_with_identity :
    ∀ m : ℕ, ∃ t : ℕ, m ≤ 1 + (Bt t).card ∧ chainSum t = 1 / 6 := by
  exact fun m => ⟨ m, by linarith [ Bt_card_eq m ], chainSum_eq_sixth m ⟩

/-! ## 9. Summary: Unbounded Primitive Support

**Theorem** (informal, supported by the formal results above):
For every `t ≥ 0`, the identity `{6} vs B_t` is a primitive reciprocal identity
among distinct (2,3)-smooth composite integers with total support `3 + 2t`.
Since `3 + 2t → ∞`, primitive support is unbounded.

**Key distinction:**
- **FALSE claim:** Primitive (2,3)-smooth identities have bounded support.
- **STILL PLAUSIBLE:** Large primitive identities are generated by bounded-support
  local refinement moves (the `1/n → 1/(2n) + 1/(3n) + 1/(6n)` identity has support 4).
  The entropy/BSRCC approach should target this local generation structure, not
  bounded primitive circuit size.
-/