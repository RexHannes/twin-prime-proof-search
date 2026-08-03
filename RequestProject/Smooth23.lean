import Mathlib
import RequestProject.Defs

/-!
# The (2,3)-Smooth Case: Reciprocal Identities

We formalize key structural results about reciprocal identities among
(2,3)-smooth integers (integers whose prime factors are only 2 and 3).

## Main results

1. Classification of support-3 identities (Type I and Type II)
2. The proposed "diamond identity" is false
3. No axis-aligned rectangle in the exponent lattice produces an identity
4. Explicit primitive identities of large support (disproving bounded support)
-/

open scoped BigOperators

/-! ## 1. Support-3 Identity Classification

Every support-3 reciprocal identity among (2,3)-smooth integers belongs to one of
three families (up to reordering LHS terms):

- **Type I** (based on `1 + 2 = 3`):
  `1/(2^(a-1)·3^b) + 1/(2^a·3^b) = 1/(2^a·3^(b-1))` for `a ≥ 1, b ≥ 1`.

- **Type II** (based on `1 + 3 = 4`):
  `1/(2^a·3^(b-1)) + 1/(2^a·3^b) = 1/(2^(a-2)·3^b)` for `a ≥ 2, b ≥ 1`.

- **Type III** (based on `1 + 8 = 9`):
  `1/(2^a·3^b) + 1/(2^(a-3)·3^b) = 1/(2^a·3^(b-2))` for `a ≥ 3, b ≥ 2`.

Completeness of this classification follows from the `{2,3}` S-unit equation,
which has coprime solutions `{1+1=2, 1+2=3, 1+3=4, 1+8=9}` only.
The `1+1=2` case requires equal denominators and does not produce a support-3
identity with *distinct* elements.

**Note:** The completeness claim is NOT Lean-proved; only the three families
are verified as valid identities. Completeness would require formalizing
the S-unit equation for `{2,3}`.
-/

/-
**Type I identity** (based on `3 = 2 + 1`):
    `1/(2^(a-1)·3^b) + 1/(2^a·3^b) = 1/(2^a·3^(b-1))` for `a ≥ 1, b ≥ 1`.
-/
theorem smooth23_typeI_identity (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : ℚ) / (2 ^ (a - 1) * 3 ^ b) + 1 / (2 ^ a * 3 ^ b) =
    1 / (2 ^ a * 3 ^ (b - 1)) := by
      cases a <;> cases b <;> norm_num [ pow_succ' ] at * ; linarith

/-
**Type II identity** (based on `4 = 3 + 1`):
    `1/(2^a·3^(b-1)) + 1/(2^a·3^b) = 1/(2^(a-2)·3^b)` for `a ≥ 2, b ≥ 1`.
-/
theorem smooth23_typeII_identity (a b : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (1 : ℚ) / (2 ^ a * 3 ^ (b - 1)) + 1 / (2 ^ a * 3 ^ b) =
    1 / (2 ^ (a - 2) * 3 ^ b) := by
      rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> norm_num [ pow_succ', ← mul_assoc, Nat.succ_eq_add_one ] at *; all_goals ring!

/-
**Type III identity** (based on `1 + 8 = 9`):
    `1/(2^a·3^b) + 1/(2^(a-3)·3^b) = 1/(2^a·3^(b-2))` for `a ≥ 3, b ≥ 2`.
-/
theorem smooth23_typeIII_identity (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) :
    (1 : ℚ) / (2 ^ a * 3 ^ b) + 1 / (2 ^ (a - 3) * 3 ^ b) =
    1 / (2 ^ a * 3 ^ (b - 2)) := by
  rcases a with ( _ | _ | _ | a ) <;> rcases b with ( _ | _ | _ | b ) <;> norm_num at * ; ring_nf at *;
  · norm_num ; ring;
  · grind

-- Concrete instance of Type III: 1/72 + 1/9 = 1/8
example : (1 : ℚ) / 72 + 1 / 9 = 1 / 8 := by norm_num
-- Another instance: a=4, b=3: 1/432 + 1/54 = 1/48
example : (1 : ℚ) / 432 + 1 / 54 = 1 / 48 := by norm_num

/-! ## 2. The Diamond Identity is False -/

/-- The proposed diamond identity
    `1/(2^a·3^b) + 1/(2^(a+2)·3^(b+2)) = 1/(2^(a+1)·3^b) + 1/(2^a·3^(b+1))`
    is **false** for all `a, b`. We disprove the case `a = 0, b = 0`. -/
theorem diamond_identity_false :
    ¬ ((1 : ℚ) / (2 ^ 0 * 3 ^ 0) + 1 / (2 ^ 2 * 3 ^ 2) =
       1 / (2 ^ 1 * 3 ^ 0) + 1 / (2 ^ 0 * 3 ^ 1)) := by
  norm_num

/-! ## 3. No Axis-Aligned Rectangle Identity -/

/-
No axis-aligned rectangle in the `(v₂, v₃)` exponent lattice produces a
    valid 2+2 reciprocal identity. The diagonal pairing always fails because
    `(2^α - 1)(3^β - 1) ≠ 0` for `α, β ≥ 1`.

    Formally: `1/(2^a·3^b) + 1/(2^(a+α)·3^(b+β)) ≠ 1/(2^(a+α)·3^b) + 1/(2^a·3^(b+β))`
    for `α ≥ 1, β ≥ 1`.
-/
theorem no_rectangle_identity (a b α β : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    (1 : ℚ) / (2 ^ a * 3 ^ b) + 1 / (2 ^ (a + α) * 3 ^ (b + β)) ≠
    1 / (2 ^ (a + α) * 3 ^ b) + 1 / (2 ^ a * 3 ^ (b + β)) := by
      -- Assume `α ≥ 1` and `β ≥ 1`. We want to show `1/(2^a·3^b) + 1/(2^(a+α)·3^(b+β)) ≠ 1/(2^(a+α)·3^b) + 1/(2^a·3^(b+β))`.
      field_simp at *; ring_nf at *; norm_num at *; (
      field_simp;
      exact mod_cast ( by nlinarith [ pow_le_pow_right₀ ( show 1 ≤ 2 by norm_num ) hα, pow_le_pow_right₀ ( show 1 ≤ 3 by norm_num ) hβ ] ) ;);

/-! ## 4. Concrete Identity Verifications -/

-- Concrete instances of support-3 identities
-- Type I: 1/3 + 1/6 = 1/2
example : (1 : ℚ) / 3 + 1 / 6 = 1 / 2 := by norm_num
-- Type I: 1/6 + 1/12 = 1/4
example : (1 : ℚ) / 6 + 1 / 12 = 1 / 4 := by norm_num
-- Type II: 1/4 + 1/12 = 1/3
example : (1 : ℚ) / 4 + 1 / 12 = 1 / 3 := by norm_num
-- Type II: 1/8 + 1/24 = 1/6
example : (1 : ℚ) / 8 + 1 / 24 = 1 / 6 := by norm_num

/-! ## 5. Explicit Large Primitive Identity (Disproving Bounded Support) -/

/-- Support-12 primitive identity:
    `1/1 + 1/18 + 1/72 + 1/216 = 1/2 + 1/6 + 1/8 + 1/9 + 1/12 + 1/24 + 1/27 + 1/108`.
    Both sides equal `29/27`. -/
theorem support12_identity :
    (1 : ℚ) / 1 + 1 / 18 + 1 / 72 + 1 / 216 =
    1 / 2 + 1 / 6 + 1 / 8 + 1 / 9 + 1 / 12 + 1 / 24 + 1 / 27 + 1 / 108 := by
  norm_num

/-- Support-12 unbalanced primitive identity:
    `1 = 1/2 + 1/6 + 1/8 + 1/18 + 1/24 + 1/27 + 1/36 + 1/54 + 1/72 + 1/108 + 1/216`.
    The RHS sums to 1. -/
theorem support12_unbalanced_identity :
    (1 : ℚ) = 1 / 2 + 1 / 6 + 1 / 8 + 1 / 18 + 1 / 24 + 1 / 27 +
              1 / 36 + 1 / 54 + 1 / 72 + 1 / 108 + 1 / 216 := by
  grind

/-- The identity `1/4 + 1/6 = 1/3 + 1/12` is the simplest support-4
    primitive identity. -/
theorem support4_identity : (1 : ℚ) / 4 + 1 / 6 = 1 / 3 + 1 / 12 := by
  norm_num