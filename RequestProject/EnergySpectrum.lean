import Mathlib

/-!
# Energy Spectrum Decomposition for Reciprocal Subset-Sum Collisions

## Overview

We formalize the exact counting identity that decomposes subset-sum collisions
into contributions from signed kernel vectors, weighted by `2^(k - ‖v‖₁)`.

For a list of denominators `q : Fin k → ℕ` (all nonzero), we define:
- Subset vectors `x : Fin k → Bool`
- Subset reciprocal sum `subsetRecipSum q x = Σ_i (if x i then 1/(q i) else 0)`
- Signed difference type `Sign3` with values `neg, zero, pos`
- `diffSign : Bool → Bool → Sign3` recording the signed difference `x - y`
- Signed reciprocal sum `signedRecipSum q v = Σ_i (signToRat (v i)) / (q i)`
- Support `sign3Support v = #{i : v i ≠ zero}`
- Zero count `sign3ZeroCount v = #{i : v i = zero}`

## Main results

1. **Collision ↔ Kernel**: `subsetRecipSum q x = subsetRecipSum q y` iff
   `signedRecipSum q (fun i => diffSign (x i) (y i)) = 0`.

2. **Fiber cardinality**: For fixed `v : Fin k → Sign3`, the number of pairs
   `(x, y)` with `diffSign (x i) (y i) = v i` for all `i` is `2^(zeroCount v)`.

3. **Zero + support = k**: `sign3ZeroCount v + sign3Support v = k`.
-/

open Finset BigOperators Fintype

/-! ## 1. The Sign3 Type -/

/-- Three-valued sign type for signed difference vectors. -/
inductive Sign3 where
  | neg  : Sign3
  | zero : Sign3
  | pos  : Sign3
  deriving DecidableEq, Fintype, Repr

namespace Sign3

instance : Inhabited Sign3 := ⟨Sign3.zero⟩

/-- Map `Sign3` to `ℤ`. -/
def toInt : Sign3 → ℤ
  | neg  => -1
  | zero => 0
  | pos  => 1

/-- Map `Sign3` to `ℚ`. -/
def toRat : Sign3 → ℚ
  | neg  => -1
  | zero => 0
  | pos  => 1

theorem toRat_neg : Sign3.neg.toRat = -1 := rfl
theorem toRat_zero : Sign3.zero.toRat = 0 := rfl
theorem toRat_pos : Sign3.pos.toRat = 1 := rfl

theorem toRat_eq_zero_iff (s : Sign3) : s.toRat = 0 ↔ s = zero := by
  cases s <;> simp [toRat]

theorem toRat_ne_zero_iff (s : Sign3) : s.toRat ≠ 0 ↔ s ≠ zero := by
  cases s <;> simp [toRat]

end Sign3

/-! ## 2. Difference of Booleans -/

/-- The signed difference of two booleans:
    `(true, false) ↦ pos`, `(false, true) ↦ neg`, equal values ↦ `zero`. -/
def diffSign : Bool → Bool → Sign3
  | true,  false => Sign3.pos
  | false, true  => Sign3.neg
  | true,  true  => Sign3.zero
  | false, false => Sign3.zero

@[simp] theorem diffSign_tt : diffSign true true = Sign3.zero := rfl
@[simp] theorem diffSign_ff : diffSign false false = Sign3.zero := rfl
@[simp] theorem diffSign_tf : diffSign true false = Sign3.pos := rfl
@[simp] theorem diffSign_ft : diffSign false true = Sign3.neg := rfl

/-- `diffSign x y = zero` iff `x = y`. -/
theorem diffSign_eq_zero_iff (x y : Bool) : diffSign x y = Sign3.zero ↔ x = y := by
  cases x <;> cases y <;> simp [diffSign]

/-- `diffSign x y ≠ zero` iff `x ≠ y`. -/
theorem diffSign_ne_zero_iff (x y : Bool) : diffSign x y ≠ Sign3.zero ↔ x ≠ y := by
  rw [ne_eq, diffSign_eq_zero_iff]

/-- For each `Sign3` value `s`, there is exactly one pair `(x,y)` with `diffSign x y = s`
    when `s ≠ zero`, and exactly two pairs when `s = zero`. -/
theorem diffSign_fiber_neg : {p : Bool × Bool | diffSign p.1 p.2 = Sign3.neg} = {(false, true)} := by
  ext ⟨x, y⟩; cases x <;> cases y <;> simp [diffSign]

theorem diffSign_fiber_pos : {p : Bool × Bool | diffSign p.1 p.2 = Sign3.pos} = {(true, false)} := by
  ext ⟨x, y⟩; cases x <;> cases y <;> simp [diffSign]

theorem diffSign_fiber_zero :
    {p : Bool × Bool | diffSign p.1 p.2 = Sign3.zero} = {(false, false), (true, true)} := by
  ext ⟨x, y⟩; cases x <;> cases y <;> simp [diffSign]

/-! ## 3. Subset Reciprocal Sum -/

/-- The reciprocal sum of a subset encoded by a boolean vector.
    `subsetRecipSum q x = Σ_i (if x i then 1/(q i) else 0)`. -/
noncomputable def subsetRecipSum (k : ℕ) (q : Fin k → ℕ) (x : Fin k → Bool) : ℚ :=
  ∑ i : Fin k, if x i then (1 : ℚ) / (q i : ℚ) else 0

/-! ## 4. Signed Reciprocal Sum -/

/-- The signed reciprocal sum for a signed vector.
    `signedRecipSum q v = Σ_i (v i).toRat / (q i)`. -/
noncomputable def signedRecipSum (k : ℕ) (q : Fin k → ℕ) (v : Fin k → Sign3) : ℚ :=
  ∑ i : Fin k, (v i).toRat / (q i : ℚ)

/-! ## 5. Support and Zero Count -/

/-- The support (L¹ norm) of a signed vector: the number of nonzero entries. -/
def sign3Support (k : ℕ) (v : Fin k → Sign3) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ Sign3.zero)).card

/-- The zero count: the number of zero entries. -/
def sign3ZeroCount (k : ℕ) (v : Fin k → Sign3) : ℕ :=
  (Finset.univ.filter (fun i => v i = Sign3.zero)).card

/-
Zero count + support = k.
-/
theorem sign3ZeroCount_add_support (k : ℕ) (v : Fin k → Sign3) :
    sign3ZeroCount k v + sign3Support k v = k := by
  convert Finset.card_add_card_compl ( Finset.filter ( fun i => v i = Sign3.zero ) Finset.univ ) using 1;
  · unfold sign3ZeroCount sign3Support; aesop;
  · norm_num

/-! ## 6. Collision ↔ Kernel Condition -/

/-- The boolean-to-rational value: `boolToRat true = 1`, `boolToRat false = 0`. -/
def boolToRat : Bool → ℚ
  | true  => 1
  | false => 0

@[simp] theorem boolToRat_true : boolToRat true = 1 := rfl
@[simp] theorem boolToRat_false : boolToRat false = 0 := rfl

/-
Key identity: `boolToRat x - boolToRat y = (diffSign x y).toRat`.
-/
theorem boolToRat_sub_eq_toRat (x y : Bool) :
    boolToRat x - boolToRat y = (diffSign x y).toRat := by
  cases x <;> cases y <;> simp [boolToRat, diffSign, Sign3.toRat]

/-
Collision condition equals kernel condition (forward direction):
    If `subsetRecipSum q x = subsetRecipSum q y`, then
    `signedRecipSum q (fun i => diffSign (x i) (y i)) = 0`.
-/
theorem collision_implies_kernel {k : ℕ} (q : Fin k → ℕ) (hq : ∀ i, q i ≠ 0)
    (x y : Fin k → Bool)
    (h : subsetRecipSum k q x = subsetRecipSum k q y) :
    signedRecipSum k q (fun i => diffSign (x i) (y i)) = 0 := by
  unfold signedRecipSum subsetRecipSum at *;
  convert sub_eq_zero.mpr h using 1;
  rw [ ← Finset.sum_sub_distrib ] ; congr ; ext i ; rcases x_i : x i with ( _ | _ ) <;> rcases y_i : y i with ( _ | _ ) <;> simp +decide [ *, div_eq_mul_inv ] ; ring;
  exact show ( -1 : ℚ ) * ( q i : ℚ ) ⁻¹ = - ( q i : ℚ ) ⁻¹ by ring;

/-
Collision condition equals kernel condition (backward direction):
    If `signedRecipSum q (fun i => diffSign (x i) (y i)) = 0`, then
    `subsetRecipSum q x = subsetRecipSum q y`.
-/
theorem kernel_implies_collision {k : ℕ} (q : Fin k → ℕ) (hq : ∀ i, q i ≠ 0)
    (x y : Fin k → Bool)
    (h : signedRecipSum k q (fun i => diffSign (x i) (y i)) = 0) :
    subsetRecipSum k q x = subsetRecipSum k q y := by
  -- By definition of signedRecipSum and subsetRecipSum, we can rewrite the signedRecipSum in terms of the subsetRecipSum.
  have h_rewrite : ∑ i : Fin k, (diffSign (x i) (y i)).toRat / (q i : ℚ) = ∑ i : Fin k, (if x i then (1 : ℚ) / (q i : ℚ) else 0) - ∑ i : Fin k, (if y i then (1 : ℚ) / (q i : ℚ) else 0) := by
    rw [ ← Finset.sum_sub_distrib ] ; congr ; ext i ; rcases x i with ( _ | _ | _ | _ ) <;> rcases y i with ( _ | _ | _ | _ ) <;> simp +decide [ * ] ; ring;
    · exact show ( -1 : ℚ ) * ( q i : ℚ ) ⁻¹ = - ( q i : ℚ ) ⁻¹ by ring;
    · erw [ div_eq_iff ] <;> norm_cast ; aesop;
      exact hq i;
  exact eq_of_sub_eq_zero ( h_rewrite.symm.trans h )

/-- Collision ↔ kernel condition (biconditional). -/
theorem collision_iff_kernel {k : ℕ} (q : Fin k → ℕ) (hq : ∀ i, q i ≠ 0)
    (x y : Fin k → Bool) :
    subsetRecipSum k q x = subsetRecipSum k q y ↔
    signedRecipSum k q (fun i => diffSign (x i) (y i)) = 0 :=
  ⟨collision_implies_kernel q hq x y, kernel_implies_collision q hq x y⟩

/-! ## 7. Fiber of a Signed Vector -/

/-- The fiber of a signed vector `v`: the set of ordered pairs `(x, y)` of boolean
    vectors such that `diffSign (x i) (y i) = v i` for all `i`. -/
def sign3Fiber (k : ℕ) (v : Fin k → Sign3) :
    Finset ((Fin k → Bool) × (Fin k → Bool)) :=
  Finset.univ.filter (fun p => ∀ i, diffSign (p.1 i) (p.2 i) = v i)

/-
The fiber cardinality equals `2^(zeroCount v)`.
-/
theorem sign3Fiber_card (k : ℕ) (v : Fin k → Sign3) :
    (sign3Fiber k v).card = 2 ^ (sign3ZeroCount k v) := by
  induction' k with k ih <;> simp_all +decide [ sign3ZeroCount ];
  · decide +revert;
  · convert congr_arg₂ ( · * · ) ( ih ( fun i => v i.succ ) ) ( show # ( Finset.filter ( fun p : Bool × Bool => diffSign p.1 p.2 = v 0 ) Finset.univ ) = 2 ^ ( if v 0 = Sign3.zero then 1 else 0 ) from ?_ ) using 1;
    · rw [ ← Finset.card_product ];
      refine' Finset.card_bij ( fun p hp => ( ( fun i => p.1 i.succ, fun i => p.2 i.succ ), ( p.1 0, p.2 0 ) ) ) _ _ _ <;> simp +decide [ sign3Fiber ];
      · exact fun a b h => ⟨ fun i => h _, h _ ⟩;
      · intro a b hab a' b' hab' ha hb ha' hb'; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
      · intro a b; refine' ⟨ _, _, _ ⟩;
        · constructor <;> intro h₁ h₂ <;> use Fin.cons ( if v 0 = Sign3.zero then false else false ) a, Fin.cons ( if v 0 = Sign3.zero then false else true ) b <;> simp_all +decide [ Fin.forall_fin_succ ];
          simp +decide [ ← h₂ ];
        · intro h1 h2; use Fin.cons true a, Fin.cons false b; simp_all +decide [ Fin.forall_fin_succ ] ;
        · intro h1 h2; use Fin.cons true a, Fin.cons true b; simp_all +decide [ Fin.forall_fin_succ ] ;
    · rw [ ← pow_add, Finset.card_filter, Finset.card_filter ];
      rw [ Fin.sum_univ_succ, add_comm ];
    · cases v 0 <;> simp +decide

/-! ## 8. Unique Signed Difference -/

/-
Every pair `(x, y)` lies in exactly one fiber — the fiber of its difference vector.
-/
theorem mem_sign3Fiber_diff (k : ℕ) (x y : Fin k → Bool) :
    (x, y) ∈ sign3Fiber k (fun i => diffSign (x i) (y i)) := by
  exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, fun i => rfl ⟩

/-
The fibers partition the set of all ordered pairs.
-/
theorem sign3Fiber_disjoint (k : ℕ) (v w : Fin k → Sign3) (hvw : v ≠ w) :
    Disjoint (sign3Fiber k v) (sign3Fiber k w) := by
  rw [ Finset.disjoint_left ];
  contrapose! hvw; unfold sign3Fiber at *; aesop;

/-
The union of all fibers is the full set.
-/
theorem sign3Fiber_biUnion (k : ℕ) :
    Finset.univ.biUnion (fun v : Fin k → Sign3 => sign3Fiber k v) =
    (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))) := by
  ext ⟨x, y⟩; simp [sign3Fiber];
  exact ⟨ _, fun i => rfl ⟩

/-! ## 9. Exact Collision Count Formula -/

/-- The kernel: the set of signed vectors `v` with `signedRecipSum q v = 0`. -/
noncomputable def signedKernel (k : ℕ) (q : Fin k → ℕ) : Finset (Fin k → Sign3) :=
  Finset.univ.filter (fun v => signedRecipSum k q v = 0)

/-- The set of collision pairs. -/
noncomputable def collisionPairs (k : ℕ) (q : Fin k → ℕ) :
    Finset ((Fin k → Bool) × (Fin k → Bool)) :=
  Finset.univ.filter (fun p => subsetRecipSum k q p.1 = subsetRecipSum k q p.2)

/-
The collision count equals the sum of `2^(zeroCount v)` over all kernel vectors.
-/
theorem collisionPairs_card_eq_sum (k : ℕ) (q : Fin k → ℕ) (hq : ∀ i, q i ≠ 0) :
    (collisionPairs k q).card =
    ∑ v ∈ signedKernel k q, 2 ^ (sign3ZeroCount k v) := by
  rw [ ← Finset.sum_congr rfl fun v hv => sign3Fiber_card k v ];
  rw [ ← Finset.card_biUnion ];
  · congr;
    ext ⟨x, y⟩; simp [collisionPairs, signedKernel, sign3Fiber];
    constructor;
    · exact fun h => ⟨ _, collision_iff_kernel q hq x y |>.1 h, fun i => rfl ⟩;
    · rintro ⟨ a, ha, ha' ⟩ ; exact kernel_implies_collision q hq x y <| by simpa [ funext_iff, ha' ] using ha;
  · exact fun x hx y hy hxy => sign3Fiber_disjoint k x y hxy