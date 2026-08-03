import Mathlib
import RequestProject.EnergySpectrum

/-!
# Exact Collision-Count Decomposition by Support Level

## Overview

We decompose the collision count into a diagonal term plus contributions
grouped by support size, yielding the energy spectrum formula:

  `#Collisions = 2^k + Σ_{s=1}^{k} E_s(Q) * 2^{k-s}`

where `E_s(Q)` counts nonzero signed kernel vectors of support exactly `s`.

This builds on the fiber decomposition in `EnergySpectrum.lean`, which proved:

  `#Collisions = Σ_{v ∈ Λ(Q)} 2^{zeroCount(v)}`

## Definitions

- `zeroVec k` — the zero signed vector (all entries `Sign3.zero`)
- `nonzeroSignedKernel k q` — kernel vectors excluding the zero vector
- `energyAtSupport k q s` — `E_s(Q)`, count of nonzero kernel vectors with support `s`
-/

open Finset BigOperators Fintype

/-! ## 1. The Zero Vector -/

/-- The zero signed vector: all entries are `Sign3.zero`. -/
def zeroVec (k : ℕ) : Fin k → Sign3 := fun _ => Sign3.zero

/-- The zero vector has zero count equal to `k`. -/
theorem zeroVec_zeroCount (k : ℕ) : sign3ZeroCount k (zeroVec k) = k := by
  simp [sign3ZeroCount, zeroVec]

/-- The zero vector has signed reciprocal sum 0 for any denominators. -/
theorem zeroVec_in_kernel (k : ℕ) (q : Fin k → ℕ) :
    signedRecipSum k q (zeroVec k) = 0 := by
  simp [signedRecipSum, zeroVec, Sign3.toRat]

/-- The zero vector has support 0. -/
theorem zeroVec_support (k : ℕ) : sign3Support k (zeroVec k) = 0 := by
  simp [sign3Support, zeroVec]

/-- The zero vector is in the signed kernel. -/
theorem zeroVec_mem_signedKernel (k : ℕ) (q : Fin k → ℕ) :
    zeroVec k ∈ signedKernel k q := by
  simp [signedKernel, zeroVec_in_kernel]

/-! ## 2. Nonzero Kernel and Energy Spectrum -/

/-- The nonzero signed kernel: kernel vectors excluding the zero vector. -/
noncomputable def nonzeroSignedKernel (k : ℕ) (q : Fin k → ℕ) : Finset (Fin k → Sign3) :=
  (signedKernel k q).erase (zeroVec k)

/-- The energy at support level `s`: the number of nonzero kernel vectors
    with support exactly `s`. This is `E_s(Q)`. -/
noncomputable def energyAtSupport (k : ℕ) (q : Fin k → ℕ) (s : ℕ) : ℕ :=
  ((nonzeroSignedKernel k q).filter (fun v => sign3Support k v = s)).card

/-! ## 3. Splitting the Sum at the Zero Vector -/

/-- The collision count splits as `2^k` (diagonal) plus the nonzero kernel contribution. -/
theorem collisionPairs_split_diagonal (k : ℕ) (q : Fin k → ℕ) (hq : ∀ i, q i ≠ 0) :
    (collisionPairs k q).card =
    2 ^ k + ∑ v ∈ nonzeroSignedKernel k q, 2 ^ (sign3ZeroCount k v) := by
  rw [collisionPairs_card_eq_sum k q hq]
  rw [← Finset.add_sum_erase _ _ (zeroVec_mem_signedKernel k q)]
  rw [zeroVec_zeroCount]
  rfl


/-! ## 4. Zero Count vs Support -/

/-- For any signed vector, `sign3ZeroCount k v = k - sign3Support k v`. -/
theorem zeroCount_eq_sub_support (k : ℕ) (v : Fin k → Sign3) :
    sign3ZeroCount k v = k - sign3Support k v := by
  have h := sign3ZeroCount_add_support k v
  omega

/-! ## 5. Grouping by Support: the Energy Spectrum Formula -/

/-- Support of any signed vector is at most k. -/
theorem sign3Support_le (k : ℕ) (v : Fin k → Sign3) : sign3Support k v ≤ k := by
  have h := sign3ZeroCount_add_support k v; omega

/-- Support of a nonzero kernel vector is in `range (k+1)`. -/
theorem support_mem_range (k : ℕ) (q : Fin k → ℕ) (v : Fin k → Sign3)
    (_hv : v ∈ nonzeroSignedKernel k q) :
    sign3Support k v ∈ Finset.range (k + 1) := by
  simp only [Finset.mem_range]
  exact Nat.lt_add_one_iff.mpr (sign3Support_le k v)

/-
The collision count decomposes as:
    `#Collisions = 2^k + Σ_{s ∈ range(k+1)} E_s(Q) * 2^{k-s}`.
    This is the main energy spectrum decomposition.
-/
theorem collisionPairs_card_eq_diagonal_add_energy (k : ℕ) (q : Fin k → ℕ) (hq : ∀ i, q i ≠ 0) :
    (collisionPairs k q).card =
    2 ^ k + ∑ s ∈ Finset.range (k + 1), energyAtSupport k q s * 2 ^ (k - s) := by
  rw [ collisionPairs_split_diagonal, ← Finset.sum_subset ( show ( Finset.filter ( fun v => sign3Support k v ∈ Finset.range ( k + 1 ) ) ( nonzeroSignedKernel k q ) ) ⊆ ( nonzeroSignedKernel k q ) from Finset.filter_subset _ _ ) ];
  · rw [ Finset.sum_congr rfl fun x hx => by rw [ zeroCount_eq_sub_support ] ];
    simp +decide [ energyAtSupport ];
    simp +decide only [sum_filter, Finset.card_eq_sum_ones];
    simp +decide only [sum_mul _ _ _];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  · exact fun x hx hx' => False.elim <| hx' <| Finset.mem_filter.mpr ⟨ hx, support_mem_range k q x hx ⟩;
  · assumption

/-! ## 6. Explicit Bijection Maps

The ordered collision bijection:
  `(U, V) with R(U) = R(V)` ↔ `(v, C)` where `v ∈ Λ(Q)` and `C ⊆ {i : v i = zero}`

is captured by the fiber decomposition in `EnergySpectrum.lean`.
Below we state the explicit forward and inverse maps and prove round-trip properties.
-/

/-- Forward map: extract the signed kernel vector from a collision pair. -/
def collisionToKernel {k : ℕ} (p : (Fin k → Bool) × (Fin k → Bool)) :
    Fin k → Sign3 :=
  fun i => diffSign (p.1 i) (p.2 i)

/-- Forward map: extract the overlap indicator from a collision pair.
    The overlap at coordinate `i` is `true` iff both `x i` and `y i` are `true`. -/
def collisionToOverlap {k : ℕ} (p : (Fin k → Bool) × (Fin k → Bool)) :
    Fin k → Bool :=
  fun i => p.1 i && p.2 i

/-- Inverse map: reconstruct the collision pair from kernel vector and overlap. -/
def kernelOverlapToCollision {k : ℕ} (v : Fin k → Sign3) (c : Fin k → Bool) :
    (Fin k → Bool) × (Fin k → Bool) :=
  (fun i => match v i with
    | Sign3.pos => true
    | Sign3.neg => false
    | Sign3.zero => c i,
   fun i => match v i with
    | Sign3.pos => false
    | Sign3.neg => true
    | Sign3.zero => c i)

/-- Round-trip: kernel vector of reconstructed pair equals original. -/
theorem collisionToKernel_kernelOverlap (k : ℕ) (v : Fin k → Sign3) (c : Fin k → Bool) :
    collisionToKernel (kernelOverlapToCollision v c) = v := by
  ext i; simp [collisionToKernel, kernelOverlapToCollision]
  cases v i
  · simp [diffSign]
  · simp [diffSign]; cases c i <;> rfl
  · simp [diffSign]

/-- Round-trip: reconstructing from extracted kernel and overlap gives original pair. -/
theorem kernelOverlap_roundtrip (k : ℕ) (x y : Fin k → Bool) :
    kernelOverlapToCollision (collisionToKernel (x, y)) (collisionToOverlap (x, y)) = (x, y) := by
  ext i
  · simp [kernelOverlapToCollision, collisionToKernel, collisionToOverlap]
    cases x i <;> cases y i <;> rfl
  · simp [kernelOverlapToCollision, collisionToKernel, collisionToOverlap]
    cases x i <;> cases y i <;> rfl