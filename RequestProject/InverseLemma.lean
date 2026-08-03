import Mathlib
import RequestProject.EnergySpectrum

/-!
# Structural Lemma: Kernel Vector Differences

## Overview

We investigate whether pairs of signed kernel vectors can produce shorter
kernel vectors. This is the "coding-theoretic inverse" approach.

## Key Obstruction

For `{-1, 0, 1}`-valued kernel vectors `v` and `w`, the pointwise sum
`v + w` may have entries in `{-2, -1, 0, 1, 2}`, which is outside the
`{-1, 0, 1}` alphabet. So the "difference of long codewords gives a short
codeword" argument from linear coding theory does NOT directly apply.

However, when `v` and `w` agree on a coordinate (both `pos` or both `neg`),
the sum at that coordinate has magnitude 2 and must be reduced. This means
the argument only works when `v` and `w` have *disjoint support* or
*complementary signs* on their common support.

## Results

1. **Disjoint-support kernel lemma**: If `v` and `w` are kernel vectors
   with disjoint support, then `v + w` (defined coordinatewise as Sign3 values)
   is also a kernel vector, with `support(v + w) = support(v) + support(w)`.

2. **Sign-complement lemma**: If `v` and `w` are kernel vectors that agree
   on their common support but with opposite signs, then there exists a
   kernel vector of support ≤ |supp(v) Δ supp(w)|`.

Neither of these immediately gives the desired "long → short" inverse theorem.

## What we can prove

Below we prove the disjoint-support composition lemma, which is a clean
exact theorem and part of the infrastructure needed for deeper results.
-/

open Finset BigOperators Fintype

/-- Coordinatewise addition of Sign3 vectors, staying within {-1,0,1}
    when supports are disjoint. -/
def sign3Add (a b : Sign3) : Sign3 :=
  match a, b with
  | Sign3.zero, x => x
  | x, Sign3.zero => x
  | _, _ => Sign3.zero  -- This case shouldn't occur for disjoint supports

/-- The support of the pointwise Sign3 sum of disjoint-support vectors
    is the union of supports. -/
theorem sign3Add_ne_zero_iff_disjoint {a b : Sign3}
    (ha : a = Sign3.zero ∨ b = Sign3.zero) :
    sign3Add a b ≠ Sign3.zero ↔ (a ≠ Sign3.zero ∨ b ≠ Sign3.zero) := by
  rcases ha with ha | hb
  · subst ha; cases b <;> simp [sign3Add]
  · subst hb; cases a <;> simp [sign3Add]

/-
When supports are disjoint, the signed reciprocal sum adds.
-/
theorem signedRecipSum_add_disjoint (k : ℕ) (q : Fin k → ℕ)
    (v w : Fin k → Sign3)
    (hdisjoint : ∀ i, v i = Sign3.zero ∨ w i = Sign3.zero) :
    signedRecipSum k q (fun i => sign3Add (v i) (w i)) =
    signedRecipSum k q v + signedRecipSum k q w := by
  unfold signedRecipSum;
  rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; rcases hdisjoint i with h | h <;> unfold sign3Add <;> simp +decide [ h ] ;
  cases v i <;> simp +decide

/-
If `v` and `w` are kernel vectors with disjoint support,
    their Sign3 sum is also a kernel vector.
-/
theorem kernel_add_disjoint (k : ℕ) (q : Fin k → ℕ)
    (v w : Fin k → Sign3)
    (hv : signedRecipSum k q v = 0)
    (hw : signedRecipSum k q w = 0)
    (hdisjoint : ∀ i, v i = Sign3.zero ∨ w i = Sign3.zero) :
    signedRecipSum k q (fun i => sign3Add (v i) (w i)) = 0 := by
  convert signedRecipSum_add_disjoint k q v w hdisjoint using 1 ; aesop

/-- The negation of a Sign3 vector. -/
def sign3Neg : Sign3 → Sign3
  | Sign3.neg  => Sign3.pos
  | Sign3.zero => Sign3.zero
  | Sign3.pos  => Sign3.neg

/-
Negation preserves kernel membership.
-/
theorem kernel_neg (k : ℕ) (q : Fin k → ℕ) (v : Fin k → Sign3)
    (hv : signedRecipSum k q v = 0) :
    signedRecipSum k q (fun i => sign3Neg (v i)) = 0 := by
  unfold signedRecipSum at *;
  -- By definition of `sign3Neg`, we know that `(sign3Neg (v i)).toRat = -(v i).toRat`.
  have h_sign3Neg : ∀ i, (sign3Neg (v i)).toRat = -(v i).toRat := by
    exact fun i => by rcases v i with ( _ | _ | _ | _ ) <;> trivial;
  simp_all +decide [ neg_div ]

/-
Negation preserves support.
-/
theorem sign3Neg_support (k : ℕ) (v : Fin k → Sign3) :
    sign3Support k (fun i => sign3Neg (v i)) = sign3Support k v := by
  unfold sign3Support;
  congr! 2;
  ext i; exact (by
  cases h : v i <;> simp +decide [ h ])

/-!
## Why the direct inverse argument fails

The key obstruction: given two kernel vectors `v, w` of support `s` each,
if they share `t` coordinates in their support, the pointwise sum may have
entries `±2` at those coordinates. Replacing `±2` with `0` changes the
signed sum, so the result is NOT a kernel vector.

To make this work, one would need to:
1. Find `v, w` that agree on common support with *opposite* signs
   (so `v_i + w_i = 0` at shared positions), OR
2. Use the algebraic structure of smooth denominators to decompose
   the `±2` positions into new kernel vectors.

Neither approach has been made to work in general.
-/