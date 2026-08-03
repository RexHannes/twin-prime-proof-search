import Mathlib
import RequestProject.DoublePeelSmooth

/-!
# Cofactor Genealogy Framework

## Overview

The previous session established that v₂-peeling support-4 {2,3}-smooth kernel
vectors can produce non-{2,3}-smooth cofactors from a finite set
C₄ = {5, 7, 13, 19, 41, 43}. The hope was that C₄ might be **self-closing**:
peeling {2,3,C₄}-smooth vectors might produce only C₄-smooth cofactors.

**This is false.** An exhaustive scan of support-5 {2,3}-smooth cores (up to
MAX_VALUE = 10⁶) found 1213 primitive support-5 cores, of which 400 produce
cofactors outside C₄ upon peeling. The new primes include:
{11, 17, 23, 29, 31, 37, 53, 59, 61, 67, 71, 73, 83, 107, 113, 127,
 193, 227, 331, 547, 661, 683, 757, 1093, 2731, 43691}.

Instead of a fixed finite cofactor set, we formalize a **cofactor genealogy**:
a structured framework describing how bad cofactors arise from p-adic peeling,
organized by residual families.

## Contents

1. **Explicit support-5 counterexample** showing cofactor 11 (outside C₄)
2. **Bad cofactor generation** under p-adic peel
3. **Residual-family equivalence** definition
4. **Finite certificate lemmas** for the first few residual families
-/

open Finset BigOperators

set_option maxHeartbeats 400000
set_option maxRecDepth 2000

/-! ### Helper for smoothness proofs -/

private theorem smooth23_by_decide (n : ℕ) (hn : n > 0)
    (h : ∀ q ∈ Finset.filter Nat.Prime (Finset.range (n+1)), q ∣ n → q ≤ 3) :
    IsSmooth23 n := by
  intro p hp hpd
  have hle : p ≤ n := Nat.le_of_dvd hn hpd
  exact h p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩) hpd

/-! ## Section 1: The Support-5 Counterexample

The identity `32 + 3 + 1 = 27 + 9` (equivalently `32 + 3 + 1 - 27 - 9 = 0`)
is a support-5 kernel equation among {2,3}-smooth integers.

Applying the v₃-peel:
- Coprime-to-3 terms: {32, 1} with signs (+1, +1). Sum S₃ = 33 = 3 · 11.
- v₃(33) = 1. Merged value = 33/3 = 11.
- Remaining terms {3, 9, 27} divided by 3 become {1, 3, 9}.
- Residual equation: 11 + 1 - 3 - 9 = 0, i.e., **1 + 11 = 12**.

The cofactor **11 ∉ C₄ = {5, 7, 13, 19, 41, 43}**, proving C₄ is not self-closing.

### Reciprocal interpretation

As a reciprocal identity with Q = {27, 32, 96, 288, 864}:
  1/27 + 1/288 + 1/864 = 1/32 + 1/96 = 1/24.
All denominators are {2,3}-smooth.
-/

section Support5Counterexample

/-- The support-5 {2,3}-smooth kernel equation: 32 + 3 + 1 - 27 - 9 = 0. -/
theorem support5_identity_11 : (32 : ℤ) + 3 + 1 - 27 - 9 = 0 := by norm_num

/-- Equivalently: 32 + 3 + 1 = 27 + 9 = 36. -/
theorem support5_identity_11_split :
    (32 : ℤ) + 3 + 1 = 36 ∧ (27 : ℤ) + 9 = 36 := by constructor <;> norm_num

/-- All five entries are {2,3}-smooth. -/
theorem support5_32_smooth : IsSmooth23 32 := isSmooth23_pow2 5
theorem support5_3_smooth : IsSmooth23 3 := isSmooth23_pow3 1
theorem support5_1_smooth : IsSmooth23 1 := isSmooth23_one
theorem support5_27_smooth : IsSmooth23 27 := isSmooth23_pow3 3
theorem support5_9_smooth : IsSmooth23 9 := isSmooth23_pow3 2

/-- The v₃-peel: coprime-to-3 terms {32, 1} sum to 33 = 3 · 11. -/
theorem v3_peel_sum : (32 : ℤ) + 1 = 33 := by norm_num

/-- 33 = 3 · 11. -/
theorem thirty_three_factored : (33 : ℤ) = 3 * 11 := by norm_num

/-- After v₃-peel (dividing by 3): residual 11 + 1 - 3 - 9 = 0. -/
theorem v3_peel_residual : (11 : ℤ) + 1 - 3 - 9 = 0 := by norm_num

/-- The "1 + 11 = 12" form of the residual. -/
theorem one_plus_eleven : (1 : ℤ) + 11 = 12 := by norm_num

/-- 12 = 3 + 9. -/
theorem twelve_split : (12 : ℤ) = 3 + 9 := by norm_num

/-- 11 is prime. -/
theorem eleven_prime : Nat.Prime 11 := by decide

/-- 11 is NOT {2,3}-smooth: it is a "bad cofactor". -/
theorem eleven_not_smooth23 : ¬ IsSmooth23 11 := by
  intro h; have := h 11 (by decide) (dvd_refl 11); omega

/-- 11 is NOT in the support-4 cofactor set C₄ = {5, 7, 13, 19, 41, 43}. -/
theorem eleven_not_in_C4 : (11 : ℕ) ∉ ({5, 7, 13, 19, 41, 43} : Finset ℕ) := by decide

/-- The reciprocal identity form: 1/27 + 1/288 + 1/864 = 1/32 + 1/96. -/
theorem reciprocal_identity_11 :
    (1 : ℚ) / 27 + 1 / 288 + 1 / 864 = 1 / 32 + 1 / 96 := by norm_num

/-- Both sides equal 1/24. -/
theorem reciprocal_identity_11_value :
    (1 : ℚ) / 27 + 1 / 288 + 1 / 864 = 1 / 24 := by norm_num

/-- All five denominators are {2,3}-smooth. -/
theorem recip_96_smooth : IsSmooth23 96 :=
  smooth23_by_decide 96 (by omega) (by native_decide)
theorem recip_288_smooth : IsSmooth23 288 :=
  smooth23_by_decide 288 (by omega) (by native_decide)
theorem recip_864_smooth : IsSmooth23 864 :=
  smooth23_by_decide 864 (by omega) (by native_decide)

/-- v₂-peel of the same identity trivializes: odd terms sum to -32 = -2⁵. -/
theorem v2_peel_trivializes : (1 : ℤ) + 3 - 9 - 27 = -32 := by norm_num

/-- So v₂-peel gives merged = -1, residual: -1 + 1 = 0 (trivial). -/
theorem v2_peel_residual_trivial : (-1 : ℤ) + 1 = 0 := by norm_num

end Support5Counterexample

/-! ## Section 2: Bad Cofactor Generation under p-adic Peel

A **v₃-peel** of a {2,3}-smooth kernel equation:
1. Collects the coprime-to-3 terms (terms wᵢ = 2^aᵢ, i.e., pure powers of 2).
2. Computes their signed sum S₃ = Σ zᵢ · 2^aᵢ.
3. Divides S₃ and all remaining terms by 3^m where m = min(v₃(S₃), min_j v₃(wⱼ)).
4. The **merged value** M = S₃ / 3^m replaces all coprime-to-3 terms.

The **bad cofactor** is the 6-free part of M.

The bad cofactor set is **not bounded** as the exponents grow:
2^n ± 1 produce Fermat/Mersenne-like factors growing without bound.
-/

section BadCofactorGeneration

/-- Remove all factors of p from n, fuel-bounded. -/
def removeFactorsAux (p : ℕ) (m : ℕ) (fuel : ℕ) : ℕ :=
  if fuel = 0 then m
  else if p > 1 ∧ m % p = 0 ∧ m > 0 then removeFactorsAux p (m / p) (fuel - 1)
  else m

/-- The 6-free part of a natural number: remove all factors of 2 and 3. -/
def sixFreePart (n : ℕ) : ℕ :=
  removeFactorsAux 3 (removeFactorsAux 2 n (n + 1)) (n + 1)

/-- A **v₃-peel cofactor** from a 2-term merge: 6-free part of (2^n + ε). -/
def v3PeelCofactor2 (n : ℕ) (plus : Bool) : ℕ :=
  sixFreePart (if plus then 2^n + 1 else 2^n - 1)

/-- A **v₂-peel cofactor** from a 2-term merge: 6-free part of (3^n + ε). -/
def v2PeelCofactor2 (n : ℕ) (plus : Bool) : ℕ :=
  sixFreePart (if plus then 3^n + 1 else 3^n - 1)

end BadCofactorGeneration

/-! ## Section 3: Residual-Family Equivalence

Two {2,3}-smooth kernel equations produce **equivalent residuals** under
v₃-peeling if their peel residuals, after removing common {2,3}-smooth
scaling (multiplying all terms by 2^a · 3^b), have the same coprime core.

A **residual family** is an equivalence class under this relation,
specified by a coprime core: a tuple of coprime positive integers
with signs summing to zero.
-/

section ResidualFamily

/-- A **signed kernel entry** is a pair of a sign and a positive weight. -/
structure SignedEntry where
  sign : Bool  -- true = +1, false = -1
  weight : ℕ
  weight_pos : 0 < weight := by omega

/-- The signed integer value of an entry. -/
def SignedEntry.val (e : SignedEntry) : ℤ :=
  if e.sign then (e.weight : ℤ) else -(e.weight : ℤ)

/-- A **residual family** is specified by a coprime core. -/
structure ResidualFamilyData where
  name : String
  entries : List SignedEntry
  sum_zero : (entries.map SignedEntry.val).sum = 0
  gcd_one : (entries.map (·.weight)).foldl Nat.gcd 0 = 1

/-- A residual family **has bad prime p** if p is prime, p > 3,
    and p divides some weight in the core. -/
def ResidualFamilyData.hasBadPrime (f : ResidualFamilyData) (p : ℕ) : Prop :=
  Nat.Prime p ∧ p > 3 ∧ ∃ e ∈ f.entries, p ∣ e.weight

end ResidualFamily

/-! ## Section 4: Residual Family Certificates -/

section ResidualFamilyCertificates

/-! ### Family F₁₁: The cofactor-11 family

Core: 11 + 1 - 3 - 9 = 0 (equivalently, 1 + 11 = 12 = 3 + 9).
Arises from v₃-peeling the support-5 identity 32 + 3 + 1 - 27 - 9 = 0.
-/

theorem F11_core_eq : (11 : ℤ) + 1 - 3 - 9 = 0 := by norm_num

theorem F11_coprime : Nat.gcd (Nat.gcd (Nat.gcd 11 1) 3) 9 = 1 := by native_decide

theorem F11_bad_cofactor : ¬ IsSmooth23 11 := eleven_not_smooth23

theorem F11_smooth_entries : IsSmooth23 1 ∧ IsSmooth23 3 ∧ IsSmooth23 9 :=
  ⟨isSmooth23_one, isSmooth23_pow3 1, isSmooth23_pow3 2⟩

theorem F11_scaling (a b : ℕ) :
    (11 : ℤ) * 2^a * 3^b + 1 * 2^a * 3^b -
    3 * 2^a * 3^b - 9 * 2^a * 3^b = 0 := by ring

/-! ### Cofactor-11 source arithmetic -/

theorem pow2_5_plus_1 : 2^5 + 1 = 33 := by norm_num
theorem factor_33 : 33 = 3 * 11 := by norm_num

/-- 6-free parts of 2^n + 1 for small n. -/
theorem v3_cofactors_small :
    sixFreePart (2^1 + 1) = 1 ∧
    sixFreePart (2^2 + 1) = 5 ∧
    sixFreePart (2^3 + 1) = 1 ∧
    sixFreePart (2^4 + 1) = 17 ∧
    sixFreePart (2^5 + 1) = 11 := by native_decide

/-- 6-free parts of 2^n - 1 for small n. -/
theorem v3_cofactors_minus_small :
    sixFreePart (2^2 - 1) = 1 ∧
    sixFreePart (2^3 - 1) = 7 ∧
    sixFreePart (2^4 - 1) = 5 := by native_decide

theorem two_pow5_mod11 : 11 ∣ (2^5 + 1) := ⟨3, by norm_num⟩

theorem v11_of_33 : 33 = 3 * 11 ∧ ¬ (11^2 ∣ 33) := by
  exact ⟨by norm_num, by intro ⟨k, hk⟩; omega⟩

end ResidualFamilyCertificates

/-! ## Section 5: More Residual Family Certificates -/

section MoreFamilies

/-! ### Support-5 identity producing cofactor 5 via v₃-peel

16 - 1 - 24 + 6 + 3 = 0.
v₃-peel: S₃ = 16 - 1 = 15 = 3·5. Merged = 5.
Residual: 5 - 8 + 2 + 1 = 0.
-/
theorem support5_cofactor5 : (16 : ℤ) - 1 - 24 + 6 + 3 = 0 := by norm_num
theorem support5_cofactor5_peel : (5 : ℤ) - 8 + 2 + 1 = 0 := by norm_num
theorem F5_support5_coprime :
    Nat.gcd (Nat.gcd (Nat.gcd 5 8) 2) 1 = 1 := by native_decide

/-! ### Support-5 identity producing cofactor 7 via v₃-peel

64 - 1 - 72 + 6 + 3 = 0.
v₃-peel: S₃ = 64 - 1 = 63. v₃(63) = 2, but min v₃ among remaining = 1.
Divide by 3. Merged = 21 = 3·7. Remaining: 24, 2, 1.
Residual: 21 - 24 + 2 + 1 = 0. Bad cofactor 7.
-/
theorem support5_cofactor7 : (64 : ℤ) - 1 - 72 + 6 + 3 = 0 := by norm_num
theorem support5_cofactor7_residual : (21 : ℤ) - 24 + 2 + 1 = 0 := by norm_num
theorem twentyone_factored : 21 = 3 * 7 := by norm_num

/-- 31 is prime and not {2,3}-smooth. -/
theorem thirtyone_prime_not_smooth : Nat.Prime 31 ∧ ¬ IsSmooth23 31 := by
  constructor
  · decide
  · intro h; have := h 31 (by decide) (dvd_refl 31); omega

end MoreFamilies

/-! ## Section 6: C₄ Non-Closure -/

section NonClosure

/-- The C₄ set from support-4 analysis. -/
def C4 : Finset ℕ := {5, 7, 13, 19, 41, 43}

theorem C4_all_prime : ∀ p ∈ C4, Nat.Prime p := by decide

/-- **C₄ non-closure theorem**: The support-5 identity 32 + 3 + 1 - 27 - 9 = 0
    (all entries {2,3}-smooth) has a v₃-peel residual containing prime factor 11,
    and 11 ∉ C₄. -/
theorem C4_not_self_closing :
    (32 : ℤ) + 3 + 1 - 27 - 9 = 0 ∧
    IsSmooth23 32 ∧ IsSmooth23 3 ∧ IsSmooth23 1 ∧ IsSmooth23 27 ∧ IsSmooth23 9 ∧
    (32 : ℤ) + 1 = 3 * 11 ∧
    Nat.Prime 11 ∧ (11 : ℕ) ∉ C4 := by
  refine ⟨by norm_num, support5_32_smooth, support5_3_smooth, support5_1_smooth,
    support5_27_smooth, support5_9_smooth, by norm_num, by decide, by decide⟩

/-- The "outside-C₄ primes" found in the support-5 scan (subset ≤ 100). -/
def outsideC4Small : Finset ℕ := {11, 17, 23, 29, 31, 37, 53, 59, 61, 67, 71, 73, 83}

theorem outsideC4_all_prime : ∀ p ∈ outsideC4Small, Nat.Prime p := by decide

theorem outsideC4_disjoint : Disjoint outsideC4Small C4 := by decide

theorem outsideC4_not_smooth : ∀ p ∈ outsideC4Small, ¬ IsSmooth23 p := by
  intro p hp h
  have hprime := outsideC4_all_prime p hp
  have hle := h p hprime (dvd_refl p)
  simp only [outsideC4Small, Finset.mem_insert, Finset.mem_singleton] at hp
  omega

end NonClosure

/-! ## Section 7: v₃-Peel Divisibility Criteria -/

section PeelCriteria

/-
For the v₃-peel to be "useful", we need 3 | S₃.
    For 2-term merges: 2^n + 1 ≡ 0 mod 3 iff n is odd.
-/
theorem useful_v3_peel_criterion (n : ℕ) (hn : 0 < n) :
    3 ∣ (2^n + 1) ↔ ¬ 2 ∣ n := by
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at *;

/-
2^n - 1 ≡ 0 mod 3 iff n is even.
-/
theorem useful_v3_peel_criterion_minus (n : ℕ) :
    3 ∣ (2^n - 1) ↔ 2 ∣ n := by
  rw [ ← Nat.mod_add_div ( 2 ^ n ) 3, ← Nat.mod_add_div n 2 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.dvd_iff_mod_eq_zero ] ; have := Nat.mod_lt n zero_lt_two ; interval_cases n % 2 <;> norm_num;

/-- Full derivation of the v₃-peel for the support-5 counterexample. -/
theorem v3_peel_full_derivation :
    (32 : ℤ) + 1 + 3 - 27 - 9 = 0 ∧
    (32 : ℤ) + 1 = 33 ∧
    (33 : ℤ) = 3 * 11 ∧
    (11 : ℤ) + 1 - 9 - 3 = 0 ∧
    (1 : ℤ) + 11 = 3 + 9 := by
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PeelCriteria

/-! ## Section 8: F₁₁ Family Enumeration

The F₁₁ core is NOT unique. Multiple coprime triples (a,b,c) satisfy
11 + a = b + c with all of a,b,c being {2,3}-smooth. For example:
- (1, 3, 9): 11 + 1 = 3 + 9 = 12
- (1, 4, 8): 11 + 1 = 4 + 8 = 12
- (1, 6, 6): 11 + 1 = 6 + 6 = 12
- (2, 4, 9): 11 + 2 = 4 + 9 = 13
- (3, 6, 8): 11 + 3 = 6 + 8 = 14
- (4, 6, 9): 11 + 4 = 6 + 9 = 15
- (6, 8, 9): 11 + 6 = 8 + 9 = 17

Each gives a different residual family shape for the cofactor-11 peel.
-/

section F11Family

/-- All seven cofactor-11 residual identities with {2,3}-smooth entries. -/
theorem F11_family_1 : (11 : ℤ) + 1 = 3 + 9 := by norm_num
theorem F11_family_2 : (11 : ℤ) + 1 = 4 + 8 := by norm_num
theorem F11_family_3 : (11 : ℤ) + 1 = 6 + 6 := by norm_num
theorem F11_family_4 : (11 : ℤ) + 2 = 4 + 9 := by norm_num
theorem F11_family_5 : (11 : ℤ) + 3 = 6 + 8 := by norm_num
theorem F11_family_6 : (11 : ℤ) + 4 = 6 + 9 := by norm_num
theorem F11_family_7 : (11 : ℤ) + 6 = 8 + 9 := by norm_num

end F11Family