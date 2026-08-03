import Mathlib
import RequestProject.DoublePeelSmooth

/-!
# Carrier Complexity Framework

## Overview

Session 9 established that C₄-self-closure is FALSE: support-5 {2,3}-smooth cores
produce cofactors outside C₄ = {5,7,13,19,41,43} upon peeling. An exhaustive scan
(MAX_VALUE = 10⁶) found 1213 primitive support-5 cores, 400 of which are "bad"
(produce outside-C₄ cofactors), yielding 395 distinct residual signatures.

The key positive finding: **all 400 bad peels have carrier complexity 1**.
That is, each residual equation contains exactly one term whose prime factorization
includes a prime outside ALLOWED = {2,3,5,7,13,19,41,43}.

This file formalizes:
1. The ALLOWED prime set and ALLOWED-smoothness
2. Carrier terms and carrier complexity
3. Explicit examples of carrier-complexity-1 residuals
4. A finite certificate framework for verifying carrier complexity 1

## Motivation

Rather than pursuing C₄-self-closure (which fails) or enumerating all residual
signatures (395 distinct — too many for a small catalogue), we formalize the
**carrier complexity** invariant. The empirical observation that carrier complexity
is always 1 suggests a structural constraint: bad peels introduce exactly one
"exotic" prime factor, while all other residual terms remain ALLOWED-smooth.

This bounded-carrier-descent picture is the proposed replacement for the failed
C₄-closure route toward subcritical energy counting.
-/

open Finset BigOperators

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

/-! ## Section 1: The ALLOWED Prime Set -/

section AllowedPrimes

/-- The ALLOWED prime set: {2, 3, 5, 7, 13, 19, 41, 43}.
    This extends {2,3} (the smooth base) with C₄ = {5,7,13,19,41,43}
    (the support-4 peel cofactors). -/
def AllowedPrimes : Finset ℕ := {2, 3, 5, 7, 13, 19, 41, 43}

/-- Every element of AllowedPrimes is prime. -/
theorem AllowedPrimes_all_prime : ∀ p ∈ AllowedPrimes, Nat.Prime p := by decide

/-- {2,3} ⊆ AllowedPrimes. -/
theorem smooth23_sub_allowed : ({2, 3} : Finset ℕ) ⊆ AllowedPrimes := by decide

/-- C₄ ⊆ AllowedPrimes. -/
theorem C4_sub_allowed : ({5, 7, 13, 19, 41, 43} : Finset ℕ) ⊆ AllowedPrimes := by decide

/-- A positive natural number is **ALLOWED-smooth** if every prime factor lies in
    AllowedPrimes = {2,3,5,7,13,19,41,43}. -/
def IsAllowedSmooth (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∈ AllowedPrimes

/-- 1 is ALLOWED-smooth (vacuously). -/
theorem isAllowedSmooth_one : IsAllowedSmooth 1 := by
  intro p hp hd
  have : p ≤ 1 := Nat.le_of_dvd one_pos hd
  exact absurd hp.one_lt (by omega)

/-- Any {2,3}-smooth number is ALLOWED-smooth. -/
theorem isAllowedSmooth_of_smooth23 {n : ℕ} (h : IsSmooth23 n) : IsAllowedSmooth n := by
  intro p hp hpd
  have hle := h p hp hpd
  show p ∈ AllowedPrimes
  have hp2 := hp.two_le
  interval_cases p <;> simp [AllowedPrimes]

/-- If d divides n and n is ALLOWED-smooth, then d is ALLOWED-smooth. -/
theorem isAllowedSmooth_of_dvd {n d : ℕ} (hn : IsAllowedSmooth n) (hd : d ∣ n) :
    IsAllowedSmooth d :=
  fun p hp hpd => hn p hp (dvd_trans hpd hd)

/-- Product of ALLOWED-smooth numbers is ALLOWED-smooth. -/
theorem isAllowedSmooth_mul {a b : ℕ} (ha : IsAllowedSmooth a) (hb : IsAllowedSmooth b) :
    IsAllowedSmooth (a * b) := by
  intro p hp hpd
  rcases hp.dvd_mul.mp hpd with h | h
  · exact ha p hp h
  · exact hb p hp h

/-- Helper: verify ALLOWED-smoothness by checking all prime factors via native_decide. -/
private theorem allowedSmooth_by_native (n : ℕ) (hn : 0 < n)
    (h : ∀ q ∈ Finset.filter Nat.Prime (Finset.range (n+1)), q ∣ n → q ∈ AllowedPrimes) :
    IsAllowedSmooth n := by
  intro p hp hpd
  have hle : p ≤ n := Nat.le_of_dvd hn hpd
  exact h p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩) hpd

end AllowedPrimes

/-! ## Section 2: Specific ALLOWED-smooth Verifications -/

section AllowedSmoothExamples

-- Small ALLOWED-smooth numbers used in examples
theorem isAllowedSmooth_2 : IsAllowedSmooth 2 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow2 1)
theorem isAllowedSmooth_3 : IsAllowedSmooth 3 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow3 1)
theorem isAllowedSmooth_4 : IsAllowedSmooth 4 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow2 2)
theorem isAllowedSmooth_8 : IsAllowedSmooth 8 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow2 3)
theorem isAllowedSmooth_9 : IsAllowedSmooth 9 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow3 2)
theorem isAllowedSmooth_16 : IsAllowedSmooth 16 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow2 4)
theorem isAllowedSmooth_27 : IsAllowedSmooth 27 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow3 3)
theorem isAllowedSmooth_81 : IsAllowedSmooth 81 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow3 4)
theorem isAllowedSmooth_128 : IsAllowedSmooth 128 :=
  isAllowedSmooth_of_smooth23 (isSmooth23_pow2 7)

-- Numbers with C₄ primes, verified by native_decide
theorem isAllowedSmooth_5 : IsAllowedSmooth 5 :=
  allowedSmooth_by_native 5 (by omega) (by native_decide)
theorem isAllowedSmooth_7 : IsAllowedSmooth 7 :=
  allowedSmooth_by_native 7 (by omega) (by native_decide)
theorem isAllowedSmooth_12 : IsAllowedSmooth 12 :=
  allowedSmooth_by_native 12 (by omega) (by native_decide)
theorem isAllowedSmooth_13 : IsAllowedSmooth 13 :=
  allowedSmooth_by_native 13 (by omega) (by native_decide)
theorem isAllowedSmooth_96 : IsAllowedSmooth 96 :=
  allowedSmooth_by_native 96 (by omega) (by native_decide)
theorem isAllowedSmooth_324 : IsAllowedSmooth 324 :=
  allowedSmooth_by_native 324 (by omega) (by native_decide)
theorem isAllowedSmooth_560 : IsAllowedSmooth 560 :=
  allowedSmooth_by_native 560 (by omega) (by native_decide)
theorem isAllowedSmooth_684 : IsAllowedSmooth 684 :=
  allowedSmooth_by_native 684 (by omega) (by native_decide)

end AllowedSmoothExamples

/-! ## Section 3: Carrier Terms and Carrier Complexity -/

section CarrierComplexity

/-- A natural number **has an outside carrier** if it has a prime factor not in AllowedPrimes.
    Equivalently, it is NOT ALLOWED-smooth. -/
def HasOutsideCarrier (n : ℕ) : Prop := ¬ IsAllowedSmooth n

/-- `HasOutsideCarrier n` iff there exists a prime factor outside AllowedPrimes. -/
theorem hasOutsideCarrier_iff {n : ℕ} (_hn : 1 < n) :
    HasOutsideCarrier n ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ∉ AllowedPrimes := by
  constructor
  · intro h
    by_contra habs
    push_neg at habs
    exact h (fun p hp hpd => habs p hp hpd)
  · intro ⟨p, hp, hpd, hnotin⟩ hsmooth
    exact hnotin (hsmooth p hp hpd)

end CarrierComplexity

/-! ## Section 4: Certificate Framework for Support-5 Bad Peels

A **carrier-complexity-1 certificate** for a support-5 {2,3}-smooth bad peel
consists of:
1. The carrier term weight and sign
2. The ALLOWED-smooth term weights and signs
3. Proofs that the equation sums to zero, the carrier is outside, and all
   other terms are ALLOWED-smooth

The framework is designed so that each certificate is a small self-contained
verification, enabling batch proofs over the 400 bad peels. -/

section CertificateFramework

/-- A **carrier-1 certificate** asserts that a residual equation arising from
    a support-5 {2,3}-smooth peel has exactly one carrier term. -/
structure Carrier1Certificate where
  /-- Human-readable name for the certificate -/
  name : String
  /-- The carrier term weight (the "exotic" value) -/
  carrierWeight : ℕ
  /-- The carrier term sign (true = positive) -/
  carrierSign : Bool
  /-- The ALLOWED-smooth term weights -/
  smoothWeights : List ℕ
  /-- The ALLOWED-smooth term signs -/
  smoothSigns : List Bool
  /-- Lengths match -/
  lengths_match : smoothWeights.length = smoothSigns.length

/-- The signed value of the carrier term. -/
def Carrier1Certificate.carrierVal (c : Carrier1Certificate) : ℤ :=
  if c.carrierSign then (c.carrierWeight : ℤ) else -(c.carrierWeight : ℤ)

/-- The list of signed smooth values. -/
def Carrier1Certificate.smoothVals (c : Carrier1Certificate) : List ℤ :=
  (c.smoothWeights.zip c.smoothSigns).map fun ⟨w, s⟩ =>
    if s then (w : ℤ) else -(w : ℤ)

/-- A certificate is **valid** if:
    1. The equation sums to zero
    2. The carrier weight has a prime factor outside ALLOWED
    3. All smooth weights are indeed ALLOWED-smooth -/
structure Carrier1Certificate.IsValid (c : Carrier1Certificate) : Prop where
  sum_zero : c.carrierVal + c.smoothVals.sum = 0
  carrier_outside : HasOutsideCarrier c.carrierWeight
  all_smooth : ∀ w ∈ c.smoothWeights, IsAllowedSmooth w

/-- A valid Carrier1Certificate witnesses carrier complexity 1:
    exactly one term (the carrier) has an outside-ALLOWED prime factor,
    and all other terms are ALLOWED-smooth. -/
theorem carrier1_certificate_gives_complexity_one (c : Carrier1Certificate)
    (hv : c.IsValid) :
    HasOutsideCarrier c.carrierWeight ∧
    ∀ w ∈ c.smoothWeights, IsAllowedSmooth w :=
  ⟨hv.carrier_outside, hv.all_smooth⟩

end CertificateFramework

/-! ## Section 5: Helper for Outside-Carrier Proofs -/

section OutsideCarrierHelpers

/-- 11 has an outside carrier (11 is prime, ∉ ALLOWED). -/
theorem hasOutsideCarrier_11 : HasOutsideCarrier 11 := by
  intro h; exact absurd (h 11 (by decide) (dvd_refl 11)) (by decide)

/-- 17 has an outside carrier. -/
theorem hasOutsideCarrier_17 : HasOutsideCarrier 17 := by
  intro h; exact absurd (h 17 (by decide) (dvd_refl 17)) (by decide)

/-- 61 has an outside carrier. -/
theorem hasOutsideCarrier_61 : HasOutsideCarrier 61 := by
  intro h; exact absurd (h 61 (by decide) (dvd_refl 61)) (by decide)

/-- 73 has an outside carrier. -/
theorem hasOutsideCarrier_73 : HasOutsideCarrier 73 := by
  intro h; exact absurd (h 73 (by decide) (dvd_refl 73)) (by decide)

/-- 85 = 5 · 17 has an outside carrier. -/
theorem hasOutsideCarrier_85 : HasOutsideCarrier 85 := by
  intro h; exact absurd (h 17 (by decide) ⟨5, by norm_num⟩) (by decide)

/-- 121 = 11² has an outside carrier. -/
theorem hasOutsideCarrier_121 : HasOutsideCarrier 121 := by
  intro h; exact absurd (h 11 (by decide) ⟨11, by norm_num⟩) (by decide)

/-- 122 = 2 · 61 has an outside carrier. -/
theorem hasOutsideCarrier_122 : HasOutsideCarrier 122 := by
  intro h; exact absurd (h 61 (by decide) ⟨2, by norm_num⟩) (by decide)

/-- 341 = 11 · 31 has an outside carrier. -/
theorem hasOutsideCarrier_341 : HasOutsideCarrier 341 := by
  intro h; exact absurd (h 11 (by decide) ⟨31, by norm_num⟩) (by decide)

/-- 547 has an outside carrier (547 is prime). -/
theorem hasOutsideCarrier_547 : HasOutsideCarrier 547 := by
  intro h; exact absurd (h 547 (by native_decide) (dvd_refl 547)) (by decide)

/-- 683 has an outside carrier (683 is prime). -/
theorem hasOutsideCarrier_683 : HasOutsideCarrier 683 := by
  intro h; exact absurd (h 683 (by native_decide) (dvd_refl 683)) (by decide)

/-- 1093 has an outside carrier (1093 is prime). -/
theorem hasOutsideCarrier_1093 : HasOutsideCarrier 1093 := by
  intro h; exact absurd (h 1093 (by native_decide) (dvd_refl 1093)) (by decide)

/-- 3641 = 11 · 331 has an outside carrier. -/
theorem hasOutsideCarrier_3641 : HasOutsideCarrier 3641 := by
  intro h; exact absurd (h 11 (by decide) ⟨331, by norm_num⟩) (by decide)

end OutsideCarrierHelpers

/-! ## Section 6: Explicit Carrier-Complexity-1 Examples

Each example is a residual equation from a support-5 {2,3}-smooth peel,
containing exactly one carrier term (the "outside" prime factor). -/

section Examples

/-! ### Example 1: 1 + 11 = 12 (equivalently 11 + 1 - 3 - 9 = 0)
    From v₃-peel of 32 + 3 + 1 = 27 + 9.
    Carrier term: 11. Other terms: 1, 3, 9 (all ALLOWED-smooth). -/

theorem carrier_ex1_identity : (11 : ℤ) + 1 - 3 - 9 = 0 := by norm_num

theorem carrier_ex1_complexity_one :
    HasOutsideCarrier 11 ∧ IsAllowedSmooth 1 ∧ IsAllowedSmooth 3 ∧ IsAllowedSmooth 9 :=
  ⟨hasOutsideCarrier_11, isAllowedSmooth_one, isAllowedSmooth_3, isAllowedSmooth_9⟩

/-! ### Example 2: 2 + 9 = 11 (equivalently 11 - 2 - 9 = 0)
    Carrier term: 11. Other terms: 2, 9 (ALLOWED-smooth). -/

theorem carrier_ex2_identity : (11 : ℤ) - 2 - 9 = 0 := by norm_num

theorem carrier_ex2_complexity_one :
    HasOutsideCarrier 11 ∧ IsAllowedSmooth 2 ∧ IsAllowedSmooth 9 :=
  ⟨hasOutsideCarrier_11, isAllowedSmooth_2, isAllowedSmooth_9⟩

/-! ### Example 3: 3 + 8 = 11 (equivalently 11 - 3 - 8 = 0)
    Carrier term: 11. Other terms: 3, 8 (ALLOWED-smooth). -/

theorem carrier_ex3_identity : (11 : ℤ) - 3 - 8 = 0 := by norm_num

theorem carrier_ex3_complexity_one :
    HasOutsideCarrier 11 ∧ IsAllowedSmooth 3 ∧ IsAllowedSmooth 8 :=
  ⟨hasOutsideCarrier_11, isAllowedSmooth_3, isAllowedSmooth_8⟩

/-! ### Example 4: 4 + 81 = 85 = 5 · 17 (equivalently 85 - 4 - 81 = 0)
    Carrier term: 85 (has factor 17 ∉ ALLOWED). Other terms: 4, 81 (ALLOWED-smooth). -/

theorem carrier_ex4_identity : (85 : ℤ) - 4 - 81 = 0 := by norm_num

theorem carrier_ex4_complexity_one :
    HasOutsideCarrier 85 ∧ IsAllowedSmooth 4 ∧ IsAllowedSmooth 81 :=
  ⟨hasOutsideCarrier_85, isAllowedSmooth_4, isAllowedSmooth_81⟩

/-! ### Example 5: 1 + 16 + 324 = 341 = 11 · 31 (equivalently 341 - 1 - 16 - 324 = 0)
    Carrier term: 341 (has factors 11, 31 ∉ ALLOWED).
    Other terms: 1, 16, 324 (all ALLOWED-smooth). -/

theorem carrier_ex5_identity : (341 : ℤ) - 1 - 16 - 324 = 0 := by norm_num

theorem carrier_ex5_complexity_one :
    HasOutsideCarrier 341 ∧ IsAllowedSmooth 1 ∧ IsAllowedSmooth 16 ∧ IsAllowedSmooth 324 :=
  ⟨hasOutsideCarrier_341, isAllowedSmooth_one, isAllowedSmooth_16, isAllowedSmooth_324⟩

/-! ### Example 6: 1 + 122 = 27 + 96, where 122 = 2 · 61 (equivalently 122 + 1 - 27 - 96 = 0)
    Carrier term: 122 (has factor 61 ∉ ALLOWED).
    Other terms: 1, 27, 96 (all ALLOWED-smooth). -/

theorem carrier_ex6_identity : (122 : ℤ) + 1 - 27 - 96 = 0 := by norm_num

theorem carrier_ex6_complexity_one :
    HasOutsideCarrier 122 ∧ IsAllowedSmooth 1 ∧ IsAllowedSmooth 27 ∧ IsAllowedSmooth 96 :=
  ⟨hasOutsideCarrier_122, isAllowedSmooth_one, isAllowedSmooth_27, isAllowedSmooth_96⟩

end Examples

/-! ## Section 7: Representative Certificate Instances

We instantiate the certificate framework for several representative bad peels,
covering the most common outside parts: 11, 61, 17, 121, 341, 73, 547, 683. -/

section RepresentativeCertificates

/-! ### Certificate: cofactor 11, family "1+11=12" -/

def cert_11_a : Carrier1Certificate where
  name := "11+1=3+9"
  carrierWeight := 11
  carrierSign := true
  smoothWeights := [1, 3, 9]
  smoothSigns := [true, false, false]
  lengths_match := rfl

theorem cert_11_a_valid : cert_11_a.IsValid where
  sum_zero := by native_decide
  carrier_outside := hasOutsideCarrier_11
  all_smooth := by
    intro w hw; simp [cert_11_a] at hw
    rcases hw with rfl | rfl | rfl
    · exact isAllowedSmooth_one
    · exact isAllowedSmooth_3
    · exact isAllowedSmooth_9

/-! ### Certificate: cofactor 61, family "122+1=27+96" -/

def cert_61_a : Carrier1Certificate where
  name := "122+1=27+96"
  carrierWeight := 122
  carrierSign := true
  smoothWeights := [1, 27, 96]
  smoothSigns := [true, false, false]
  lengths_match := rfl

theorem cert_61_a_valid : cert_61_a.IsValid where
  sum_zero := by native_decide
  carrier_outside := hasOutsideCarrier_122
  all_smooth := by
    intro w hw; simp [cert_61_a] at hw
    rcases hw with rfl | rfl | rfl
    · exact isAllowedSmooth_one
    · exact isAllowedSmooth_27
    · exact isAllowedSmooth_96

/-! ### Certificate: cofactor 17, family "85=4+81" -/

def cert_17_a : Carrier1Certificate where
  name := "85=4+81"
  carrierWeight := 85
  carrierSign := true
  smoothWeights := [4, 81]
  smoothSigns := [false, false]
  lengths_match := rfl

theorem cert_17_a_valid : cert_17_a.IsValid where
  sum_zero := by native_decide
  carrier_outside := hasOutsideCarrier_85
  all_smooth := by
    intro w hw; simp [cert_17_a] at hw
    rcases hw with rfl | rfl
    · exact isAllowedSmooth_4
    · exact isAllowedSmooth_81

/-! ### Certificate: cofactor 121 = 11², family "121+7=128" -/

def cert_121_a : Carrier1Certificate where
  name := "121+7=128"
  carrierWeight := 121
  carrierSign := true
  smoothWeights := [7, 128]
  smoothSigns := [true, false]
  lengths_match := rfl

theorem cert_121_a_valid : cert_121_a.IsValid where
  sum_zero := by native_decide
  carrier_outside := hasOutsideCarrier_121
  all_smooth := by
    intro w hw; simp [cert_121_a] at hw
    rcases hw with rfl | rfl
    · exact isAllowedSmooth_7
    · exact isAllowedSmooth_128

/-! ### Certificate: cofactor 341 = 11 · 31, family "341=1+16+324" -/

def cert_341_a : Carrier1Certificate where
  name := "341=1+16+324"
  carrierWeight := 341
  carrierSign := true
  smoothWeights := [1, 16, 324]
  smoothSigns := [false, false, false]
  lengths_match := rfl

theorem cert_341_a_valid : cert_341_a.IsValid where
  sum_zero := by native_decide
  carrier_outside := hasOutsideCarrier_341
  all_smooth := by
    intro w hw; simp [cert_341_a] at hw
    rcases hw with rfl | rfl | rfl
    · exact isAllowedSmooth_one
    · exact isAllowedSmooth_16
    · exact isAllowedSmooth_324

/-! ### Certificate: cofactor 73, family "73+8=81" -/

def cert_73_a : Carrier1Certificate where
  name := "73+8=81"
  carrierWeight := 73
  carrierSign := true
  smoothWeights := [8, 81]
  smoothSigns := [true, false]
  lengths_match := rfl

theorem cert_73_a_valid : cert_73_a.IsValid where
  sum_zero := by native_decide
  carrier_outside := hasOutsideCarrier_73
  all_smooth := by
    intro w hw; simp [cert_73_a] at hw
    rcases hw with rfl | rfl
    · exact isAllowedSmooth_8
    · exact isAllowedSmooth_81

/-! ### Certificate: cofactor 547, family "547+13=560"
    547 is prime. 560 = 2⁴ · 5 · 7, ALLOWED-smooth. -/

def cert_547_a : Carrier1Certificate where
  name := "547+13=560"
  carrierWeight := 547
  carrierSign := true
  smoothWeights := [13, 560]
  smoothSigns := [true, false]
  lengths_match := rfl

theorem cert_547_a_valid : cert_547_a.IsValid where
  sum_zero := by native_decide
  carrier_outside := hasOutsideCarrier_547
  all_smooth := by
    intro w hw; simp [cert_547_a] at hw
    rcases hw with rfl | rfl
    · exact isAllowedSmooth_13
    · exact isAllowedSmooth_560

/-! ### Certificate: cofactor 683, family "683+1=684"
    683 is prime. 684 = 2² · 3² · 19, ALLOWED-smooth. -/

def cert_683_a : Carrier1Certificate where
  name := "683+1=684"
  carrierWeight := 683
  carrierSign := true
  smoothWeights := [1, 684]
  smoothSigns := [true, false]
  lengths_match := rfl

theorem cert_683_a_valid : cert_683_a.IsValid where
  sum_zero := by native_decide
  carrier_outside := hasOutsideCarrier_683
  all_smooth := by
    intro w hw; simp [cert_683_a] at hw
    rcases hw with rfl | rfl
    · exact isAllowedSmooth_one
    · exact isAllowedSmooth_684

end RepresentativeCertificates

/-! ## Section 8: Batch Certificate Verification -/

section BatchVerification

/-- The list of all verified certificates. -/
def verifiedCertificates : List Carrier1Certificate :=
  [cert_11_a, cert_61_a, cert_17_a, cert_121_a, cert_341_a, cert_73_a, cert_547_a, cert_683_a]

/-- All 8 representative certificates cover 8 distinct outside parts. -/
theorem certificates_distinct_carriers :
    (verifiedCertificates.map (·.carrierWeight)).Nodup := by native_decide

/-- Summary: every verified certificate has an outside carrier. -/
theorem all_verified_have_outside_carrier :
    ∀ c ∈ verifiedCertificates, HasOutsideCarrier c.carrierWeight := by
  intro c hc
  simp only [verifiedCertificates, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_11_a_valid.carrier_outside
  · exact cert_61_a_valid.carrier_outside
  · exact cert_17_a_valid.carrier_outside
  · exact cert_121_a_valid.carrier_outside
  · exact cert_341_a_valid.carrier_outside
  · exact cert_73_a_valid.carrier_outside
  · exact cert_547_a_valid.carrier_outside
  · exact cert_683_a_valid.carrier_outside

end BatchVerification

/-! ## Section 9: The Common Outside Parts

The scan found that the most frequent outside parts appearing as 6-free parts
of the carrier terms include: 11, 61, 17, 121, 341, 73, 547, 683, 3641, 1093.

We verify that all of these are indeed outside ALLOWED. -/

section CommonOutsideParts

/-- The 10 most common outside parts from the support-5 scan. -/
def commonOutsideParts : List ℕ := [11, 61, 17, 121, 341, 73, 547, 683, 3641, 1093]

/-- All common outside parts have an outside carrier. -/
theorem commonOutsideParts_are_outside : ∀ n ∈ commonOutsideParts, HasOutsideCarrier n := by
  intro n hn
  simp only [commonOutsideParts, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hasOutsideCarrier_11
  · exact hasOutsideCarrier_61
  · exact hasOutsideCarrier_17
  · exact hasOutsideCarrier_121
  · exact hasOutsideCarrier_341
  · exact hasOutsideCarrier_73
  · exact hasOutsideCarrier_547
  · exact hasOutsideCarrier_683
  · exact hasOutsideCarrier_3641
  · exact hasOutsideCarrier_1093

/-- Prime factorizations of the common outside parts. -/
theorem outside_part_factorizations :
    121 = 11 ^ 2 ∧
    341 = 11 * 31 ∧
    3641 = 11 * 331 := by
  exact ⟨by norm_num, by norm_num, by norm_num⟩

/-- Primality of the prime outside parts. -/
theorem outside_parts_prime :
    Nat.Prime 11 ∧ Nat.Prime 17 ∧ Nat.Prime 61 ∧ Nat.Prime 73 ∧
    Nat.Prime 547 ∧ Nat.Prime 683 ∧ Nat.Prime 1093 := by
  refine ⟨by decide, by decide, by decide, by decide,
    by native_decide, by native_decide, by native_decide⟩

end CommonOutsideParts

/-! ## Section 10: Structural Properties of Carrier-1 Residuals -/

section StructuralProperties

/-- In a carrier-1 residual, the carrier term equals (up to sign) the sum of the
    ALLOWED-smooth terms. This means the carrier value is determined by the smooth
    part of the residual. -/
theorem carrier_determined_by_smooth (c : Carrier1Certificate) (hv : c.IsValid) :
    c.carrierVal = -c.smoothVals.sum := by
  linarith [hv.sum_zero]

/-- A carrier-1 certificate with support 3 has exactly 2 smooth terms. -/
theorem carrier1_support3_shape (c : Carrier1Certificate) (hv : c.IsValid)
    (h3 : c.smoothWeights.length = 2) :
    ∃ a b : ℕ, c.smoothWeights = [a, b] ∧ IsAllowedSmooth a ∧ IsAllowedSmooth b := by
  have ⟨a, b, heq⟩ : ∃ a b, c.smoothWeights = [a, b] := by
    match c.smoothWeights, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  exact ⟨a, b, heq, hv.all_smooth a (heq ▸ .head _),
    hv.all_smooth b (heq ▸ .tail _ (.head _))⟩

/-- A carrier-1 certificate with support 4 has exactly 3 smooth terms. -/
theorem carrier1_support4_shape (c : Carrier1Certificate) (hv : c.IsValid)
    (h4 : c.smoothWeights.length = 3) :
    ∃ a b d : ℕ, c.smoothWeights = [a, b, d] ∧
      IsAllowedSmooth a ∧ IsAllowedSmooth b ∧ IsAllowedSmooth d := by
  have ⟨a, b, d, heq⟩ : ∃ a b d, c.smoothWeights = [a, b, d] := by
    match c.smoothWeights, h4 with
    | [a, b, d], _ => exact ⟨a, b, d, rfl⟩
  exact ⟨a, b, d, heq, hv.all_smooth a (heq ▸ .head _),
    hv.all_smooth b (heq ▸ .tail _ (.head _)),
    hv.all_smooth d (heq ▸ .tail _ (.tail _ (.head _)))⟩

end StructuralProperties

/-! ## Section 11: Conjectural Statements

The following conjectures are **not proved**. They record empirical observations
and guide future work. Each is clearly marked as a conjecture. -/

section Conjectures

/-!
### Conjecture A: Universal Carrier Complexity 1 for Support-5

**Statement**: Every primitive support-5 {2,3}-smooth kernel equation,
after any single p-adic peel (p ∈ {2,3}), produces a residual equation
with carrier complexity at most 1 (relative to ALLOWED = {2,3,5,7,13,19,41,43}).

**Evidence**: 400/400 bad peels in the scan up to MAX_VALUE = 10⁶ have
carrier complexity exactly 1.

**Status**: Empirically supported, not proved. A proof would require
understanding why the merged value (a sum/difference of two {2,3}-smooth terms)
can contribute at most one prime factor outside ALLOWED. This is related to the
arithmetic of 2^a ± 3^b.
-/

/-!
### Conjecture B: Bounded Carrier Descent

**Statement**: Primitive {2,3}-smooth p-adic peels may fail finite cofactor
closure, but they appear to have bounded carrier complexity and decreasing
support/height. This bounded-carrier descent, rather than C₄-closure, is
the plausible route toward subcritical energy counting.

More precisely: iterating p-adic peels on {2,3}-smooth kernel equations,
the carrier complexity of each intermediate residual equation is at most 1.
The total support decreases at each step. After finitely many steps
(bounded by the original support), the equation reduces to a support-3
identity in the {2,3}-smooth base.

**Evidence**: The support-5 scan shows carrier complexity 1 universally.
The support-4 catalogue shows that all 25 cores either stay {2,3}-smooth
(18 cores) or introduce a single C₄-element (7 cores) upon peeling.
Support-3 identities are fully classified.

**Status**: Open conjecture. Would require:
1. Proving carrier complexity ≤ 1 for all supports (not just 5)
2. Proving support decreases at each peel step (known for single peels)
3. Proving that carrier terms from different peel levels don't interact
   to create unbounded carrier complexity in composed peels
-/

/-!
### Conjecture C: Residual Support Distribution

**Observation**: Among the 400 bad support-5 peels:
  - 29 have residual support 3 (carrier + 2 smooth terms)
  - 371 have residual support 4 (carrier + 3 smooth terms)

This means the peeled merged value almost always preserves full support
(support 5 → residual support 4). The rare support-3 cases arise when
two smooth terms happen to cancel during the merge.

**Status**: Descriptive observation, not a conjecture requiring proof.
-/

/-!
### Conjecture D: Carrier Multiplier Concentration

**Observation**: The number of distinct ALLOWED-smooth multipliers that can
multiply a given outside part to produce a valid carrier weight is concentrated:
  - 246 outside parts have exactly 1 multiplier
  - 55 have 5 multipliers
  - 21 have 2 multipliers
  - 12 have 4 multipliers
  - 10 have 3 multipliers

This suggests that most carrier values are "rigid": the outside part essentially
determines the carrier weight. The multiplier count may be controlled by the
number of ALLOWED-smooth solutions to x · p^k = carrier_weight.

**Status**: Descriptive observation. May follow from S-unit equation finiteness
but the exact distribution is not explained.
-/

end Conjectures
