/-
# Gate1B / R11 / Frontier : the squarefull core decomposition

Append-only module of the minimal-gap-kernel delta.

For a positive `M` we define its **full squarefull part**

```
SqFull(M) = ∏_{p^v ‖ M, v ≥ 2} p^v
```

and the complementary squarefree part `sqFreeCore M`, and we kernel-prove the *unique*
decomposition

```
M = b · a,   b = SqFull(M),   a squarefree,   gcd(a,b) = 1.
```

Two firewalls are kernel-proved as well:

* `SqFull(M)` is **not** `M / rad M`;
* `SqFull(M)` need **not** be a square.
-/
import Gate1B.R11.Frontier.CompleteDivisorFibre

namespace Gate1B.R11.Frontier

open Finset

/-! ## 0. A factorisation helper -/

/-- The factorisation of an explicit product of prime powers. -/
theorem factorization_prod_prime_pow {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) (q : ℕ) :
    (∏ p ∈ S, p ^ e p).factorization q = if q ∈ S then e q else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hS p hp).ne_zero),
    Finsupp.finset_sum_apply]
  have hterm : ∀ p ∈ S, (p ^ e p).factorization q = if p = q then e p else 0 := by
    intro p hp
    rw [Nat.Prime.factorization_pow (hS p hp), Finsupp.single_apply]
  rw [Finset.sum_congr rfl hterm]
  by_cases hq : q ∈ S
  · rw [if_pos hq, Finset.sum_eq_single q]
    · simp
    · intro b _ hbq; simp [hbq]
    · intro h; exact absurd hq h
  · rw [if_neg hq]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpq : p ≠ q := fun h => hq (h ▸ hp)
    simp [hpq]

theorem prod_primeFactors_pow_factorization {M : ℕ} (hM : M ≠ 0) :
    ∏ p ∈ M.primeFactors, p ^ M.factorization p = M := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hM]
  rw [Nat.prod_factorization_eq_prod_primeFactors]

/-! ## 1. Definitions -/

/-- The full squarefull part `SqFull(M) = ∏_{p^v ‖ M, v ≥ 2} p^v`. -/
def sqFullPart (M : ℕ) : ℕ :=
  ∏ p ∈ M.primeFactors with 2 ≤ M.factorization p, p ^ M.factorization p

/-- The complementary squarefree part `∏_{p ‖ M} p`. -/
def sqFreeCore (M : ℕ) : ℕ :=
  ∏ p ∈ M.primeFactors with ¬ (2 ≤ M.factorization p), p ^ M.factorization p

/-- Being squarefull: every prime divisor occurs to order at least two. -/
def IsSquarefull (b : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ b → p ^ 2 ∣ b

/-! ## 2. The decomposition -/

theorem sqFullPart_mul_sqFreeCore {M : ℕ} (hM : M ≠ 0) :
    sqFullPart M * sqFreeCore M = M := by
  rw [sqFullPart, sqFreeCore, Finset.prod_filter_mul_prod_filter_not]
  exact prod_primeFactors_pow_factorization hM

theorem sqFullPart_dvd (M : ℕ) : sqFullPart M ∣ M := by
  rcases eq_or_ne M 0 with rfl | hM
  · exact dvd_zero _
  · exact ⟨sqFreeCore M, (sqFullPart_mul_sqFreeCore hM).symm⟩

theorem sqFullPart_ne_zero (M : ℕ) : sqFullPart M ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hp => pow_ne_zero _
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).ne_zero

theorem sqFreeCore_ne_zero (M : ℕ) : sqFreeCore M ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hp => pow_ne_zero _
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).ne_zero

/-- The factorisation of the squarefull part. -/
theorem factorization_sqFullPart (M q : ℕ) :
    (sqFullPart M).factorization q =
      if q ∈ M.primeFactors ∧ 2 ≤ M.factorization q then M.factorization q else 0 := by
  classical
  rw [sqFullPart, factorization_prod_prime_pow
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)]
  by_cases h : q ∈ M.primeFactors ∧ 2 ≤ M.factorization q
  · rw [if_pos (Finset.mem_filter.2 ⟨h.1, h.2⟩), if_pos h]
  · rw [if_neg (fun hmem => h ⟨(Finset.mem_filter.1 hmem).1, (Finset.mem_filter.1 hmem).2⟩),
      if_neg h]

/-- The factorisation of the squarefree core. -/
theorem factorization_sqFreeCore (M q : ℕ) :
    (sqFreeCore M).factorization q =
      if q ∈ M.primeFactors ∧ ¬ (2 ≤ M.factorization q) then M.factorization q else 0 := by
  classical
  rw [sqFreeCore, factorization_prod_prime_pow
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)]
  by_cases h : q ∈ M.primeFactors ∧ ¬ (2 ≤ M.factorization q)
  · rw [if_pos (Finset.mem_filter.2 ⟨h.1, h.2⟩), if_pos h]
  · rw [if_neg (fun hmem => h ⟨(Finset.mem_filter.1 hmem).1, (Finset.mem_filter.1 hmem).2⟩),
      if_neg h]

theorem squarefree_sqFreeCore (M : ℕ) : Squarefree (sqFreeCore M) := by
  refine (Nat.squarefree_iff_factorization_le_one (sqFreeCore_ne_zero M)).2 fun p => ?_
  rw [factorization_sqFreeCore]
  by_cases h : p ∈ M.primeFactors ∧ ¬ (2 ≤ M.factorization p)
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem isSquarefull_sqFullPart (M : ℕ) : IsSquarefull (sqFullPart M) := by
  intro p hp hdvd
  have h1 : 1 ≤ (sqFullPart M).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp (sqFullPart_ne_zero M)).1 (by simpa using hdvd)
  rw [factorization_sqFullPart] at h1
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp (sqFullPart_ne_zero M),
    factorization_sqFullPart]
  by_cases h : p ∈ M.primeFactors ∧ 2 ≤ M.factorization p
  · rw [if_pos h]; exact h.2
  · rw [if_neg h] at h1; omega

theorem coprime_sqFullPart_sqFreeCore (M : ℕ) :
    Nat.Coprime (sqFullPart M) (sqFreeCore M) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpb : p ∣ sqFullPart M := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hpa : p ∣ sqFreeCore M := hdvd.trans (Nat.gcd_dvd_right _ _)
  have h1 : 1 ≤ (sqFullPart M).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp (sqFullPart_ne_zero M)).1 (by simpa using hpb)
  have h2 : 1 ≤ (sqFreeCore M).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp (sqFreeCore_ne_zero M)).1 (by simpa using hpa)
  rw [factorization_sqFullPart] at h1
  rw [factorization_sqFreeCore] at h2
  by_cases h : 2 ≤ M.factorization p
  · rw [if_neg (fun hh => hh.2 h)] at h2; omega
  · rw [if_neg (fun hh => h hh.2)] at h1; omega

/-- **Existence** of the squarefull-core decomposition. -/
theorem squarefull_decomposition {M : ℕ} (hM : M ≠ 0) :
    sqFullPart M * sqFreeCore M = M ∧ IsSquarefull (sqFullPart M) ∧
      Squarefree (sqFreeCore M) ∧ Nat.Coprime (sqFreeCore M) (sqFullPart M) :=
  ⟨sqFullPart_mul_sqFreeCore hM, isSquarefull_sqFullPart M, squarefree_sqFreeCore M,
    (coprime_sqFullPart_sqFreeCore M).symm⟩

/-! ## 3. Uniqueness -/

/-- **Uniqueness** of the squarefull-core decomposition: any factorisation `M = b·a` with `b`
squarefull, `a` squarefree and `gcd(a,b) = 1` has `b = SqFull(M)` and `a = sqFreeCore M`. -/
theorem squarefull_decomposition_unique {M b a : ℕ} (hM : M ≠ 0) (hEq : b * a = M)
    (hb : IsSquarefull b) (ha : Squarefree a) (hcop : Nat.Coprime a b) :
    b = sqFullPart M ∧ a = sqFreeCore M := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hEq; exact hM hEq.symm
  have ha0 : a ≠ 0 := by rintro rfl; simp at hEq; exact hM hEq.symm
  have hfac : ∀ p : ℕ, M.factorization p = b.factorization p + a.factorization p := by
    intro p; rw [← hEq, Nat.factorization_mul hb0 ha0]; simp
  have hnotboth : ∀ p : ℕ, p.Prime → ¬ (p ∣ b ∧ p ∣ a) := by
    rintro p hp ⟨h1, h2⟩
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h2 h1))
  have hane : ∀ p : ℕ, a.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one ha0).1 ha
  have hbeq : b = sqFullPart M := by
    refine Nat.eq_of_factorization_eq hb0 (sqFullPart_ne_zero M) fun p => ?_
    rw [factorization_sqFullPart]
    by_cases hvb : b.factorization p = 0
    · rw [hvb]
      by_cases h : p ∈ M.primeFactors ∧ 2 ≤ M.factorization p
      · exfalso; have := hfac p; have := hane p; omega
      · rw [if_neg h]
    · have hmem : p ∈ b.primeFactors := by
        rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 hvb
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hmem
      have hva : a.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun h => hnotboth p hpp ⟨hpb, h⟩
      have h2b : 2 ≤ b.factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hpp hb0).1 (hb p hpp hpb)
      have hpM : p ∈ M.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hpp, hpb.trans ⟨a, hEq.symm⟩, hM⟩
      rw [if_pos ⟨hpM, by have := hfac p; omega⟩]
      have := hfac p; omega
  refine ⟨hbeq, ?_⟩
  have hprod := sqFullPart_mul_sqFreeCore hM
  have hbpos : 0 < sqFullPart M := Nat.pos_of_ne_zero (sqFullPart_ne_zero M)
  have h3 : sqFullPart M * a = M := by rw [← hbeq]; exact hEq
  exact Nat.eq_of_mul_eq_mul_left hbpos (h3.trans hprod.symm)

/-! ## 4. Firewalls -/

/-- `8` is squarefull. -/
theorem isSquarefull_eight : IsSquarefull 8 := by
  intro p hp hdvd
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (h8 ▸ hdvd)
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
  subst this; norm_num

theorem sqFullPart_eight : sqFullPart 8 = 8 :=
  (squarefull_decomposition_unique (M := 8) (b := 8) (a := 1) (by norm_num) (by norm_num)
    isSquarefull_eight squarefree_one (Nat.coprime_one_left 8)).1.symm

theorem radNat_eight : radNat 8 = 2 := by
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [radNat, h8, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  simp

/-- `SqFull(M)` is **not** `M / rad M`: at `M = 8` the two differ. -/
theorem sqFullPart_ne_div_radNat : sqFullPart 8 ≠ 8 / radNat 8 := by
  rw [sqFullPart_eight, radNat_eight]
  decide

/-- `SqFull(M)` need **not** be a square: at `M = 8` it equals `8`. -/
theorem sqFullPart_not_square : ¬ ∃ k : ℕ, sqFullPart 8 = k * k := by
  rw [sqFullPart_eight]
  rintro ⟨k, hk⟩
  have hk3 : k ≤ 3 := by nlinarith
  interval_cases k <;> omega

end Gate1B.R11.Frontier
