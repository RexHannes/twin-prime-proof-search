import Mathlib
import RequestProject.DominantShortEnergy

/-!
# Support-3 Completeness for (2,3)-Smooth Reciprocal Identities

## Main result

Every support-3 reciprocal identity `1/d₁ + 1/d₂ = 1/d₃` among distinct positive
(2,3)-smooth integers belongs to one of three families (Type I, II, III),
up to permutation of the LHS terms.

## Proof structure

The completeness proof reduces to classifying coprime {2,3}-S-unit equations
`x + y = z`, which in turn reduces to finding consecutive {2,3}-smooth pairs.
The key number-theoretic inputs are two Catalan-type lemmas:

1. `3^b + 1 = 2^a` has solutions only `(b,a) ∈ {(0,1), (1,2)}`
2. `2^a + 1 = 3^b` has solutions only `(a,b) ∈ {(1,1), (3,2)}` (for a,b ≥ 1)
-/

open Finset BigOperators

/-! ## Section 1: Catalan-type Lemmas -/

/-
`3^b + 1 = 2^a` has no solution for `b ≥ 2`.
-/
theorem no_pow3_add_one_eq_pow2_of_ge_two (b : ℕ) (hb : 2 ≤ b) (a : ℕ) :
    3 ^ b + 1 ≠ 2 ^ a := by
      by_contra h_contra;
      rcases a with ( _ | _ | _ | _ | a ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
      · grind;
      · linarith [ Nat.pow_le_pow_right ( show 1 ≤ 3 by norm_num ) hb ];
      · grind;
      · have := congr_arg ( · % 8 ) h_contra ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
        rcases Nat.even_or_odd' b with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at this

/-
`2^a + 1 = 3^b` has no solution with `a ≥ 4`.
-/
theorem no_pow2_add_one_eq_pow3_of_ge_four (a : ℕ) (ha : 4 ≤ a) (b : ℕ) :
    2 ^ a + 1 ≠ 3 ^ b := by
      by_contra h_contra;
      rcases a with ( _ | _ | _ | _ | a ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
      have := congr_arg ( · % 16 ) h_contra ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
      rw [ ← Nat.mod_add_div b 4 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt b four_pos; interval_cases b % 4 <;> norm_num at *;
      have := congr_arg ( · % 5 ) h_contra ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
      rw [ ← Nat.mod_add_div a 4 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt a four_pos; interval_cases a % 4 <;> contradiction;

/-
Complete classification: `3^b + 1 = 2^a` iff `(b,a) ∈ {(0,1), (1,2)}`.
-/
theorem pow3_add_one_eq_pow2_complete (a b : ℕ) :
    3 ^ b + 1 = 2 ^ a ↔ (b = 0 ∧ a = 1) ∨ (b = 1 ∧ a = 2) := by
      rcases b with ( _ | _ | b ) <;> rcases a with ( _ | _ | _ | a ) <;> norm_num [ pow_succ' ] at *;
      · bv_omega;
      · lia;
      · grind;
      · exact fun h => no_pow3_add_one_eq_pow2_of_ge_two ( b + 2 ) ( by linarith ) ( a + 3 ) ( by ring_nf at *; linarith )

/-
Complete classification: `2^a + 1 = 3^b` with `a ≥ 1, b ≥ 1`
    iff `(a,b) ∈ {(1,1), (3,2)}`.
-/
theorem pow2_add_one_eq_pow3_complete (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 ^ a + 1 = 3 ^ b ↔ (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 2) := by
      by_cases ha4 : a ≥ 4;
      · exact ⟨ fun h => False.elim <| no_pow2_add_one_eq_pow3_of_ge_four a ha4 b h, fun h => by rcases h with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> trivial ⟩;
      · interval_cases a <;> rcases b with ( _ | _ | _ | _ | b ) <;> norm_num [ Nat.pow_succ' ] at * <;> omega

/-! ## Section 2: Smooth Structure Lemmas -/

/-
A positive {2,3}-smooth integer coprime to 3 is a power of 2.
-/
lemma smooth23_coprime3_is_pow2 (n : ℕ) (hn : 0 < n) (hs : isSmooth 3 n)
    (hc : Nat.Coprime n 3) : ∃ a : ℕ, n = 2 ^ a := by
      have h_prime_factors : ∀ p : ℕ, Nat.Prime p → p ∣ n → p = 2 := by
        intro p pp dp; have := hs p pp dp; interval_cases p <;> simp_all +decide ;
        exact absurd ( Nat.dvd_gcd dp ( dvd_refl 3 ) ) ( by aesop );
      rw [ ← Nat.prod_primeFactorsList hn.ne' ] ; rw [ List.prod_eq_pow_single 2 ] ; aesop;
      exact fun p hp₁ hp₂ => False.elim <| hp₁ <| h_prime_factors p ( Nat.prime_of_mem_primeFactorsList hp₂ ) <| Nat.dvd_of_mem_primeFactorsList hp₂

/-
A positive {2,3}-smooth odd integer is a power of 3.
-/
lemma smooth23_odd_is_pow3 (n : ℕ) (hn : 0 < n) (hs : isSmooth 3 n)
    (hodd : ¬ 2 ∣ n) : ∃ b : ℕ, n = 3 ^ b := by
      have h_prime_factors : ∀ p : ℕ, Nat.Prime p → p ∣ n → p = 3 := by
        intro p pp dp; have := hs p pp dp; interval_cases p <;> simp_all +decide ;
      nth_rw 1 [ ← Nat.prod_primeFactorsList hn.ne', List.prod_eq_pow_single 3 ];
      · exact ⟨ _, rfl ⟩;
      · exact fun p hp₁ hp₂ => False.elim <| hp₁ <| h_prime_factors p ( Nat.prime_of_mem_primeFactorsList hp₂ ) <| Nat.dvd_of_mem_primeFactorsList hp₂

/-! ## Section 3: Consecutive Smooth Pairs -/

/-
The consecutive (2,3)-smooth pairs are exactly {(1,2), (2,3), (3,4), (8,9)}.
-/
theorem consecutive_smooth23_pairs (n : ℕ) (hn : 0 < n)
    (hs_n : isSmooth 3 n) (hs_succ : isSmooth 3 (n + 1)) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 8 := by
      by_cases h_even : Even n;
      · obtain ⟨a, ha⟩ : ∃ a, n = 2^a := by
          apply smooth23_coprime3_is_pow2 n hn hs_n;
          refine' Nat.Coprime.symm ( Nat.prime_three.coprime_iff_not_dvd.mpr _ );
          intro h_div3
          have h_not_div3_succ : ¬3 ∣ (n + 1) := by
            norm_num [ Nat.dvd_add_right h_div3 ];
          obtain ⟨b, hb⟩ : ∃ b : ℕ, n + 1 = 3 ^ b := by
            apply smooth23_odd_is_pow3 (n + 1) (by linarith) hs_succ (by
            simp_all +decide [ ← even_iff_two_dvd, parity_simps ]);
          rcases b with ( _ | _ | b ) <;> simp_all +decide [ Nat.pow_succ' ]
        obtain ⟨b, hb⟩ : ∃ b, n + 1 = 3^b := by
          apply smooth23_odd_is_pow3;
          · positivity;
          · assumption;
          · simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
        rcases a with ( _ | _ | _ | _ | a ) <;> rcases b with ( _ | _ | _ | _ | b ) <;> norm_num [ Nat.pow_succ' ] at * <;> first | omega | simp_all +arith +decide;
        have := congr_arg ( · % 16 ) hb; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
        have := congr_arg ( · % 5 ) hb; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
        rw [ ← Nat.mod_add_div a 4, ← Nat.mod_add_div b 4 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt a four_pos; have := Nat.mod_lt b four_pos; interval_cases a % 4 <;> interval_cases b % 4 <;> contradiction;
      · obtain ⟨b, hb⟩ : ∃ b : ℕ, n = 3 ^ b := by
          apply smooth23_odd_is_pow3 n hn hs_n;
          simpa [ ← even_iff_two_dvd ] using h_even;
        obtain ⟨a, ha⟩ : ∃ a : ℕ, n + 1 = 2 ^ a := by
          apply smooth23_coprime3_is_pow2 (n + 1) (by linarith) hs_succ (by
          rcases b with ( _ | _ | b ) <;> simp_all +decide [ Nat.pow_succ' ]);
        have := pow3_add_one_eq_pow2_complete a b; aesop;

/-! ## Section 4: Helper Lemmas for Completeness -/

/-
Every positive {2,3}-smooth integer can be written as 2^a * 3^b.
-/
lemma smooth23_eq_pow2_mul_pow3 (n : ℕ) (hn : 0 < n) (hs : isSmooth 3 n) :
    ∃ a b : ℕ, n = 2 ^ a * 3 ^ b := by
      use n.factorization 2, n.factorization 3;
      conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self hn.ne' ];
      rw [ Finsupp.prod_of_support_subset ];
      case s => exact { 2, 3 };
      · norm_num;
      · intro p hp; have := hs p; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
        interval_cases p <;> simp_all +decide;
      · norm_num

/-
In a coprime sum x + y = z of positive {2,3}-smooth integers,
    one of x or y must equal 1.
-/
lemma coprime_smooth23_sum_has_one (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsx : isSmooth 3 x) (hsy : isSmooth 3 y) (hsz : isSmooth 3 z)
    (hsum : x + y = z) (hcop : Nat.gcd x y = 1) :
    x = 1 ∨ y = 1 := by
      obtain ⟨a, b, hx⟩ : ∃ a b : ℕ, x = 2 ^ a * 3 ^ b :=
        smooth23_eq_pow2_mul_pow3 x hx hsx
      obtain ⟨c, d, hy⟩ : ∃ c d : ℕ, y = 2 ^ c * 3 ^ d :=
        smooth23_eq_pow2_mul_pow3 y hy hsy
      obtain ⟨e, f, hz⟩ : ∃ e f : ℕ, z = 2 ^ e * 3 ^ f :=
        smooth23_eq_pow2_mul_pow3 z hz hsz
      rcases a with ( _ | a ) <;> rcases c with ( _ | c ) <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
      · cases b <;> cases d <;> aesop;
      · rcases e with ( _ | e ) <;> rcases f with ( _ | f ) <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
        · exact Nat.eq_zero_of_not_pos fun h => by nlinarith [ pow_pos ( show 0 < 3 by decide ) b, pow_pos ( show 0 < 2 by decide ) c, pow_pos ( show 0 < 3 by decide ) d ] ;
        · have := congr_arg ( · % 3 ) hsum; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
          rcases b with ( _ | b ) <;> rcases d with ( _ | d ) <;> norm_num at *;
          · exact absurd ( Nat.dvd_of_mod_eq_zero this ) ( by norm_num [ Nat.Prime.dvd_iff_one_le_factorization, * ] );
          · norm_num [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] at hcop;
        · have := congr_arg ( · % 2 ) hsum; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
        · have := congr_arg ( · % 2 ) hsum; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
      · rcases e with ( _ | e ) <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
        · have := congr_arg ( · % 3 ) hsum ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
          rcases b with ( _ | b ) <;> rcases d with ( _ | d ) <;> rcases f with ( _ | f ) <;> norm_num at *;
          · grind;
          · exact absurd ( Nat.dvd_of_mod_eq_zero this ) ( by norm_num [ Nat.Prime.dvd_iff_one_le_factorization, * ] );
          · norm_num [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] at hcop;
        · have := congr_arg ( · % 2 ) hsum; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;
      · norm_num [ Nat.gcd_mul_left ] at hcop

/-! ## Section 5: Divisor smoothness -/

/-- A divisor of a smooth number is smooth. -/
lemma isSmooth_of_dvd (y d n : ℕ) (hs : isSmooth y n) (hd : d ∣ n) :
    isSmooth y d := by
  intro p hp hpd
  exact hs p hp (dvd_trans hpd hd)

/-- The gcd of two smooth numbers is smooth. -/
lemma isSmooth_gcd (y a b : ℕ) (ha : isSmooth y a) :
    isSmooth y (Nat.gcd a b) :=
  isSmooth_of_dvd y _ a ha (Nat.gcd_dvd_left a b)

/-! ## Section 6: Denominator clearing -/

/-- Clearing denominators in `1/d₁ + 1/d₂ = 1/d₃`. -/
lemma recip_identity_clearing (d₁ d₂ d₃ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hid : (1 : ℚ) / d₁ + 1 / d₂ = 1 / d₃) :
    d₃ * (d₁ + d₂) = d₁ * d₂ := by
  have h1 : (d₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : (d₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h3 : (d₃ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (d₃ : ℚ) * (d₁ + d₂) = d₁ * d₂ := by field_simp at hid; linarith
  exact_mod_cast key

/-! ## Section 7: Coprime reduction -/

/-
From the cleared-denominator equation with coprime reduction.
    If `d₁ = g*a, d₂ = g*b` with `gcd(a,b)=1` and `d₃*(a+b) = g*a*b`,
    then `a*b ∣ d₃` and `(a+b) ∣ g`.
-/
lemma coprime_sum_dvd_of_coprime (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    Nat.Coprime (a * b) (a + b) := by
  simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.Coprime, Nat.gcd_comm ]

/-
Main parametric reduction: from `1/d₁ + 1/d₂ = 1/d₃` with positive naturals,
    extract coprime `a, b` with `a + b` smooth.
-/
lemma recip_identity_coprime_reduction (d₁ d₂ d₃ : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hid : (1 : ℚ) / d₁ + 1 / d₂ = 1 / d₃) :
    ∃ (g a b : ℕ), 0 < g ∧ 0 < a ∧ 0 < b ∧
      Nat.Coprime a b ∧
      d₁ = g * a * (a + b) ∧ d₂ = g * b * (a + b) ∧ d₃ = g * a * b := by
  obtain ⟨g, a, b, ha, hb, hab⟩ : ∃ g a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ d₁ = g * a ∧ d₂ = g * b := by
    exact ⟨ Nat.gcd d₁ d₂, d₁ / Nat.gcd d₁ d₂, d₂ / Nat.gcd d₁ d₂, Nat.div_pos ( Nat.le_of_dvd hd₁ ( Nat.gcd_dvd_left _ _ ) ) ( Nat.gcd_pos_of_pos_left _ hd₁ ), Nat.div_pos ( Nat.le_of_dvd hd₂ ( Nat.gcd_dvd_right _ _ ) ) ( Nat.gcd_pos_of_pos_right _ hd₂ ), by rw [ Nat.Coprime, Nat.gcd_div ( Nat.gcd_dvd_left _ _ ) ( Nat.gcd_dvd_right _ _ ), Nat.div_self ( Nat.gcd_pos_of_pos_left _ hd₁ ) ], by rw [ Nat.mul_div_cancel' ( Nat.gcd_dvd_left _ _ ) ], by rw [ Nat.mul_div_cancel' ( Nat.gcd_dvd_right _ _ ) ] ⟩;
  -- From `recip_identity_clearing`, we have $d₃ * (d₁ + d₂) = d₁ * d₂$, which gives $d₃ * g * (a + b) = g^2 * a * b$, so $d₃ * (a + b) = g * a * b$.
  have h_eq : d₃ * (a + b) = g * a * b := by
    field_simp at hid;
    norm_cast at hid; rw [ hab.2.1, hab.2.2 ] at hid; nlinarith;
  -- Since $a$ and $b$ are coprime, $a*b$ divides $d₃$. Let $g' = d₃ / (a*b)$.
  obtain ⟨g', hg'⟩ : ∃ g' : ℕ, d₃ = g' * a * b := by
    have h_div : a * b ∣ d₃ := by
      have h_coprime : Nat.Coprime (a * b) (a + b) := by
        simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.Coprime, Nat.gcd_comm ];
      exact h_coprime.dvd_of_dvd_mul_right ⟨ g, by linarith ⟩;
    simpa only [ mul_assoc ] using dvd_iff_exists_eq_mul_left.mp h_div;
  exact ⟨ g', a, b, Nat.pos_of_ne_zero ( by aesop_cat ), ha, hb, hab.1, by nlinarith [ mul_pos ha hb ], by nlinarith [ mul_pos ha hb ], hg' ⟩

/-! ## Section 8: Support-3 Completeness -/

/-
**Support-3 Completeness Theorem.**

Every support-3 reciprocal identity among distinct positive (2,3)-smooth integers
belongs to one of three families (up to permutation of LHS terms):

- **Type I** (from `1 + 2 = 3`): `1/(2^(a-1)·3^b) + 1/(2^a·3^b) = 1/(2^a·3^(b-1))`
- **Type II** (from `1 + 3 = 4`): `1/(2^a·3^(b-1)) + 1/(2^a·3^b) = 1/(2^(a-2)·3^b)`
- **Type III** (from `1 + 8 = 9`): `1/(2^a·3^b) + 1/(2^(a-3)·3^b) = 1/(2^a·3^(b-2))`

Reduces to the S-unit classification for {2,3} via denominator clearing.
-/
theorem support3_completeness_of_smooth23
    (d₁ d₂ d₃ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hs₁ : isSmooth 3 d₁) (hs₂ : isSmooth 3 d₂) (hs₃ : isSmooth 3 d₃)
    (hdist₁₂ : d₁ ≠ d₂) (hdist₁₃ : d₁ ≠ d₃) (hdist₂₃ : d₂ ≠ d₃)
    (hid : (1 : ℚ) / d₁ + 1 / d₂ = 1 / d₃) :
    -- Type I (up to LHS permutation)
    (∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      ((d₁ = 2 ^ (a - 1) * 3 ^ b ∧ d₂ = 2 ^ a * 3 ^ b ∧ d₃ = 2 ^ a * 3 ^ (b - 1)) ∨
       (d₂ = 2 ^ (a - 1) * 3 ^ b ∧ d₁ = 2 ^ a * 3 ^ b ∧ d₃ = 2 ^ a * 3 ^ (b - 1)))) ∨
    -- Type II (up to LHS permutation)
    (∃ a b : ℕ, 2 ≤ a ∧ 1 ≤ b ∧
      ((d₁ = 2 ^ a * 3 ^ (b - 1) ∧ d₂ = 2 ^ a * 3 ^ b ∧ d₃ = 2 ^ (a - 2) * 3 ^ b) ∨
       (d₂ = 2 ^ a * 3 ^ (b - 1) ∧ d₁ = 2 ^ a * 3 ^ b ∧ d₃ = 2 ^ (a - 2) * 3 ^ b))) ∨
    -- Type III (up to LHS permutation)
    (∃ a b : ℕ, 3 ≤ a ∧ 2 ≤ b ∧
      ((d₁ = 2 ^ a * 3 ^ b ∧ d₂ = 2 ^ (a - 3) * 3 ^ b ∧ d₃ = 2 ^ a * 3 ^ (b - 2)) ∨
       (d₂ = 2 ^ a * 3 ^ b ∧ d₁ = 2 ^ (a - 3) * 3 ^ b ∧ d₃ = 2 ^ a * 3 ^ (b - 2)))) := by
  obtain ⟨ g, a, b, hg, ha, hb, hab, hd₁, hd₂, hd₃ ⟩ := recip_identity_coprime_reduction d₁ d₂ d₃ hd₁ hd₂ hd₃ ( by simpa using hid );
  -- Apply `coprime_smooth23_sum_has_one` with x=a, y=b, z=a+b. Get a=1 or b=1.
  have h_ab_one : a = 1 ∨ b = 1 := by
    apply coprime_smooth23_sum_has_one a b (a + b) ha hb (by linarith);
    · exact isSmooth_of_dvd 3 a d₁ hs₁ ( hd₁.symm ▸ dvd_mul_of_dvd_left ( dvd_mul_left _ _ ) _ );
    · exact isSmooth_of_dvd 3 b d₂ hs₂ ( hd₂.symm ▸ dvd_mul_of_dvd_left ( dvd_mul_left _ _ ) _ );
    · exact isSmooth_of_dvd _ _ _ hs₁ ( hd₁.symm ▸ dvd_mul_left _ _ );
    · rfl;
    · assumption;
  rcases h_ab_one with ( rfl | rfl ) <;> simp_all +decide;
  · -- Apply `consecutive_smooth23_pairs` to get b ∈ {1,2,3,8}.
    have hb_cases : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 8 := by
      apply consecutive_smooth23_pairs b hb;
      · exact isSmooth_of_dvd 3 b ( g * b ) hs₃ ( dvd_mul_left _ _ );
      · exact isSmooth_of_dvd 3 ( b + 1 ) ( g * ( 1 + b ) ) hs₁ ( by exact ⟨ g, by ring ⟩ );
    rcases hb_cases with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide;
    · -- Use `smooth23_eq_pow2_mul_pow3` on g to write g = 2^α * 3^β.
      obtain ⟨α, β, hg_eq⟩ : ∃ α β : ℕ, g = 2 ^ α * 3 ^ β := by
        apply smooth23_eq_pow2_mul_pow3 g hg (isSmooth_of_dvd 3 g (g * 3) hs₁ (by norm_num));
      refine Or.inl ⟨ α + 1, by linarith, β + 1, by linarith, ?_ ⟩ ; simp +decide [ *, pow_succ', mul_assoc, mul_comm, mul_left_comm ];
    · -- Apply `smooth23_eq_pow2_mul_pow3` to get g = 2^α * 3^β.
      obtain ⟨ α, β, hg_eq ⟩ := smooth23_eq_pow2_mul_pow3 g hg (isSmooth_of_dvd 3 g (g * 3) hs₃ (by norm_num));
      refine Or.inr <| Or.inl ⟨ α + 2, by linarith, β + 1, by linarith, ?_ ⟩ ; simp +decide [ *, pow_succ' ] ; ring_nf ; aesop;
    · -- Use `smooth23_eq_pow2_mul_pow3` on g to write g = 2^α * 3^β.
      obtain ⟨α, β, hg_eq⟩ : ∃ α β : ℕ, g = 2 ^ α * 3 ^ β := by
        apply smooth23_eq_pow2_mul_pow3 g hg (isSmooth_of_dvd 3 g (g * 9) hs₁ (by norm_num));
      refine Or.inr <| Or.inr <| ⟨ α + 3, by linarith, β + 2, by linarith, ?_ ⟩ ; simp +decide [ *, pow_add ] ; ring_nf ; aesop;
  · -- Apply `consecutive_smooth23_pairs` with x=a, y=a+1.
    have h_consecutive : a ∈ ({1, 2, 3, 8} : Set ℕ) := by
      apply consecutive_smooth23_pairs a ha (isSmooth_of_dvd 3 a (g * a) hs₃ (by
      exact dvd_mul_left _ _)) (isSmooth_of_dvd 3 (a + 1) (g * (a + 1)) hs₂ (by
      exact dvd_mul_left _ _));
    rcases h_consecutive with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide;
    · -- Apply `smooth23_eq_pow2_mul_pow3` to get that $g = 2^α * 3^β$.
      obtain ⟨α, β, hg_eq⟩ : ∃ α β : ℕ, g = 2 ^ α * 3 ^ β := by
        have := smooth23_eq_pow2_mul_pow3 g hg ( isSmooth_of_dvd 3 g ( g * 2 * 3 ) hs₁ ( dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _ ) ) ; aesop;
      refine Or.inl ⟨ α + 1, by linarith, β + 1, by linarith, ?_ ⟩ ; simp +decide [ *, pow_succ' ] ; ring_nf ; aesop;
    · -- Since $g$ is a positive integer, we can write $g = 2^a * 3^b$ for some $a, b \geq 0$.
      obtain ⟨a, b, ha, hb⟩ : ∃ a b : ℕ, g = 2 ^ a * 3 ^ b := by
        have := smooth23_eq_pow2_mul_pow3 g hg ( isSmooth_of_dvd 3 g ( g * 3 ) hs₃ ( dvd_mul_right _ _ ) ) ; aesop;
      refine Or.inr <| Or.inl ⟨ a + 2, by linarith, b + 1, by linarith, ?_ ⟩ ; ring_nf ; aesop;
    · -- Use `smooth23_eq_pow2_mul_pow3` on g to write g = 2^α * 3^β.
      obtain ⟨α, β, hg_eq⟩ : ∃ α β : ℕ, g = 2 ^ α * 3 ^ β := by
        have := smooth23_eq_pow2_mul_pow3 g hg ( isSmooth_of_dvd 3 g ( g * 8 * 9 ) hs₁ ( dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _ ) ) ; aesop;
      exact Or.inr <| Or.inr <| ⟨ α + 3, by linarith, β + 2, by linarith, by simp +decide [ hg_eq, pow_add ] ; ring_nf; aesop ⟩