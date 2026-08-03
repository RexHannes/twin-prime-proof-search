import Mathlib

/-!
# Y=3 Shortest Vector Attempt: p-adic Extremal Layer Lemmas

## Overview

This file proves clean local lemmas for signed reciprocal kernel vectors among
`{2,3}`-smooth denominators, establishing that extremal p-adic layers must contain
multiple support elements.

## Mathematical Setup

For a finite collection of {2,3}-smooth positive integers `q₁, ..., qₖ`, each
`qᵢ = 2^{aᵢ} · 3^{bᵢ}`, a **signed kernel vector** is `z : Fin k → ℤ` with
`zᵢ ∈ {-1, 0, 1}` and `∑ zᵢ / qᵢ = 0`.

After clearing denominators by `L = 2^A · 3^B` (where `A = max aᵢ`, `B = max bᵢ`),
this becomes the integer equation `∑ zᵢ · wᵢ = 0` where `wᵢ = 2^{A-aᵢ} · 3^{B-bᵢ}`.

### Stage 1: p-adic extremal cancellation

**2-adic lemma**: The element `qⱼ` with maximal `v₂(qⱼ)` (equivalently, `wⱼ` is odd)
cannot be the only odd-weight support element. At least two support elements must
have odd weight, otherwise the sum is odd and cannot be zero.

**3-adic lemma**: Similarly, the element with maximal `v₃(qⱼ)` (equivalently, `wⱼ`
is coprime to 3) cannot be the only coprime-to-3 support element. The sum of a
single term `±w` coprime to 3 is nonzero mod 3.

## References

These are the "Lemma 1" and "Lemma 2" from the layer-peeling proof sketch in
`EnergyDominanceY3Plan.md`, Section 4 (Recommended Next Attack).
-/

open Finset BigOperators

/-! ## Stage 1: Divisibility Lemmas for Signed Integer Sums -/

section Stage1

/-! ### Definitions -/

/-- A vector `z : Fin k → ℤ` is a **sign vector** if every entry is in `{-1, 0, 1}`. -/
def IsSignVec {k : ℕ} (z : Fin k → ℤ) : Prop :=
  ∀ i, z i = -1 ∨ z i = 0 ∨ z i = 1

/-- The **support** of a sign vector: indices where `z i ≠ 0`. -/
def signSupp {k : ℕ} (z : Fin k → ℤ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => z i ≠ 0)

/-- The **signed weighted sum**: `∑ᵢ zᵢ · wᵢ`. -/
def signedWtSum {k : ℕ} (z : Fin k → ℤ) (w : Fin k → ℕ) : ℤ :=
  ∑ i, z i * (w i : ℤ)

/-- The set of support elements with odd weight. -/
def oddWtSupp {k : ℕ} (z : Fin k → ℤ) (w : Fin k → ℕ) : Finset (Fin k) :=
  (signSupp z).filter (fun i => ¬ 2 ∣ w i)

/-- The set of support elements with weight coprime to 3. -/
def coprime3WtSupp {k : ℕ} (z : Fin k → ℤ) (w : Fin k → ℕ) : Finset (Fin k) :=
  (signSupp z).filter (fun i => ¬ 3 ∣ w i)

/-! ### Auxiliary lemmas -/

/-- A sign vector entry squared is 0 or 1. -/
lemma sign_sq {z : ℤ} (h : z = -1 ∨ z = 0 ∨ z = 1) : z ^ 2 = 0 ∨ z ^ 2 = 1 := by
  rcases h with rfl | rfl | rfl <;> norm_num

/-- A sign vector entry is congruent to its absolute value mod 2. -/
lemma sign_mod2 {z : ℤ} (h : z = -1 ∨ z = 0 ∨ z = 1) :
    z % 2 = 0 ∧ z = 0 ∨ z % 2 = 1 ∧ z ≠ 0 := by
  rcases h with rfl | rfl | rfl <;> norm_num

/-- If z ∈ {-1, 0, 1} and z ≠ 0, then z is odd. -/
lemma sign_odd_of_ne_zero {z : ℤ} (h : z = -1 ∨ z = 0 ∨ z = 1) (hz : z ≠ 0) :
    ¬ (2 : ℤ) ∣ z := by
  rcases h with rfl | rfl | rfl <;> simp_all

/-- If z ∈ {-1, 0, 1} and z ≠ 0, then z is not divisible by 3. -/
lemma sign_not_dvd3_of_ne_zero {z : ℤ} (h : z = -1 ∨ z = 0 ∨ z = 1) (hz : z ≠ 0) :
    ¬ (3 : ℤ) ∣ z := by
  rcases h with rfl | rfl | rfl <;> simp_all [Int.dvd_iff_emod_eq_zero]

/-! ### Stage 1, Lemma 1: 2-adic extremal cancellation -/

/-
**2-adic extremal cancellation (unique odd-weight version)**:

If `z` is a sign vector, `w` has positive entries, `∑ zᵢ · wᵢ = 0`,
and exactly one support element has odd weight, then we have a contradiction.

Proof: modulo 2, each term `zᵢ · wᵢ` with `wᵢ` even vanishes.
The single odd-weight term contributes `zᵢ · (odd) ≡ ±1 ≡ 1 mod 2`,
so the total sum is `≡ 1 mod 2 ≠ 0`.
-/
theorem two_adic_extremal_unique {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (_hpos : ∀ i, 0 < w i)
    (hker : signedWtSum z w = 0)
    (j : Fin k)
    (hj_supp : z j ≠ 0)
    (hj_odd : ¬ 2 ∣ w j)
    (hothers : ∀ i, i ≠ j → z i ≠ 0 → 2 ∣ w i) :
    False := by
  -- Consider the sum modulo 2.
  have h_mod2 : (∑ i, z i * (w i : ℤ)) % 2 = (∑ i ∈ {j}, z i * (w i : ℤ)) % 2 := by
    rw [ Finset.sum_int_mod, Finset.sum_eq_single_of_mem j ] <;> simp_all +decide [];
    exact fun i hi => if hi' : z i = 0 then by simp +decide [ hi' ] else dvd_mul_of_dvd_right ( mod_cast hothers i hi hi' ) _
  simp_all +decide [ signedWtSum ];
  cases hsign j <;> simp_all +decide [ Int.mul_emod ]; all_goals omega

/-
**2-adic extremal cancellation (cardinality version)**:

If `z` is a sign vector and `∑ zᵢ · wᵢ = 0`, then the number of
support elements with odd weight is even.

This is the quantitative strengthening: the odd-weight support indices
come in pairs.
-/
theorem even_card_oddWtSupp {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0) :
    Even (oddWtSupp z w).card := by
  -- Consider the sum $\sum z_i \cdot w_i$ modulo 2.
  have h_mod : (∑ i, z i * (w i : ℤ)) % 2 = (∑ i ∈ oddWtSupp z w, 1) % 2 := by
    -- For each $i$, $z_i \cdot w_i \equiv 0 \pmod{2}$ if $w_i$ is even or $z_i = 0$, and $z_i \cdot w_i \equiv 1 \pmod{2}$ if $w_i$ is odd and $z_i \neq 0$.
    have h_mod_eq : ∀ i, (z i * (w i : ℤ)) % 2 = if (z i ≠ 0 ∧ ¬ 2 ∣ w i) then 1 else 0 := by
      intro i; rcases hsign i with hi | hi | hi <;> norm_num [ hi ] ;
      · split_ifs <;> norm_cast ; omega;
      · split_ifs <;> norm_cast ; omega;
    simp +decide [ Finset.sum_int_mod, h_mod_eq, oddWtSupp, signSupp ];
    simp +decide [ Finset.filter_filter ];
  simp_all +decide [];
  exact even_iff_two_dvd.mpr ( Int.natCast_dvd_natCast.mp ( Int.dvd_of_emod_eq_zero ( h_mod.symm.trans ( Int.emod_eq_zero_of_dvd <| by exact_mod_cast hker ▸ dvd_zero _ ) ) ) )

/-
Corollary: if there are any support elements with odd weight, there are ≥ 2.
-/
theorem two_le_card_oddWtSupp {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (hne : (oddWtSupp z w).Nonempty) :
    2 ≤ (oddWtSupp z w).card := by
  exact Nat.le_of_dvd ( Finset.card_pos.mpr hne ) ( even_iff_two_dvd.mp ( even_card_oddWtSupp hsign hker ) )

/-! ### Stage 1, Lemma 2: 3-adic extremal cancellation -/

/-
**3-adic extremal cancellation (unique coprime-to-3 version)**:

If `z` is a sign vector, `∑ zᵢ · wᵢ = 0`,
and exactly one support element has weight coprime to 3, then contradiction.

Proof: modulo 3, each term `zᵢ · wᵢ` with `3 ∣ wᵢ` vanishes.
The single coprime-to-3 term contributes `zᵢ · wⱼ ≢ 0 mod 3`
(since `zᵢ ∈ {±1}` and `gcd(wⱼ, 3) = 1`), so the sum is `≢ 0 mod 3`.
-/
theorem three_adic_extremal_unique {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (_hpos : ∀ i, 0 < w i)
    (hker : signedWtSum z w = 0)
    (j : Fin k)
    (hj_supp : z j ≠ 0)
    (hj_cop : ¬ 3 ∣ w j)
    (hothers : ∀ i, i ≠ j → z i ≠ 0 → 3 ∣ w i) :
    False := by
  contrapose! hker; simp_all +decide [] ;
  -- Consider the sum modulo 3.
  have h_mod : (∑ i, z i * (w i : ℤ)) % 3 = z j * (w j : ℤ) % 3 := by
    rw [ Finset.sum_int_mod, Finset.sum_eq_single j ] <;> simp_all +decide [ Int.mul_emod ];
    intro i hi; specialize hothers i hi; by_cases hi' : z i = 0 <;> simp_all +decide [] ;
    norm_cast; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
  exact fun h => absurd ( Int.dvd_of_emod_eq_zero ( h_mod.symm.trans ( Int.emod_eq_zero_of_dvd <| by rw [ show signedWtSum z w = ∑ i, z i * ( w i : ℤ ) by rfl ] at h; exact h.symm ▸ dvd_zero _ ) ) ) ( by exact fun h' => hj_cop <| Int.natCast_dvd_natCast.mp <| Or.resolve_left ( Int.Prime.dvd_mul' ( by decide ) h' ) ( by have := hsign j; rcases this with h|h|h <;> aesop ) )

/-
Corollary: if there are any support elements with weight coprime to 3,
    there are ≥ 2.
-/
theorem two_le_card_coprime3WtSupp {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (hne : (coprime3WtSupp z w).Nonempty) :
    2 ≤ (coprime3WtSupp z w).card := by
  contrapose! hker; interval_cases _ : Finset.card ( coprime3WtSupp z w ) <;> simp_all +decide ;
  obtain ⟨ j, hj ⟩ := Finset.card_eq_one.mp ‹_›; simp_all +decide [ coprime3WtSupp ] ;
  simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
  -- Since $j$ is the only element in the support with weight coprime to 3, we have $z_j \cdot w_j \equiv \pm w_j \pmod{3}$.
  have h_mod3 : ∑ i, z i * w i ≡ z j * w j [ZMOD 3] := by
    have h_mod3 : ∀ i, i ≠ j → z i * w i ≡ 0 [ZMOD 3] := by
      intro i hi; by_cases hi' : z i = 0 <;> simp_all +decide [ Int.ModEq ] ;
      exact dvd_mul_of_dvd_right ( Int.natCast_dvd_natCast.mpr ( Classical.not_not.mp fun h => hi <| hj.2 i ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hi' ⟩ ) h ) ) _;
    simpa [ Int.modEq_iff_dvd ] using Finset.dvd_sum fun i ( hi : i ∈ Finset.univ.erase j ) => Int.modEq_iff_dvd.mp ( h_mod3 i ( Finset.ne_of_mem_erase hi ) );
  -- Since $z_j \cdot w_j \equiv \pm w_j \pmod{3}$ and $w_j$ is not divisible by 3, we have $z_j \cdot w_j \not\equiv 0 \pmod{3}$.
  have h_not_zero_mod3 : ¬(z j * w j ≡ 0 [ZMOD 3]) := by
    have := hsign j; rcases this with ( h | h | h ) <;> simp_all +decide [ Int.ModEq ] ;
    · exact_mod_cast hj.1.2;
    · exact absurd h ( by simpa [ h ] using Finset.mem_filter.mp hj.1.1 |>.2 );
    · exact_mod_cast hj.1.2;
  exact fun h => h_not_zero_mod3 <| h_mod3.symm.trans <| h.symm ▸ rfl

/-! ### Application to {2,3}-smooth denominators -/

/-- A positive natural number is `{2,3}`-smooth if its only prime factors are 2 and 3. -/
def isSmooth23 (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3

/-
For {2,3}-smooth positive integers, the LCM weight `L / q` can be computed
    from the exponent differences. Each weight `wᵢ = 2^{A - aᵢ} · 3^{B - bᵢ}`.
-/
theorem smooth23_weight_form (a b A B : ℕ) (ha : a ≤ A) (hb : b ≤ B) :
    2 ^ A * 3 ^ B / (2 ^ a * 3 ^ b) = 2 ^ (A - a) * 3 ^ (B - b) := by
  exact Nat.div_eq_of_eq_mul_left ( by positivity ) ( by rw [ show 2 ^ A * 3 ^ B = ( 2 ^ ( A - a ) * 3 ^ ( B - b ) ) * ( 2 ^ a * 3 ^ b ) by rw [ show 2 ^ A = 2 ^ ( A - a ) * 2 ^ a by rw [ ← pow_add, Nat.sub_add_cancel ha ], show 3 ^ B = 3 ^ ( B - b ) * 3 ^ b by rw [ ← pow_add, Nat.sub_add_cancel hb ] ] ; ring ] )

/-
For {2,3}-smooth denominators, the element with maximal `v₂` has odd weight
    (since `A - a = 0` means `2^0 = 1` divides the weight but no higher power of 2).
-/
theorem maximal_v2_gives_odd_weight (B b : ℕ) (_hb : b ≤ B) :
    ¬ 2 ∣ (2 ^ 0 * 3 ^ (B - b)) := by
  norm_num [ ← even_iff_two_dvd, parity_simps ]

/-
For {2,3}-smooth denominators, the element with maximal `v₃` has weight
    coprime to 3 (since `B - b = 0` means `3^0 = 1`).
-/
theorem maximal_v3_gives_coprime3_weight (A a : ℕ) (_ha : a ≤ A) :
    ¬ 3 ∣ (2 ^ (A - a) * 3 ^ 0) := by
  norm_num [ Nat.Prime.dvd_iff_one_le_factorization ]

/-
**Main 2-adic corollary for {2,3}-smooth denominators**:

In a nonzero signed kernel vector among {2,3}-smooth denominators,
at least two support elements share the maximal `v₂` value.

Formally: if `qᵢ = 2^{aᵢ} · 3^{bᵢ}` and we set `wᵢ = 2^{A-aᵢ} · 3^{B-bᵢ}`
(the cleared-denominator weights), then among support elements, the ones with
`aᵢ = A` (equivalently `wᵢ` odd) number at least 2.
-/
theorem smooth23_two_adic_extremal {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    {a b : Fin k → ℕ} {A B : ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (_hsupp : (signSupp z).Nonempty)
    (hw : ∀ i, w i = 2 ^ (A - a i) * 3 ^ (B - b i))
    (hA : ∀ i, a i ≤ A)
    (_hB : ∀ i, b i ≤ B)
    (hmax : ∃ j ∈ signSupp z, a j = A) :
    ∃ j₁ j₂ : Fin k, j₁ ≠ j₂ ∧ z j₁ ≠ 0 ∧ z j₂ ≠ 0 ∧ a j₁ = A ∧ a j₂ = A := by
  -- Apply two_le_card_oddWtSupp to get card ≥ 2.
  have h_card : 2 ≤ (oddWtSupp z w).card := by
    apply two_le_card_oddWtSupp hsign hker;
    obtain ⟨ j, hj₁, hj₂ ⟩ := hmax;
    exact ⟨ j, Finset.mem_filter.mpr ⟨ hj₁, by simp +decide [ *, Nat.Prime.dvd_iff_one_le_factorization ] ⟩ ⟩;
  obtain ⟨ j₁, hj₁, j₂, hj₂, hne ⟩ := Finset.one_lt_card.mp h_card; use j₁, j₂; simp_all +decide [ oddWtSupp, signSupp ] ;
  cases h : A - a j₁ <;> cases h' : A - a j₂ <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod ];
  grind +qlia

/-
**Main 3-adic corollary for {2,3}-smooth denominators**:

In a nonzero signed kernel vector among {2,3}-smooth denominators,
at least two support elements share the maximal `v₃` value.
-/
theorem smooth23_three_adic_extremal {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    {a b : Fin k → ℕ} {A B : ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (_hsupp : (signSupp z).Nonempty)
    (hw : ∀ i, w i = 2 ^ (A - a i) * 3 ^ (B - b i))
    (_hA : ∀ i, a i ≤ A)
    (hB : ∀ i, b i ≤ B)
    (hmax : ∃ j ∈ signSupp z, b j = B) :
    ∃ j₁ j₂ : Fin k, j₁ ≠ j₂ ∧ z j₁ ≠ 0 ∧ z j₂ ≠ 0 ∧ b j₁ = B ∧ b j₂ = B := by
  -- By two_le_card_coprime3WtSupp, the set of support elements with weight coprime to 3 has cardinality at least 2.
  have hcard : 2 ≤ (coprime3WtSupp z w).card := by
    apply two_le_card_coprime3WtSupp;
    · assumption;
    · exact hker;
    · obtain ⟨ j, hj₁, hj₂ ⟩ := hmax; use j; simp_all +decide [ coprime3WtSupp ] ;
      exact mt ( Nat.prime_three.dvd_of_dvd_pow ) ( by norm_num );
  obtain ⟨ j₁, hj₁, j₂, hj₂, hne ⟩ := Finset.one_lt_card.mp hcard; use j₁, j₂; simp_all +decide [ coprime3WtSupp ] ;
  simp_all +decide [ Nat.Prime.dvd_iff_one_le_factorization, signSupp ];
  exact ⟨ by linarith [ Nat.sub_add_cancel ( hB j₁ ) ], by linarith [ Nat.sub_add_cancel ( hB j₂ ) ] ⟩

end Stage1

/-! ## Stage 2: Restricted Short-Vector Extraction

**Status**: Attempted but requires Stage 1 lemmas plus substantial case analysis.
See `GrowthQ/Y3ShortestVectorAttempt_REPORT.md` for details.
-/