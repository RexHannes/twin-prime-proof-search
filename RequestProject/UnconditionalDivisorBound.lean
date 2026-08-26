import Mathlib

/-!
# The divisor bound, proved unconditionally

The master ledger of this project lists "divisor-bound estimates" among the
*imported analytic theorems* (§14.5 of the original task): statements that were
used as hypotheses/interfaces rather than proved.  This module removes that
import for the basic divisor bound: it contains a complete, hypothesis-free,
kernel-checked proof of

  `∀ ε > 0, ∃ C, ∀ n ≠ 0, τ(n) ≤ C · n^ε`

together with the two forms in which the bank actually uses it:

* `card_divisors_le_mul_rpow` — the ε-form above;
* `card_divisors_in_range_le_mul_rpow` — the count of divisors of `K` lying in
  a dyadic window `q ∼ Q`, bounded by `C · K^ε` (this is the exact counting
  input `#{q ∼ Q : q ∣ mn+2} ≤ τ(mn+2)` of the pre-Poisson diagonal).

No hypothesis beyond `ε > 0` and `n ≠ 0` is used, and nothing here is
conditional on an external analytic input.
-/

namespace ShiftedMobiusBank

open Finset

/-- Pointwise Euler factor bound.  For a prime power `p^a` with `p ≥ 2`,
`a + 1 ≤ g(p) · p^{aε}` where `g(p) = B` when `p^ε < 2` and `g(p) = 1`
otherwise, provided `B ≥ 1` and `B ≥ 2/(ε log 2)`. -/
theorem divisor_euler_factor_le (ε : ℝ) (hε : 0 < ε) (B : ℝ) (hB1 : 1 ≤ B)
    (hB2 : 2 / (ε * Real.log 2) ≤ B) (p a : ℕ) (hp : 2 ≤ p) :
    ((a : ℝ) + 1) ≤ (if ((p : ℝ) ^ ε < 2) then B else 1) * (p : ℝ) ^ ((a : ℝ) * ε) := by
  have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  by_cases h : ((p:ℝ) ^ ε < 2)
  · simp only [h, if_true]
    have key : (2:ℝ) ^ ((a:ℝ) * ε) ≤ (p:ℝ) ^ ((a:ℝ) * ε) :=
      Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    have hexp : Real.log 2 * ((a:ℝ) * ε) + 1 ≤ (2:ℝ) ^ ((a:ℝ) * ε) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      exact Real.add_one_le_exp _
    have ha : (0:ℝ) ≤ (a:ℝ) := by positivity
    have hB2' : 2 ≤ B * (ε * Real.log 2) := by
      rw [div_le_iff₀ (by positivity)] at hB2
      linarith
    nlinarith [mul_le_mul_of_nonneg_left key (le_trans zero_le_one hB1)]
  · simp only [h, if_false, one_mul]
    push_neg at h
    have hrw : (p:ℝ) ^ ((a:ℝ) * ε) = ((p:ℝ) ^ ε) ^ a := by
      rw [mul_comm, Real.rpow_mul hp0, Real.rpow_natCast]
    rw [hrw]
    have h2a : (2:ℝ) ^ a ≤ ((p:ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) h a
    have hstep : ((a:ℝ) + 1) ≤ (2:ℝ) ^ a := by
      have h1 := Nat.lt_two_pow_self (n := a)
      have h2 : (a:ℝ) + 1 ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast h1
      simpa using h2
    linarith

/-- If `p^ε < 2` with `ε > 0`, then `p < 2^{1/ε}`. -/
theorem small_prime_of_rpow_lt_two {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (h : (p : ℝ) ^ ε < 2) : (p : ℝ) < (2:ℝ) ^ (1/ε) := by
  by_contra hcon
  push_neg at hcon
  have h1 : ((2:ℝ) ^ (1/ε)) ^ ε ≤ (p:ℝ) ^ ε :=
    Real.rpow_le_rpow (by positivity) hcon (le_of_lt hε)
  have h2 : ((2:ℝ) ^ (1/ε)) ^ ε = 2 := by
    rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ (ne_of_gt hε),
      Real.rpow_one]
  rw [h2] at h1
  linarith

/-- **The divisor bound, unconditional.**  For every `ε > 0` there is a constant
`C ≥ 1` with `τ(n) ≤ C · n^ε` for all `n ≠ 0`. -/
theorem card_divisors_le_mul_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n:ℝ) ^ ε := by
  set B : ℝ := max 1 (2 / (ε * Real.log 2)) with hBdef
  have hB1 : (1:ℝ) ≤ B := le_max_left _ _
  have hB2 : 2 / (ε * Real.log 2) ≤ B := le_max_right _ _
  have hB0 : (0:ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  set Kn : ℕ := ⌈(2:ℝ) ^ (1/ε)⌉₊ + 1 with hKn
  refine ⟨B ^ Kn, one_le_pow₀ hB1, ?_⟩
  intro n hn
  set S := n.primeFactors with hS
  set f : ℕ → ℕ := fun p => n.factorization p with hf
  have hcard : ((n.divisors.card : ℝ)) = ∏ p ∈ S, ((f p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]
    push_cast
    rfl
  have hnprod : (n:ℝ) = ∏ p ∈ S, (p:ℝ) ^ (f p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod]
    push_cast
    rfl
  have hrpow : (n:ℝ) ^ ε = ∏ p ∈ S, (p:ℝ) ^ ((f p : ℝ) * ε) := by
    rw [hnprod, ← Real.finset_prod_rpow _ _ (fun i _ => by positivity)]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [← Real.rpow_natCast (p:ℝ) (f p), ← Real.rpow_mul (by positivity)]
  -- pointwise comparison
  have hstep : ∏ p ∈ S, ((f p : ℝ) + 1)
      ≤ ∏ p ∈ S, ((if ((p:ℝ) ^ ε < 2) then B else 1) * (p:ℝ) ^ ((f p : ℝ) * ε)) := by
    refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    exact divisor_euler_factor_le ε hε B hB1 hB2 p (f p) hp2
  have hsplit : ∏ p ∈ S, ((if ((p:ℝ) ^ ε < 2) then B else 1) * (p:ℝ) ^ ((f p : ℝ) * ε))
      = (∏ p ∈ S, (if ((p:ℝ) ^ ε < 2) then B else 1)) * (n:ℝ) ^ ε := by
    rw [Finset.prod_mul_distrib, hrpow]
  -- the small-prime product is at most `B ^ Kn`
  have hsmall : (∏ p ∈ S, (if ((p:ℝ) ^ ε < 2) then B else 1)) ≤ B ^ Kn := by
    classical
    have hpe : (∏ p ∈ S, (if ((p:ℝ) ^ ε < 2) then B else 1))
        = B ^ (S.filter (fun p : ℕ => (p:ℝ) ^ ε < 2)).card := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [hpe]
    have hsub : (S.filter (fun p : ℕ => (p:ℝ) ^ ε < 2)) ⊆ Finset.range Kn := by
      intro p hp
      have hlt := small_prime_of_rpow_lt_two hε (Finset.mem_filter.mp hp).2
      have hceil : (p:ℝ) < (⌈(2:ℝ) ^ (1/ε)⌉₊ : ℝ) :=
        lt_of_lt_of_le hlt (Nat.le_ceil _)
      have : p < ⌈(2:ℝ) ^ (1/ε)⌉₊ := by exact_mod_cast hceil
      exact Finset.mem_range.mpr (by omega)
    have hcardle : (S.filter (fun p : ℕ => (p:ℝ) ^ ε < 2)).card ≤ Kn := by
      have h := Finset.card_le_card hsub
      rwa [Finset.card_range] at h
    exact pow_le_pow_right₀ hB1 hcardle
  calc (n.divisors.card : ℝ) = ∏ p ∈ S, ((f p : ℝ) + 1) := hcard
    _ ≤ (∏ p ∈ S, (if ((p:ℝ) ^ ε < 2) then B else 1)) * (n:ℝ) ^ ε := by
        rw [← hsplit]; exact hstep
    _ ≤ (B ^ Kn) * (n:ℝ) ^ ε := by
        have : (0:ℝ) ≤ (n:ℝ) ^ ε := by positivity
        exact mul_le_mul_of_nonneg_right hsmall this

/-- The counting form used by the pre-Poisson diagonal: for any window
`[Q, 2Q)` (indeed any set of integers), the number of divisors of `K ≠ 0`
lying in the window is at most `C · K^ε`. -/
theorem card_divisors_in_range_le_mul_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : ℕ), K ≠ 0 → ∀ (W : Finset ℕ),
      ((W.filter (fun q => q ∣ K)).card : ℝ) ≤ C * (K:ℝ) ^ ε := by
  obtain ⟨C, hC1, hC⟩ := card_divisors_le_mul_rpow ε hε
  refine ⟨C, hC1, fun K hK W => ?_⟩
  have hsub : W.filter (fun q => q ∣ K) ⊆ K.divisors := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨_, hdvd⟩
    exact Nat.mem_divisors.mpr ⟨hdvd, hK⟩
  have : ((W.filter (fun q => q ∣ K)).card : ℝ) ≤ (K.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact this.trans (hC K hK)

/-- The divisor-power bound `τ(n)^A ≤ C · n^ε`, unconditional.  This is the form
in which divisor-bounded coefficients `|α_m| ≤ τ(m)^A` are used. -/
theorem card_divisors_pow_le_mul_rpow (A : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → ((n.divisors.card : ℝ)) ^ A ≤ C * (n:ℝ) ^ ε := by
  obtain ⟨C₀, hC₀, hC⟩ := card_divisors_le_mul_rpow (ε / (A + 1)) (by positivity)
  refine ⟨C₀ ^ A, one_le_pow₀ hC₀, fun n hn => ?_⟩
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    exact_mod_cast this
  have hstep : ((n.divisors.card : ℝ)) ^ A ≤ (C₀ * (n:ℝ) ^ (ε / (A + 1))) ^ A :=
    pow_le_pow_left₀ (by positivity) (hC n hn) A
  have hexp : (C₀ * (n:ℝ) ^ (ε / (A + 1))) ^ A
      = C₀ ^ A * (n:ℝ) ^ ((A : ℝ) * (ε / (A + 1))) := by
    rw [mul_pow, ← Real.rpow_natCast ((n:ℝ) ^ (ε / (A + 1))) A, ← Real.rpow_mul (by positivity),
      mul_comm (ε / (A + 1)) (A:ℝ)]
  have hle : (A : ℝ) * (ε / (A + 1)) ≤ ε := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hε.le, Nat.cast_nonneg (α := ℝ) A]
  have hmono : (n:ℝ) ^ ((A : ℝ) * (ε / (A + 1))) ≤ (n:ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hn1 hle
  calc ((n.divisors.card : ℝ)) ^ A ≤ (C₀ * (n:ℝ) ^ (ε / (A + 1))) ^ A := hstep
    _ = C₀ ^ A * (n:ℝ) ^ ((A : ℝ) * (ε / (A + 1))) := hexp
    _ ≤ C₀ ^ A * (n:ℝ) ^ ε := by
        exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- Unconditional divisor-cost bound for the `m`-diagonal count of the shifted
dispersion square: the total number of incidences `q ∣ mn+2` with `q` in a
window `W`, over `1 ≤ m ≤ M` and `1 ≤ n ≤ N`, is at most `C · M N (MN+2)^ε`.
Only the divisor bound is used; no analytic input. -/
theorem diagonal_divisor_count_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (M N : ℕ) (W : Finset ℕ),
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ((W.filter (fun q => q ∣ (m * n + 2))).card : ℝ)
        ≤ C * (M * N : ℕ) * ((M * N + 2 : ℕ) : ℝ) ^ ε := by
  obtain ⟨C, hC1, hC⟩ := card_divisors_in_range_le_mul_rpow ε hε
  refine ⟨C, hC1, fun M N W => ?_⟩
  have hpt : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 N,
      ((W.filter (fun q => q ∣ (m * n + 2))).card : ℝ)
        ≤ C * ((M * N + 2 : ℕ) : ℝ) ^ ε := by
    intro m hm n hn
    have hmM := (Finset.mem_Icc.mp hm).2
    have hnN := (Finset.mem_Icc.mp hn).2
    have hle : m * n + 2 ≤ M * N + 2 := by
      have : m * n ≤ M * N := Nat.mul_le_mul hmM hnN
      omega
    have hbase : ((m * n + 2 : ℕ) : ℝ) ≤ ((M * N + 2 : ℕ) : ℝ) := by exact_mod_cast hle
    have hmono : ((m * n + 2 : ℕ) : ℝ) ^ ε ≤ ((M * N + 2 : ℕ) : ℝ) ^ ε :=
      Real.rpow_le_rpow (by positivity) hbase hε.le
    refine le_trans (hC (m * n + 2) (by omega) W) ?_
    exact mul_le_mul_of_nonneg_left hmono (le_trans zero_le_one hC1)
  have hstep : ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ((W.filter (fun q => q ∣ (m * n + 2))).card : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, C * ((M * N + 2 : ℕ) : ℝ) ^ ε :=
    Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hpt m hm n hn))
  refine le_trans hstep (le_of_eq ?_)
  rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Nat.card_Icc]
  simp only [nsmul_eq_mul, Nat.add_sub_cancel]
  push_cast
  ring

end ShiftedMobiusBank
