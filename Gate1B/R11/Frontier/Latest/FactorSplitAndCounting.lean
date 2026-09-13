/-
# Gate1B / R11 / Frontier / Latest : the universal factor split and exact near-diagonal counting

Append-only module.  **Exact deterministic mathematics only.**

* §1 the *universal window split*: any integer all of whose prime factors are `≤ B` has a divisor
  in every window `[A, A·B]` with `1 ≤ A ≤ n`.  This is the greedy/minimal-divisor argument, and
  it is proved here in full.
* §2 its frontier specialisation, the **universal 3/7 – 4/7 split**: if every prime factor of `n`
  is at most `n^{1/7}`, then `n` has a divisor `d` with `n^{3/7} ≤ d ≤ n^{4/7}`.
* §3 exact near-diagonal counting: the number of elements of a range in a fixed residue class,
  and the number of moduli in a range dividing a fixed integer (divisor-bounded, no analytic
  input).
-/
import Mathlib

namespace Gate1B.R11.Frontier.Latest

open Finset Classical

/-! ## 1. The universal window split -/

/-- **Universal window split.**  If every prime factor of `n ≥ 1` is at most `B`, then for every
window base `A` with `1 ≤ A ≤ n` there is a divisor of `n` in `[A, A·B]`.

The proof is the minimal-divisor (greedy) argument: take the least divisor `d ≥ A`; if `d > A·B`
then dividing `d` by its least prime factor `p ≤ B` produces a smaller divisor, which must be
`< A` by minimality, whence `d < A·B` — a contradiction. -/
theorem exists_divisor_in_window {n : ℕ} (hn : 0 < n) {A B : ℝ} (hA1 : 1 ≤ A) (hB1 : 1 ≤ B)
    (hAn : A ≤ (n : ℝ)) (hB : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ B) :
    ∃ d : ℕ, d ∣ n ∧ A ≤ (d : ℝ) ∧ (d : ℝ) ≤ A * B := by
  classical
  set T : Finset ℕ := n.divisors.filter (fun d => A ≤ (d : ℝ)) with hT
  have hnT : n ∈ T := by
    simp only [hT, mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_rfl, hn.ne'⟩, hAn⟩
  have hTne : T.Nonempty := ⟨n, hnT⟩
  set d := T.min' hTne with hd
  have hdT : d ∈ T := T.min'_mem hTne
  have hdvd : d ∣ n := (Nat.mem_divisors.mp (mem_filter.mp hdT).1).1
  have hdA : A ≤ (d : ℝ) := (mem_filter.mp hdT).2
  refine ⟨d, hdvd, hdA, ?_⟩
  by_contra hcon
  push_neg at hcon
  -- `d ≥ 2`, so it has a least prime factor
  have hd1 : (1 : ℝ) < (d : ℝ) := by nlinarith
  have hdpos : 0 < d := Nat.pos_of_mem_divisors (mem_filter.mp hdT).1
  have hdne1 : d ≠ 1 := by
    intro h; rw [h] at hd1; norm_num at hd1
  set p := d.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime hdne1
  have hpd : p ∣ d := Nat.minFac_dvd d
  have hpB : (p : ℝ) ≤ B := hB p hpp (hpd.trans hdvd)
  set e := d / p with he
  have hde : d = p * e := (Nat.mul_div_cancel' hpd).symm
  have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd hdpos hpd) hpp.pos
  have hedvd : e ∣ n := dvd_trans (Nat.div_dvd_of_dvd hpd) hdvd
  have helt : e < d := by
    have h2 : 2 ≤ p := hpp.two_le
    calc e = 1 * e := (one_mul e).symm
      _ < p * e := by
          exact Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hepos
      _ = d := hde.symm
  -- minimality forces `e < A`
  have heA : (e : ℝ) < A := by
    by_contra hcon2
    push_neg at hcon2
    have : e ∈ T := by
      simp only [hT, mem_filter, Nat.mem_divisors]
      exact ⟨⟨hedvd, hn.ne'⟩, hcon2⟩
    have := T.min'_le e this
    omega
  have : (d : ℝ) < A * B := by
    rw [hde]
    push_cast
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    calc (p : ℝ) * (e : ℝ) < (p : ℝ) * A := by nlinarith
      _ = A * (p : ℝ) := by ring
      _ ≤ A * B := by nlinarith
  linarith

/-! ## 2. The universal 3/7 – 4/7 split -/

/-- **Universal 3/7 – 4/7 split.**  If every prime factor of `n ≥ 1` is at most `n^{1/7}` then
`n` has a divisor `d` with `n^{3/7} ≤ d ≤ n^{4/7}`. -/
theorem universal_three_sevenths_split {n : ℕ} (hn : 1 ≤ n)
    (hB : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 7)) :
    ∃ d : ℕ, d ∣ n ∧ (n : ℝ) ^ ((3 : ℝ) / 7) ≤ (d : ℝ)
      ∧ (d : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 7) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hA1 : (1 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 7) := Real.one_le_rpow hn1 (by norm_num)
  have hB1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 7) := Real.one_le_rpow hn1 (by norm_num)
  have hAn : (n : ℝ) ^ ((3 : ℝ) / 7) ≤ (n : ℝ) := by
    calc (n : ℝ) ^ ((3 : ℝ) / 7) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = (n : ℝ) := Real.rpow_one _
  obtain ⟨d, hdvd, hlow, hhigh⟩ :=
    exists_divisor_in_window (n := n) (by omega) hA1 hB1 hAn hB
  refine ⟨d, hdvd, hlow, ?_⟩
  have hmul : (n : ℝ) ^ ((3 : ℝ) / 7) * (n : ℝ) ^ ((1 : ℝ) / 7) = (n : ℝ) ^ ((4 : ℝ) / 7) := by
    rw [← Real.rpow_add_of_nonneg (by linarith) (by norm_num) (by norm_num)]
    norm_num
  linarith [hhigh, hmul.le, hmul.ge]

/-! ## 3. Exact near-diagonal counting -/

/-- Exact near-diagonal counting: a fixed residue class modulo `g` meets `range M` in at most
`M / g + 1` points.  No analytic input. -/
theorem card_residue_class_le (g a M : ℕ) :
    ((range M).filter (fun m => m % g = a)).card ≤ M / g + 1 := by
  classical
  have hmaps : ∀ m ∈ (range M).filter (fun m => m % g = a), m / g ∈ range (M / g + 1) := by
    intro m hm
    rw [mem_range]
    have hmM : m < M := mem_range.mp (mem_filter.mp hm).1
    have : m / g ≤ M / g := Nat.div_le_div_right hmM.le
    omega
  have hinj : ∀ m₁ ∈ (range M).filter (fun m => m % g = a),
      ∀ m₂ ∈ (range M).filter (fun m => m % g = a), m₁ / g = m₂ / g → m₁ = m₂ := by
    intro m₁ h₁ m₂ h₂ h
    have e₁ : m₁ % g = a := (mem_filter.mp h₁).2
    have e₂ : m₂ % g = a := (mem_filter.mp h₂).2
    calc m₁ = g * (m₁ / g) + m₁ % g := (Nat.div_add_mod m₁ g).symm
      _ = g * (m₂ / g) + m₂ % g := by rw [h, e₁, e₂]
      _ = m₂ := Nat.div_add_mod m₂ g
  calc ((range M).filter (fun m => m % g = a)).card
      ≤ (range (M / g + 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = M / g + 1 := card_range _

/-- The moduli in a range dividing a fixed nonzero integer are divisor-bounded: their number is
at most `τ(k)`.  This is the exact form of the diagonal count used before Poisson. -/
theorem card_divisors_in_range_le {k : ℕ} (hk : k ≠ 0) (Q : ℕ) :
    ((range Q).filter (fun q => q ∣ k)).card ≤ k.divisors.card := by
  classical
  refine Finset.card_le_card ?_
  intro q hq
  rw [mem_filter] at hq
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · exact absurd (Nat.eq_zero_of_zero_dvd hq.2) hk
  · exact Nat.mem_divisors.mpr ⟨hq.2, hk⟩

end Gate1B.R11.Frontier.Latest
