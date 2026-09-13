/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the complementary-quotient
identities TC1 / TC2 / TC3 and the terminal small-complement lemma  (T5)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

Three exact finite identities, no asymptotics:

* **TC1**  `a(q) = ∑_{m ≤ Q_max / q} λ(qm)/(qm)`;
* **TC2**  `F_top(N) = ∑_m (1/m) ∑_{q₀ < q ≤ Q_max, qm ≤ Q_max} (λ(qm)/q) c_q(N)`;
* **TC3**  `F_top(N) = ∑_{d ≤ Q_max} (λ(d)/d) ∑_{q ∣ d, q > q₀} c_q(N)`.

and the elementary **terminal small-complement implication**

* `q > q₀`, `qm ≤ Q_max`, `Q_max ≤ q₀ R_cut`, `0 < m`  ⇒  `m < R_cut`,

which is the exact statement that terminal Ramanujan modes have a small complementary quotient.
`R_cut` stays a parameter: no `x^{o(1)}` claim is made anywhere.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TerminalSplit

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset

/-! ## 1. TC1 — the complementary-quotient form of the coefficient -/

/-- **TC1**: `a(q) = ∑_{0 < m ≤ Q_max/q} λ(qm)/(qm)` — exact, finite. -/
theorem aCoeff_complementary_quotient (I : Cutoffs) {q : ℕ} (hq : 0 < q) :
    aCoeff I q = ∑ m ∈ Finset.Ioc 0 (I.Qmax / q),
      ((lam I (q * m) : ℤ) : ℚ) / ((q * m : ℕ) : ℚ) := by
  rw [aCoeff_eq_aDiv, aDiv, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun d => d / q) (fun m => q * m) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hd ⊢
    obtain ⟨⟨hd0, hdQ⟩, hdvd⟩ := hd
    refine ⟨Nat.div_pos (Nat.le_of_dvd hd0 hdvd) hq, Nat.div_le_div_right hdQ⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hm ⊢
    obtain ⟨hm0, hmQ⟩ := hm
    refine ⟨⟨by positivity, ?_⟩, Dvd.intro m rfl⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hq).1 hmQ
  · intro d hd
    simp only [Finset.mem_filter] at hd
    exact Nat.mul_div_cancel' hd.2
  · intro m _
    exact Nat.mul_div_cancel_left m hq
  · intro d hd
    simp only [Finset.mem_filter] at hd
    rw [Nat.mul_div_cancel' hd.2]

/-- TC1 with the summation range widened to `(0, Q_max]` and the constraint `qm ≤ Q_max` moved
into the summand: the form used by TC2. -/
theorem aCoeff_sum_over_quotients (I : Cutoffs) {q : ℕ} (hq : 0 < q) :
    aCoeff I q = ∑ m ∈ Finset.Ioc 0 I.Qmax,
      (if q * m ≤ I.Qmax then ((lam I (q * m) : ℤ) : ℚ) / ((q * m : ℕ) : ℚ) else 0) := by
  rw [aCoeff_complementary_quotient I hq, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hm0, hmle⟩
    have h1 : m * q ≤ I.Qmax := (Nat.le_div_iff_mul_le hq).1 hmle
    have h2 : m ≤ m * q := Nat.le_mul_of_pos_right m hq
    exact ⟨⟨hm0, by omega⟩, by rwa [mul_comm]⟩
  · rintro ⟨⟨hm0, -⟩, hqm⟩
    exact ⟨hm0, (Nat.le_div_iff_mul_le hq).2 (by rwa [mul_comm] at hqm)⟩

/-! ## 2. TC2 — the terminal band in complementary-quotient form -/

/-- **TC2**: `F_top(N) = ∑_m (1/m) ∑_{q₀ < q ≤ Q_max, qm ≤ Q_max} (λ(qm)/q) c_q(N)`. -/
theorem Ftop_complementary_quotient (I : Cutoffs) (q0 N : ℕ) :
    Ftop I q0 N = ∑ m ∈ Finset.Ioc 0 I.Qmax, (1 / (m : ℚ)) *
      ∑ q ∈ (Finset.Ioc q0 I.Qmax).filter (fun q => q * m ≤ I.Qmax),
        ((lam I (q * m) : ℤ) : ℚ) / (q : ℚ) * ((ram q N : ℤ) : ℚ) := by
  have h1 : Ftop I q0 N = ∑ q ∈ Finset.Ioc q0 I.Qmax, ∑ m ∈ Finset.Ioc 0 I.Qmax,
      (if q * m ≤ I.Qmax then
        ((lam I (q * m) : ℤ) : ℚ) / ((q * m : ℕ) : ℚ) * ((ram q N : ℤ) : ℚ) else 0) := by
    rw [Ftop]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq0 : 0 < q := by
      have := Finset.mem_Ioc.1 hq
      omega
    rw [aCoeff_sum_over_quotients I hq0, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by split <;> simp
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : 0 < m := (Finset.mem_Ioc.1 hm).1
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm0.ne'
  rw [Finset.mul_sum, ← Finset.sum_filter]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : 0 < q := by
    have := Finset.mem_Ioc.1 (Finset.mem_filter.1 hq).1
    omega
  have hqQ : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq0.ne'
  push_cast
  field_simp

/-! ## 3. TC3 — the large-divisor form -/

/-- For `0 < d ≤ Q_max`, the moduli of the terminal band dividing `d` are exactly the divisors
of `d` exceeding `q₀`. -/
theorem filter_dvd_top {I : Cutoffs} {q0 d : ℕ} (hd : d ∈ Finset.Ioc 0 I.Qmax) :
    (Finset.Ioc q0 I.Qmax).filter (· ∣ d) = d.divisors.filter (fun q => q0 < q) := by
  rw [Finset.mem_Ioc] at hd
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hq0, -⟩, hqd⟩; exact ⟨⟨hqd, by omega⟩, hq0⟩
  · rintro ⟨⟨hqd, -⟩, hq0⟩
    exact ⟨⟨hq0, le_trans (Nat.le_of_dvd hd.1 hqd) hd.2⟩, hqd⟩

/-- **TC3**: `F_top(N) = ∑_{0 < d ≤ Q_max} (λ(d)/d) ∑_{q ∣ d, q > q₀} c_q(N)` — the equivalent
large-divisor form, with the correct finite support restrictions. -/
theorem Ftop_large_divisor (I : Cutoffs) (q0 N : ℕ) :
    Ftop I q0 N = ∑ d ∈ Finset.Ioc 0 I.Qmax, ((lam I d : ℤ) : ℚ) / (d : ℚ) *
      ∑ q ∈ d.divisors.filter (fun q => q0 < q), ((ram q N : ℤ) : ℚ) := by
  have h1 : Ftop I q0 N = ∑ q ∈ Finset.Ioc q0 I.Qmax, ∑ d ∈ Finset.Ioc 0 I.Qmax,
      (if q ∣ d then ((lam I d : ℤ) : ℚ) / (d : ℚ) * ((ram q N : ℤ) : ℚ) else 0) := by
    rw [Ftop]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [aCoeff_eq_aDiv, aDiv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by split <;> simp
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, filter_dvd_top hd, Finset.mul_sum]

/-! ## 4. The terminal small-complement lemma -/

/-- **Terminal small complement** (elementary, cutoff-parametric).  If the cutoff satisfies
`Q_max ≤ q₀ · R_cut` — the integer form of `q₀ = Q_max / R_cut` — then every terminal mode
`q > q₀` with `qm ≤ Q_max` has complementary quotient `m < R_cut`.

`R_cut` is a parameter here: no `R_cut = x^{o(1)}` claim is made. -/
theorem terminal_small_complement {q0 Qmax Rcut q m : ℕ} (hm : 0 < m)
    (hcut : Qmax ≤ q0 * Rcut) (hq : q0 < q) (hqm : q * m ≤ Qmax) : m < Rcut := by
  have h1 : q0 * m < q * m := by
    exact Nat.mul_lt_mul_of_lt_of_le hq (le_refl m) hm
  have h2 : q0 * m < q0 * Rcut := by omega
  exact Nat.lt_of_mul_lt_mul_left h2

/-- The same implication in the exact rational formulation `q₀ = Q_max / R_cut`. -/
theorem terminal_small_complement_rat {q0 Qmax Rcut q m : ℚ} (hq0 : 0 < q0) (hm : 0 < m)
    (hRcut : 0 < Rcut) (hcut : q0 = Qmax / Rcut) (hq : q0 < q) (hqm : q * m ≤ Qmax) :
    m < Rcut := by
  have hQ : Qmax = q0 * Rcut := by rw [hcut]; field_simp
  have h1 : q0 * m < q * m := by nlinarith
  nlinarith

/-- The terminal band of TC2 is supported on complementary quotients `m < R_cut`: the summand
vanishes outside that range.  (Stated pointwise, as the exact support statement.) -/
theorem Ftop_terminal_support {I : Cutoffs} {q0 Rcut q m : ℕ} (hm : 0 < m)
    (hcut : I.Qmax ≤ q0 * Rcut) (hq : q0 < q) (hqm : q * m ≤ I.Qmax) : m < Rcut :=
  terminal_small_complement hm hcut hq hqm

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
