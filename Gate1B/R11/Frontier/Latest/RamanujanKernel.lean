/-
# Gate1B / R11 / Frontier / Latest : the Ramanujan kernel `c_p(v) = p·1_{p|v} − 1`

Append-only module.  **Exact finite algebra only.**  No analytic estimate is proved here and no
open proposition is inhabited.

Contents:

* §1 the exact decomposition of `c_p` into its principal part `p·1_{p|v}` and its constant part
  `−1`, and the exact complete-period vanishing `∑_{v < p t} c_p(v) = 0` (the *negative branch*
  mechanism);
* §2 the exact positive branch `p | v ⇒ v = p w`, as a reindexing identity, together with the
  exact cancellation of the outer `χ(p)` against the conjugate `χ(p)` (`chi_p_cancels`);
* §3 the **capacity firewall** for the frozen-`p` coordinate: freezing `p` replaces the period
  `p` by the composite period `c p ν d`, and a complete-period argument is then *unavailable*
  whenever the retained range is shorter than the period.  This is proved, not assumed:
  `partial_period_sum_not_forced_zero` produces, for every period `P` and every strictly
  shorter range, a `P`-periodic mean-zero function whose partial sum is `1`.
  `range_shorter_than_period_of_exponent` is the exponent comparison in the form used by the
  frontier (period exponent ≈ .69–.711 against a strictly smaller range exponent).
* §4 the source-valid alternative coordinate in which `p` is *not* frozen but remains a
  summation variable: the exact double-counting identity `sum_over_prime_divisor_coordinate`.
-/
import Mathlib

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. The kernel and its complete-period vanishing -/

/-- The Ramanujan-type kernel `c_p(v) = p·1_{p|v} − 1`. -/
def cpKernel (p v : ℕ) : ℤ := if p ∣ v then (p : ℤ) - 1 else -1

/-- **Exact decomposition** of the kernel into principal part and constant part. -/
theorem cpKernel_eq (p v : ℕ) :
    cpKernel p v = (p : ℤ) * (if p ∣ v then 1 else 0) - 1 := by
  unfold cpKernel; split <;> ring

/-- The positive branch of the kernel. -/
theorem cpKernel_of_dvd {p v : ℕ} (h : p ∣ v) : cpKernel p v = (p : ℤ) - 1 := if_pos h

/-- The negative branch of the kernel. -/
theorem cpKernel_of_not_dvd {p v : ℕ} (h : ¬ p ∣ v) : cpKernel p v = -1 := if_neg h

/-- The multiples of `p` below `p t` are exactly the `t` numbers `p·w`, `w < t`. -/
theorem filter_dvd_range_eq_image {p : ℕ} (hp : 0 < p) (t : ℕ) :
    (range (p * t)).filter (fun v => p ∣ v) = (range t).image (fun w => p * w) := by
  ext v
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hv, w, rfl⟩
    exact ⟨w, lt_of_mul_lt_mul_left hv (Nat.zero_le p), rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(Nat.mul_lt_mul_left hp).mpr hw, ⟨w, rfl⟩⟩

/-- There are exactly `t` multiples of `p` below `p t` (for `p > 0`). -/
theorem card_multiples_below {p : ℕ} (hp : 0 < p) (t : ℕ) :
    ((range (p * t)).filter (fun v => p ∣ v)).card = t := by
  rw [filter_dvd_range_eq_image hp t,
    Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left hp hab),
    card_range]

/-- **Complete-period vanishing (negative branch mechanism).**  Over any whole number of periods
the Ramanujan kernel sums to exactly zero. -/
theorem sum_cpKernel_complete_period {p : ℕ} (hp : 0 < p) (t : ℕ) :
    ∑ v ∈ range (p * t), cpKernel p v = 0 := by
  calc ∑ v ∈ range (p * t), cpKernel p v
      = ∑ v ∈ range (p * t), ((p : ℤ) * (if p ∣ v then 1 else 0) - 1) :=
        Finset.sum_congr rfl fun v _ => cpKernel_eq p v
    _ = (p : ℤ) * ∑ v ∈ range (p * t), (if p ∣ v then (1 : ℤ) else 0)
          - ((p * t : ℕ) : ℤ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
    _ = 0 := by rw [Finset.sum_boole, card_multiples_below hp t]; push_cast; ring

/-! ## 2. The positive branch `v = p w` and the exact `χ(p)` cancellation -/

/-- **Positive-branch reindexing.**  On the branch `p | v` one may write `v = p w` exactly. -/
theorem sum_positive_branch {M : Type*} [AddCommMonoid M] {p : ℕ} (hp : 0 < p) (t : ℕ)
    (F : ℕ → M) :
    ∑ v ∈ (range (p * t)).filter (fun v => p ∣ v), F v = ∑ w ∈ range t, F (p * w) := by
  rw [filter_dvd_range_eq_image hp t, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hp hab

/-- **Exact `χ(p)` cancellation on the `p | v` branch.**  Writing `v = p w`, the outer `χ(p)`
produced by complete multiplicativity meets the conjugate `χ(p)` of the dual side, and the two
cancel exactly, because a Dirichlet character takes unimodular values at units. -/
theorem chi_p_cancels {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) {a : ZMod n}
    (ha : IsUnit a) : χ a * (starRingEnd ℂ) (χ a) = 1 := by
  have hnorm : ‖χ a‖ = 1 := by
    rw [DirichletCharacter.toUnitHom_eq_char' χ ha]
    exact DirichletCharacter.unit_norm_eq_one χ _
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, hnorm]
  norm_num

/-- The cancellation in the form used on the positive branch: for a completely multiplicative
character the factor produced by `v = p w` is exactly removed. -/
theorem chi_positive_branch_factor {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) {p : ℕ}
    (hp : IsUnit ((p : ZMod n))) (w : ZMod n) (z : ℂ) :
    (χ ((p : ZMod n)) * χ w) * ((starRingEnd ℂ) (χ ((p : ZMod n))) * z) = χ w * z := by
  have h := chi_p_cancels χ hp
  calc (χ ((p : ZMod n)) * χ w) * ((starRingEnd ℂ) (χ ((p : ZMod n))) * z)
      = (χ ((p : ZMod n)) * (starRingEnd ℂ) (χ ((p : ZMod n)))) * (χ w * z) := by ring
    _ = χ w * z := by rw [h, one_mul]

/-! ## 3. The frozen-`p` capacity firewall -/

/-- The composite period created by freezing the prime `p`: the residue variable then runs
modulo `c · p · ν · d` rather than modulo `p`. -/
def frozenPeriod (c p nu d : ℕ) : ℕ := c * p * nu * d

/-- Freezing `p` only ever *increases* the period. -/
theorem frozenPeriod_ge {c p nu d : ℕ} (hc : 0 < c) (hnu : 0 < nu) (hd : 0 < d) :
    p ≤ frozenPeriod c p nu d := by
  unfold frozenPeriod
  calc p = 1 * p * 1 * 1 := by ring
    _ ≤ c * p * nu * d :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc le_rfl) hnu) hd

/-- **Capacity firewall.**  If the retained range is strictly shorter than the period, the
complete-period argument is unavailable: there is a `P`-periodic function whose sum over a full
period is `0` but whose sum over the retained range is `1`.  So no cancellation can be inferred
from periodicity alone. -/
theorem partial_period_sum_not_forced_zero {P L : ℕ} (hL : 0 < L) (hLP : L < P) :
    ∃ f : ℕ → ℤ,
      (∀ v, f (v + P) = f v) ∧
      (∑ v ∈ range P, f v) = 0 ∧
      (∑ v ∈ range L, f v) ≠ 0 := by
  refine ⟨fun v => (if v % P = 0 then 1 else 0) - (if v % P = L then 1 else 0), ?_, ?_, ?_⟩
  · intro v; simp [Nat.add_mod_right]
  · have hP : 0 < P := lt_trans hL hLP
    have hzero : (range P).filter (fun v => v % P = 0) = {0} := by
      ext v
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hv, h⟩; rwa [Nat.mod_eq_of_lt hv] at h
      · rintro rfl; exact ⟨hP, by simp⟩
    have hL' : (range P).filter (fun v => v % P = L) = {L} := by
      ext v
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hv, h⟩; rwa [Nat.mod_eq_of_lt hv] at h
      · rintro rfl; exact ⟨hLP, Nat.mod_eq_of_lt hLP⟩
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hzero, hL']
    simp
  · have hzero : (range L).filter (fun v => v % P = 0) = {0} := by
      ext v
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hv, h⟩; rwa [Nat.mod_eq_of_lt (lt_trans hv hLP)] at h
      · rintro rfl; exact ⟨hL, by simp⟩
    have hLL : (range L).filter (fun v => v % P = L) = ∅ := by
      ext v
      simp only [mem_filter, mem_range, notMem_empty, iff_false, not_and]
      intro hv
      rw [Nat.mod_eq_of_lt (lt_trans hv hLP)]
      omega
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hzero, hLL]
    simp

/-- The exponent form of the capacity comparison used at the frontier: if the frozen period has
size exponent `a` and the retained range has size exponent `b < a` (in the `x`-scale, `x > 1`),
the range is strictly shorter than the period. -/
theorem range_shorter_than_period_of_exponent {x a b : ℝ} (hx : 1 < x) (hab : b < a) :
    x ^ b < x ^ a := (Real.rpow_lt_rpow_left_iff hx).mpr hab

/-! ## 4. The source-valid alternative coordinate: `p` stays a summation variable -/

/-- **Prime-divisor coordinate.**  Keeping `p` as a summation variable rather than freezing it,
the sum over pairs `(p, v)` with `p | v` is exactly the sum over `v` of its prime-divisor fibre.
No periodicity in a composite modulus is used. -/
theorem sum_over_prime_divisor_coordinate {M : Type*} [AddCommMonoid M] (S P : Finset ℕ)
    (F : ℕ → ℕ → M) :
    ∑ p ∈ P, ∑ v ∈ S.filter (fun v => p ∣ v), F p v
      = ∑ v ∈ S, ∑ p ∈ P.filter (fun p => p ∣ v), F p v := by
  simp only [Finset.sum_filter]
  exact Finset.sum_comm

end Gate1B.R11.Frontier.Latest
