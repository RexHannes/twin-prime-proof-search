import Mathlib

/-!
# BANK C — additive characters and nonzero-frequency orthogonality

This module fixes the additive-character infrastructure used by the whole
consolidation bank and proves the exact finite identities

* complete orthogonality  `∑_{a mod q} e_q(a t) = q · 1_{q ∣ t}`;
* **NZORTH**              `∑_{a mod q, a ≠ 0} e_q(a t) = q · 1_{q ∣ t} − 1`;
* the normalised form     `(1/q) ∑_{a ≠ 0} e_q(a t) = 1_{q ∣ t} − 1/q`;
* **RES_EQ**              `q ∣ m + 2 n̄  ↔  q ∣ m n + 2`  when `n n̄ ≡ 1 (q)`.

Everything here is finite algebra / modular arithmetic.  No analytic bound for
the nonzero-frequency term is proved anywhere, and in particular

```text
UNCENTERED_N1_IS_NOT_FORCED_BY_NONZERO_ORTHOGONALITY
```

is a *ledger* statement: the identity `NZORTH` produces the centering
`1_{q∣t} − 1/q` and nothing more.  No theorem asserting that the uncentered N1
estimate is false is stated here.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-- The additive character `e_q(x) = exp(2πi x / q)`.  For `q = 0` the value is
`1`; all statements below assume `0 < q`. -/
noncomputable def ec (q : ℕ) (x : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) / (q : ℂ))

@[simp] theorem ec_zero (q : ℕ) : ec q 0 = 1 := by simp [ec]

theorem ec_add (q : ℕ) (x y : ℤ) : ec q (x + y) = ec q x * ec q y := by
  unfold ec; rw [← Complex.exp_add]; push_cast; ring_nf

/-- `e_q(x) = 1` exactly when `q ∣ x`. -/
theorem ec_eq_one_iff {q : ℕ} (hq : 0 < q) (x : ℤ) : ec q x = 1 ↔ (q : ℤ) ∣ x := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold ec
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    field_simp at hn
    exact_mod_cast hn
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    field_simp

/-- Additive characters only see the residue class. -/
theorem ec_congr {q : ℕ} (hq : 0 < q) {x y : ℤ} (h : x ≡ y [ZMOD q]) : ec q x = ec q y := by
  have h1 : ec q (x - y) = 1 := (ec_eq_one_iff hq _).mpr (Int.ModEq.dvd h.symm)
  have h2 : ec q (x - y) * ec q y = ec q x := by rw [← ec_add]; ring_nf
  rw [h1, one_mul] at h2
  exact h2.symm

theorem ec_natMul (q : ℕ) (a : ℕ) (t : ℤ) : ec q (a * t) = (ec q t) ^ a := by
  induction a with
  | zero => simp
  | succ k ih => push_cast; rw [add_mul, ec_add, ih, one_mul, pow_succ, mul_comm]

/-- **Complete additive orthogonality.** -/
theorem sum_ec_orthogonality {q : ℕ} (hq : 0 < q) (t : ℤ) :
    ∑ a ∈ Finset.range q, ec q (a * t) = if (q : ℤ) ∣ t then (q : ℂ) else 0 := by
  by_cases h : (q : ℤ) ∣ t
  · simp only [h, if_true]
    have h1 : ∀ a ∈ Finset.range q, ec q (a * t) = 1 :=
      fun a _ => (ec_eq_one_iff hq _).mpr (Dvd.dvd.mul_left h a)
    rw [Finset.sum_congr rfl h1]
    simp
  · simp only [h, if_false]
    have hz : ec q t ≠ 1 := fun hc => h ((ec_eq_one_iff hq t).mp hc)
    have h1 : ∑ a ∈ Finset.range q, ec q (a * t) = ∑ a ∈ Finset.range q, (ec q t) ^ a :=
      Finset.sum_congr rfl (fun a _ => ec_natMul q a t)
    have h2 : (ec q t) ^ q = 1 := by
      rw [← ec_natMul]
      exact (ec_eq_one_iff hq _).mpr ⟨t, rfl⟩
    rw [h1, geom_sum_eq hz, h2]
    simp

/-- **NZORTH.**  `∑_{a mod q, a ≠ 0} e_q(a t) = q · 1_{q ∣ t} − 1`. -/
theorem sum_ec_nonzero {q : ℕ} (hq : 0 < q) (t : ℤ) :
    ∑ a ∈ (Finset.range q).erase 0, ec q (a * t)
      = (if (q : ℤ) ∣ t then (q : ℂ) else 0) - 1 := by
  have h0 : (0 : ℕ) ∈ Finset.range q := Finset.mem_range.mpr hq
  have := Finset.add_sum_erase (Finset.range q) (fun a : ℕ => ec q (a * t)) h0
  rw [sum_ec_orthogonality hq t] at this
  simp only [Nat.cast_zero, zero_mul, ec_zero] at this
  exact eq_sub_of_add_eq' this

/-- **NZORTH, normalised form.**  `(1/q) ∑_{a ≠ 0} e_q(a t) = 1_{q ∣ t} − 1/q`. -/
theorem sum_ec_nonzero_div {q : ℕ} (hq : 0 < q) (t : ℤ) :
    (1 / (q : ℂ)) * ∑ a ∈ (Finset.range q).erase 0, ec q (a * t)
      = (if (q : ℤ) ∣ t then (1 : ℂ) else 0) - 1 / (q : ℂ) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [sum_ec_nonzero hq t]
  split
  · field_simp
  · field_simp
    ring

/-! ## RES_EQ — the shifted residue equivalence -/

/-- **RES_EQ (integer form).**  If `n n̄ ≡ 1 (mod q)` then
`q ∣ m + 2 n̄ ↔ q ∣ m n + 2`. -/
theorem dvd_add_two_inv_iff {q : ℕ} {m n nbar : ℤ} (h : n * nbar ≡ 1 [ZMOD (q : ℤ)]) :
    ((q : ℤ) ∣ m + 2 * nbar) ↔ ((q : ℤ) ∣ m * n + 2) := by
  constructor
  · intro hd
    have h1 : (q : ℤ) ∣ n * (m + 2 * nbar) := hd.mul_left n
    have h2 : n * (m + 2 * nbar) - (m * n + 2) = 2 * (n * nbar - 1) := by ring
    have h3 : (q : ℤ) ∣ (n * nbar - 1) := Int.ModEq.dvd h.symm
    have h4 : (q : ℤ) ∣ n * (m + 2 * nbar) - (m * n + 2) := by
      rw [h2]; exact h3.mul_left 2
    simpa using dvd_sub h1 h4
  · intro hd
    have h1 : (q : ℤ) ∣ nbar * (m * n + 2) := hd.mul_left nbar
    have h2 : nbar * (m * n + 2) - (m + 2 * nbar) = m * (n * nbar - 1) := by ring
    have h3 : (q : ℤ) ∣ (n * nbar - 1) := Int.ModEq.dvd h.symm
    have h4 : (q : ℤ) ∣ nbar * (m * n + 2) - (m + 2 * nbar) := by
      rw [h2]; exact h3.mul_left m
    simpa using dvd_sub h1 h4

/-- **RES_EQ (`ZMod` form).**  For a unit `n` of `ZMod q`,
`m + 2 n⁻¹ = 0 ↔ m n + 2 = 0`. -/
theorem zmod_add_two_inv_iff {q : ℕ} {m n : ZMod q} (hn : IsUnit n) :
    (m + 2 * n⁻¹ = 0) ↔ (m * n + 2 = 0) := by
  obtain ⟨u, rfl⟩ := hn
  have hinv : (u : ZMod q) * (↑u)⁻¹ = 1 := ZMod.mul_inv_of_unit _ ⟨u, rfl⟩
  constructor
  · intro h
    linear_combination (u : ZMod q) * h - 2 * hinv
  · intro h
    linear_combination ((u : ZMod q))⁻¹ * h - m * hinv

end Gate01Consolidation
end TwinPrimeProject
