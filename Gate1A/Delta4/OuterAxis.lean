/-
# Gate-1A Δv4 §15 / §16 / §17 — the outer `Z = 0` axis, split correctly

The Δv4 addendum **retracts** the earlier claim

> `Z = 0, L ≠ 0` ⇒ all five local Kloosterman factors are always `-1`.

The correct outer-axis dictionary is

```
S_r(0, L) = -1     if r ∤ L,
S_r(0, L) = r - 1  if r ∣ L,
```

and this file proves exactly that, with the two branches separated:

* `outer_axis_local_factor` — the full dictionary, for a primitive additive
  character on `ZMod r` (`r` prime), with `L : ℤ` and `r ∣ L` decided by
  `ZMod.intCast_zmod_eq_zero_iff_dvd`;
* `outer_axis_not_always_minus_one` — the formal **refutation** of the
  retracted claim: for every prime `r ≥ 3` and every `L` divisible by `r`,
  the outer factor is `r - 1 ≠ -1`;
* `inner_axis_local_factor_neg_one` — for the four `p/q` local factors on the
  recombined support (`p ∤ h`, i.e. `h ≢ 0`), the value is `-1`;
* `outer_regular_axis_contraction` (§16) — on the regular axis `r ∤ L` the
  *normalised* local factor has size `r^{-1/2} < 1`: the one-zero axis is a
  strict contraction in the normalised local Hilbert norm;
* `outer_true_zero_divisor_bound` (§17) — the `r ∣ L` branch is a genuine
  rank/conductor-loss branch and is controlled only by divisor sparsity:
  for fixed `L ≠ 0` the number of primes `r ∣ L` is at most `log₂ |L|`.
-/
import Mathlib
import Gate1A.Kloosterman

namespace Gate1A

namespace Delta4

open Gate1A.Kloosterman

variable {r : ℕ} [Fact (Nat.Prime r)]

/-! ## §15 The exact outer axis dictionary -/

/-- **§15 outer axis dictionary.**  For a primitive additive character of
`ZMod r` (`r` prime) and an integer `L`,

`S_r(0, L) = -1` if `r ∤ L`, and `S_r(0, L) = r - 1` if `r ∣ L`.

The two branches are genuinely different; see
`outer_axis_not_always_minus_one`. -/
theorem outer_axis_local_factor (psi : AddChar (ZMod r) ℂ) (hp : psi.IsPrimitive)
    (L : ℤ) :
    kloosterman psi 0 ((L : ZMod r)) = if (r : ℤ) ∣ L then (r : ℂ) - 1 else -1 := by
  by_cases hdvd : (r : ℤ) ∣ L
  · have hzero : ((L : ZMod r)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd L r).mpr hdvd
    rw [if_pos hdvd, hzero, kloosterman_zero_zero]
  · have hne : ((L : ZMod r)) ≠ 0 := fun hc =>
      hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd L r).mp hc)
    rw [if_neg hdvd, kloosterman_axis_right psi hp hne]

/-- **Refutation of the retracted claim.**  For every prime `r ≥ 3`, every
additive character (primitivity is not even needed here) and every `L`
divisible by `r`, the outer local factor equals `r - 1`, which is **not**
`-1`.  Hence "all five local factors are always `-1` on `Z = 0, L ≠ 0`" is
false: the `r ∣ L` branch is a true local zero vector. -/
theorem outer_axis_not_always_minus_one (psi : AddChar (ZMod r) ℂ)
    (hr3 : 3 ≤ r) {L : ℤ} (hdvd : (r : ℤ) ∣ L) :
    kloosterman psi 0 ((L : ZMod r)) = (r : ℂ) - 1 ∧ ((r : ℂ) - 1 ≠ -1) := by
  have hzero : ((L : ZMod r)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd L r).mpr hdvd
  refine ⟨by rw [hzero, kloosterman_zero_zero], ?_⟩
  intro hc
  have : (r : ℂ) = 0 := by linear_combination hc
  have hr0 : (r : ℕ) = 0 := by exact_mod_cast this
  omega

/-- **§15 inner (`p/q`) axis factors.**  On the recombined support, where the
prime does not divide the relevant `h` (equivalently `h ≢ 0 (mod p)`, the
case `h = 0` being firewalled separately), each of the four `p/q` local
factors equals `-1`. -/
theorem inner_axis_local_factor_neg_one (psi : AddChar (ZMod r) ℂ)
    (hp : psi.IsPrimitive) {h : ℤ} (hdvd : ¬ (r : ℤ) ∣ h) :
    kloosterman psi 0 ((h : ZMod r)) = -1 := by
  have hne : ((h : ZMod r)) ≠ 0 := fun hc =>
    hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd h r).mp hc)
  exact kloosterman_axis_right psi hp hne

/-! ## §16 The regular axis `Z = 0`, `r ∤ L` is a contraction -/

/-- **§16 (`outer_regular_axis_contraction`).**  On the regular one-zero axis
(`Z = 0`, `r ∤ L`) the local factor has modulus exactly `1`; hence the
*normalised* local factor `r^{-1/2} S_r(0,L)` has modulus `r^{-1/2} < 1` for
`r ≥ 2`.  The restriction to the one-zero axis is therefore a strict
contraction in the normalised local Hilbert norm, and the axis contributes at
most its natural (diagonal) mass. -/
theorem outer_regular_axis_contraction (psi : AddChar (ZMod r) ℂ)
    (hp : psi.IsPrimitive) {L : ℤ} (hdvd : ¬ (r : ℤ) ∣ L) :
    ‖kloosterman psi 0 ((L : ZMod r))‖ = 1 ∧
      ‖kloosterman psi 0 ((L : ZMod r))‖ / Real.sqrt r < 1 := by
  have hval := inner_axis_local_factor_neg_one psi hp hdvd
  have hnorm : ‖kloosterman psi 0 ((L : ZMod r))‖ = 1 := by rw [hval]; simp
  refine ⟨hnorm, ?_⟩
  have hr2 : 2 ≤ r := (Fact.out : Nat.Prime r).two_le
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have h1 : (1 : ℝ) < Real.sqrt r := by
    have : Real.sqrt 1 < Real.sqrt r := by
      apply Real.sqrt_lt_sqrt (by norm_num); linarith
    simpa using this
  rw [hnorm, div_lt_one (by linarith)]
  exact h1

/-- The local Plancherel identity behind §16, restated from the banked
Kloosterman layer: `∑_V S_r(U,V) conj S_r(U',V) = r² 1_{U=U'} − r`.  In
particular the total axis mass over all `V` is `r² − r`, so a single axis
state carries at most an `r^{-1}` fraction of it. -/
theorem outer_axis_plancherel (psi : AddChar (ZMod r) ℂ) (hp : psi.IsPrimitive)
    (U U' : ZMod r) :
    (∑ V : ZMod r, kloosterman psi U V * (starRingEnd ℂ) (kloosterman psi U' V))
      = (if U = U' then (r : ℂ) ^ 2 else 0) - (r : ℂ) :=
  kloosterman_local_correlation psi hp U U'

/-! ## §17 The true local zero `r ∣ L`: divisor sparsity -/

/-- **§17 (`outer_true_zero_divisor_bound`).**  The `r ∣ L` branch is sparse:
for a fixed nonzero integer `L`, the number of *distinct primes* dividing `L`
is at most `log₂ |L|`, i.e. `2 ^ ω(|L|) ≤ |L|`.

This is the exact, constant-free form of the addendum's
`#{ r ~ R prime : r ∣ L } ≤ X^{o(1)}`. -/
theorem outer_true_zero_divisor_bound {L : ℤ} (hL : L ≠ 0) :
    2 ^ (L.natAbs.primeFactors.card) ≤ L.natAbs := by
  have hpos : 0 < L.natAbs := Int.natAbs_pos.mpr hL
  have hprod : ∏ p ∈ L.natAbs.primeFactors, p ≤ L.natAbs :=
    Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd _)
  have hle : 2 ^ (L.natAbs.primeFactors.card) ≤ ∏ p ∈ L.natAbs.primeFactors, p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod' ?_
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  exact hle.trans hprod

/-- The `r ∣ L` branch of the outer axis is **not** a generic projective
point: on it the outer local pair is `(Z, L) ≡ (0,0) (mod r)`, and the local
factor is `r - 1`, not `-1`.  This records the routing obligation: the branch
must be sent to the rank-loss / proper-conductor sector (or bounded by
divisor sparsity), never treated as full-conductor generic. -/
theorem outer_true_zero_is_rank_loss (psi : AddChar (ZMod r) ℂ)
    (hr3 : 3 ≤ r) {L : ℤ} (hdvd : (r : ℤ) ∣ L) :
    ((L : ZMod r)) = 0 ∧ kloosterman psi 0 ((L : ZMod r)) ≠ -1 := by
  obtain ⟨hval, hne⟩ := outer_axis_not_always_minus_one psi hr3 hdvd
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd L r).mpr hdvd, by rw [hval]; exact hne⟩

end Delta4

end Gate1A
