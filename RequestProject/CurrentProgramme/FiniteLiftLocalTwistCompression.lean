import Mathlib
import RequestProject.CurrentProgramme.FiniteLineFourier

/-!
# Gate 1B · finite-lift local-twist compression (append-only delta layer)

`DETLINE-FINITELIFT-LOCAL-TWIST-COMPRESSION45`.

**Everything proved here is an exact finite identity.**  No analytic estimate is
formalised.  In particular the summatory divisor estimate

```
∑_{e ≤ (log X)^B} τ(e) ≪ (log X)^{B + o(1)}
```

is *not* proved: it is exposed as the uninhabited interface
`LocalTwistDivisorSummationInput`.

## Contents

* `ez` — the standard additive character `n ↦ e_k(n)` on `ZMod k`, written on
  integer arguments (this is `ZMod.stdAddChar` composed with `Int.cast`; it is
  *not* a new Fourier library, and the orthogonality used is the repository's
  `FiniteLineFourier.sum_stdAddChar_mul`).
* `additive_indicator` — the exact expansion
  `1_{e ∣ n} = (1/e) ∑_{ν mod e} e_e(ν n)`.
* `localTwist_indicator` — the same with `n = u A s + 2`, i.e. the exact
  congruence indicator `1_{u A s ≡ -2 (mod e)}`.
* `moebius_coprime_indicator` — `1_{gcd(s,e)=1} = ∑_{a ∣ gcd(s,e)} μ(a)`.
* `localTwist_cell_expansion` — the combined exact expansion, whose cells are
  indexed by `(a ∣ e, ν mod e)`.
* `localTwist_cell_card` / `localTwist_cell_normalisation` — the finite
  bookkeeping `#{(ν, a)} = e · τ(e)` and `(1/e) · e · τ(e) = τ(e)`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FiniteLiftLocalTwist

open Finset

/-! ## 1. The integer-argument additive character -/

/-- `ez k n = e_k(n) = exp(2πi n / k)`, realised as the repository's standard
additive character on `ZMod k` evaluated at the reduction of `n`. -/
noncomputable def ez (k : ℕ) [NeZero k] (n : ℤ) : ℂ :=
  ZMod.stdAddChar ((n : ZMod k))

theorem ez_eq_exp (k : ℕ) [NeZero k] (n : ℤ) :
    ez k n = Complex.exp (2 * Real.pi * Complex.I * n / k) := by
  simpa [ez] using ZMod.stdAddChar_coe (N := k) n

theorem ez_add (k : ℕ) [NeZero k] (m n : ℤ) : ez k (m + n) = ez k m * ez k n := by
  simp [ez, Int.cast_add, AddChar.map_add_eq_mul]

@[simp] theorem ez_zero (k : ℕ) [NeZero k] : ez k 0 = 1 := by
  simp [ez]

/-- **Scaling of moduli.**  `e_{q k}(q n) = e_k(n)` for `q ≠ 0`. -/
theorem ez_scale (q k : ℕ) [NeZero q] [NeZero k] [NeZero (q * k)] (n : ℤ) :
    ez (q * k) ((q : ℤ) * n) = ez k n := by
  rw [ez_eq_exp, ez_eq_exp]
  congr 1
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne k)
  push_cast
  field_simp

/-! ## 2. The exact additive indicator -/

/-- **Exact finite Fourier expansion of a congruence indicator.**

`1_{e ∣ n} = (1/e) ∑_{ν mod e} e_e(ν n)`. -/
theorem additive_indicator (e : ℕ) [NeZero e] (n : ℤ) :
    (if (e : ℤ) ∣ n then (1 : ℂ) else 0)
      = ((e : ℂ))⁻¹ * ∑ nu : ZMod e, ez e (nu.val * n) := by
  classical
  have hchar : ∀ nu : ZMod e, ez e (nu.val * n)
      = (ZMod.stdAddChar : AddChar (ZMod e) ℂ) (nu * ((n : ℤ) : ZMod e)) := by
    intro nu
    simp [ez, ZMod.natCast_val, ZMod.cast_id]
  rw [Finset.sum_congr rfl (fun nu _ => hchar nu),
    FiniteLineFourier.sum_stdAddChar_mul (H := e) ((n : ℤ) : ZMod e)]
  have he : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne e)
  by_cases h : ((n : ℤ) : ZMod e) = 0
  · rw [if_pos h, if_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd n e).1 h), inv_mul_cancel₀ he]
  · rw [if_neg h, if_neg (fun hd => h ((ZMod.intCast_zmod_eq_zero_iff_dvd n e).2 hd)),
      mul_zero]

/-- **The local twist.**  `1_{u A s ≡ -2 (mod e)} = (1/e) ∑_{ν mod e} e_e(ν(uAs+2))`. -/
theorem localTwist_indicator (e : ℕ) [NeZero e] (u A s : ℤ) :
    (if (e : ℤ) ∣ (u * A * s + 2) then (1 : ℂ) else 0)
      = ((e : ℂ))⁻¹ * ∑ nu : ZMod e, ez e (nu.val * (u * A * s + 2)) :=
  additive_indicator e (u * A * s + 2)

/-! ## 2b. The instance-free form of the character (used by the companion layer) -/

/-- `ezExp k n = exp(2πi n / k)`, defined for every `k` (with the Lean convention
`n/0 = 0`, so `ezExp 0 n = 1`).  This avoids carrying a `NeZero` instance when
the modulus varies with a summation index. -/
noncomputable def ezExp (k : ℕ) (n : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * n / k)

theorem ez_eq_ezExp (k : ℕ) [NeZero k] (n : ℤ) : ez k n = ezExp k n :=
  ez_eq_exp k n

theorem ezExp_add (k : ℕ) (m n : ℤ) : ezExp k (m + n) = ezExp k m * ezExp k n := by
  rw [ezExp, ezExp, ezExp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e_{qk}(q n) = e_k(n)` for `q ≠ 0`. -/
theorem ezExp_scale_left (q k : ℕ) (n : ℤ) (hq : q ≠ 0) :
    ezExp (q * k) ((q : ℤ) * n) = ezExp k n := by
  rw [ezExp, ezExp]
  congr 1
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    push_cast
    field_simp

/-- `e_{qk}(k n) = e_q(n)` for `k ≠ 0`. -/
theorem ezExp_scale_right (q k : ℕ) (n : ℤ) (hk : k ≠ 0) :
    ezExp (q * k) ((k : ℤ) * n) = ezExp q n := by
  rw [ezExp, ezExp]
  congr 1
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    push_cast
    field_simp

/-- The additive indicator in the instance-free notation. -/
theorem additive_indicator_exp (e : ℕ) [NeZero e] (n : ℤ) :
    (if (e : ℤ) ∣ n then (1 : ℂ) else 0)
      = ((e : ℂ))⁻¹ * ∑ nu : ZMod e, ezExp e (nu.val * n) := by
  rw [additive_indicator e n]
  congr 1
  exact Finset.sum_congr rfl fun nu _ => ez_eq_ezExp e _

/-- Unnormalised orthogonality: `∑_{ν mod e} e_e(ν n) = e · 1_{e ∣ n}`. -/
theorem sum_ezExp (e : ℕ) [NeZero e] (n : ℤ) :
    ∑ nu : ZMod e, ezExp e (nu.val * n) = if (e : ℤ) ∣ n then (e : ℂ) else 0 := by
  have he : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne e)
  have h := additive_indicator_exp e n
  by_cases hd : (e : ℤ) ∣ n
  · rw [if_pos hd] at h ⊢
    field_simp at h
    linear_combination -h
  · rw [if_neg hd] at h ⊢
    have h2 := h.symm
    field_simp at h2
    simpa using h2

/-- Orthogonality over the integer range `0 ≤ b < e` (no `Fintype` instance on a
variable modulus is needed in this form). -/
theorem sum_range_ezExp (e : ℕ) [NeZero e] (n : ℤ) :
    ∑ b ∈ Finset.range e, ezExp e ((b : ℤ) * n) = if (e : ℤ) ∣ n then (e : ℂ) else 0 := by
  have hre : ∑ b ∈ Finset.range e, ezExp e ((b : ℤ) * n)
      = ∑ z : ZMod e, ezExp e ((z.val : ℤ) * n) := by
    refine Finset.sum_nbij' (fun b => (b : ZMod e)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro z _; exact Finset.mem_range.2 (ZMod.val_lt z)
    · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)
    · intro z _; simp [ZMod.natCast_val, ZMod.cast_id]
    · intro a ha; rw [ZMod.val_cast_of_lt (Finset.mem_range.1 ha)]
  rw [hre, sum_ezExp e n]

/-! ## 3. The Möbius coprimality identity -/

/-- **Exact Möbius coprimality identity.**  `1_{n = 1} = ∑_{a ∣ n} μ(a)`; applied
below with `n = gcd(s,e)`. -/
theorem moebius_divisor_sum (n : ℕ) :
    ∑ a ∈ n.divisors, (ArithmeticFunction.moebius a : ℤ) = if n = 1 then 1 else 0 := by
  have h2 := congrArg (fun f => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h2
  exact h2

/-- `1_{gcd(s,e)=1} = ∑_{a ∣ gcd(s,e)} μ(a)`. -/
theorem moebius_coprime_indicator (s e : ℕ) :
    ∑ a ∈ (Nat.gcd s e).divisors, (ArithmeticFunction.moebius a : ℤ)
      = if Nat.gcd s e = 1 then 1 else 0 :=
  moebius_divisor_sum _

/-! ## 4. The compressed local-twist cell expansion -/

/-- **`DETLINE-FINITELIFT-LOCAL-TWIST-COMPRESSION45`, exact expansion.**

The coprimality-restricted congruence indicator expands into cells indexed by a
divisor `a ∣ gcd(s,e)` and a frequency `ν mod e`:

```
1_{gcd(s,e)=1} · 1_{u A s ≡ -2 (mod e)}
  = ∑_{a ∣ gcd(s,e)} μ(a) · (1/e) ∑_{ν mod e} e_e(ν (u A s + 2)).
```

Kernel-proved; purely finite. -/
theorem localTwist_cell_expansion (e : ℕ) [NeZero e] (sN : ℕ) (u A s : ℤ) :
    (if Nat.gcd sN e = 1 then (1 : ℂ) else 0) *
        (if (e : ℤ) ∣ (u * A * s + 2) then (1 : ℂ) else 0)
      = ∑ a ∈ (Nat.gcd sN e).divisors,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            (((e : ℂ))⁻¹ * ∑ nu : ZMod e, ez e (nu.val * (u * A * s + 2))) := by
  classical
  rw [← Finset.sum_mul, ← localTwist_indicator]
  congr 1
  have h := moebius_coprime_indicator sN e
  have : ∑ a ∈ (Nat.gcd sN e).divisors, ((ArithmeticFunction.moebius a : ℤ) : ℂ)
      = ((if Nat.gcd sN e = 1 then (1 : ℤ) else 0 : ℤ) : ℂ) := by
    rw [← h]; push_cast; ring
  rw [this]
  split <;> simp

/-! ## 5. Finite bookkeeping: the cell index set -/

/-- After the substitution `s = a s'`, a local-twist cell at lift `e` is indexed
by a frequency `ν mod e` together with a divisor `a ∣ e`.  The number of such
cells is exactly `e · τ(e)`. -/
theorem localTwist_cell_card (e : ℕ) [NeZero e] :
    ((Finset.univ : Finset (ZMod e)) ×ˢ e.divisors).card = e * e.divisors.card := by
  simp [Finset.card_product, ZMod.card]

/-- The `1/e` from the additive expansion exactly cancels the `e` frequencies,
leaving the divisor count `τ(e)`: `(1/e) · (e · τ(e)) = τ(e)`. -/
theorem localTwist_cell_normalisation (e : ℕ) [NeZero e] :
    ((e : ℚ))⁻¹ * ((Finset.univ : Finset (ZMod e)) ×ˢ e.divisors).card
      = e.divisors.card := by
  have he : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne e)
  rw [localTwist_cell_card]
  push_cast
  field_simp

/-! ## 6. The analytic bookkeeping input (uninhabited) -/

/-- **`LocalTwistDivisorSummationInput` — UNINHABITED.**

The analytic bookkeeping step of the local-twist compression: the divisor sum
over the finite lift range is at most an arbitrary-log factor.  This is *not*
proved here and is never inhabited in this repository; only the exact finite
expansion above is kernel-proved. -/
structure LocalTwistDivisorSummationInput where
  /-- The lift cut-off, e.g. `(log X)^{B_A}`. -/
  liftBound : ℕ
  /-- The declared budget. -/
  budget : ℝ
  /-- The (unproved) summatory estimate `∑_{e ≤ liftBound} τ(e) ≤ budget`. -/
  divisorSum_le :
    (∑ e ∈ Finset.Icc 1 liftBound, (e.divisors.card : ℝ)) ≤ budget

/-- Trivial firewall: the interface asserts a *bound*, not a saving; nothing in
this file supplies one. -/
theorem localTwistDivisorSummationInput_is_an_assumption
    (I : LocalTwistDivisorSummationInput) :
    (∑ e ∈ Finset.Icc 1 I.liftBound, (e.divisors.card : ℝ)) ≤ I.budget :=
  I.divisorSum_le

end FiniteLiftLocalTwist
end CurrentProgramme
end TwinPrimeProject
