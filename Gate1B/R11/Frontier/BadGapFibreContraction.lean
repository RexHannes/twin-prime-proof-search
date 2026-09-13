/-
# Gate1B / R11 / Frontier : the complete bad-gap fibre contraction

Append-only module of the minimal-gap-kernel delta.  One of the central new kernel theorems.

```
H_bad(z,x,M) = ∑_{d | M, d > z, Fgap(d) > x} μ(d) log(M/d).
```

With `v` the unique minimal bad-gap kernel dividing `M ≤ x` and `M = v·m`:

```
H_bad(z,x,M) = μ(v) · H_{z/v}(m),
```

and, when moreover `v > z`,

```
H_bad(z,x,M) = μ(v) · Λ(m).
```

Consequently `H_bad = 0` unless `m` is a prime power (in particular `m = 1` gives `0`).
-/
import Gate1B.R11.Frontier.MinimalGapKernel

namespace Gate1B.R11.Frontier

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The bad-gap part of the sharp divisor fibre. -/
noncomputable def Hbad (z : ℝ) (x M : ℕ) : ℝ :=
  ∑ d ∈ M.divisors,
    (if x < Fgap d then
      (if z < (d : ℝ) then (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) else 0) else 0)

/-- **Bad-gap fibre contraction.**  If `v` is the (unique) minimal bad-gap kernel dividing
`M = v·m ≤ x`, the bad-gap fibre contracts to the sharp divisor fibre of the cofactor. -/
theorem Hbad_contraction {z : ℝ} {x M v m : ℕ} (hx : 1 ≤ x) (hM0 : M ≠ 0) (hMx : M ≤ x)
    (hv : IsMinKernel x v) (hvm : v * m = M) :
    Hbad z x M = (μ v : ℝ) * Hdiv (z / v) m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hvm; exact hM0 hvm.symm
  have hv0 : v ≠ 0 := hv.ne_zero
  have hcop : Nat.Coprime v m := (coprime_cofactor hx hv (by rw [hvm]; exact hMx) hm0).symm
  have hvM : v ∣ M := ⟨m, hvm.symm⟩
  -- the bad guard and the divisibility guard agree on the whole divisor set
  have hguard : Hbad z x M =
      ∑ d ∈ M.divisors,
        (if v ∣ d then
          (if z < (d : ℝ) then (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) else 0) else 0) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mem_divisors] at hd
    by_cases hsq : Squarefree d
    · have hiff := bad_divisor_iff hx hM0 hMx hv hvM hd.1 hsq
      by_cases hb : x < Fgap d
      · rw [if_pos hb, if_pos (hiff.1 hb)]
      · rw [if_neg hb, if_neg fun hh => hb (hiff.2 hh)]
    · have hmu : (μ d : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
      by_cases h1 : x < Fgap d <;> by_cases h2 : v ∣ d <;>
        simp [h1, h2, hmu]
  rw [hguard]
  have : M = v * m := hvm.symm
  subst this
  exact sum_fibre_dvd z hv0 hm0 hv.squarefree hcop

/-- **Bad-gap fibre contraction above the threshold.**  If in addition `v > z`, the cofactor
fibre collapses to von Mangoldt. -/
theorem Hbad_eq_vonMangoldt {z : ℝ} {x M v m : ℕ} (hx : 1 ≤ x) (hM0 : M ≠ 0) (hMx : M ≤ x)
    (hv : IsMinKernel x v) (hvm : v * m = M) (hzv : z < (v : ℝ)) :
    Hbad z x M = (μ v : ℝ) * Λ m := by
  have hv0 : v ≠ 0 := hv.ne_zero
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hv0
  have hlt : z / (v : ℝ) < 1 := by
    rw [div_lt_one hvpos]; exact hzv
  rw [Hbad_contraction hx hM0 hMx hv hvm, Hdiv_of_lt_one hlt]

/-- **Non-prime-power cofactor.**  `Λ(m) ≠ 0` forces `m` to be a prime power. -/
theorem prime_power_of_vonMangoldt_ne_zero {m : ℕ} (h : Λ m ≠ 0) :
    ∃ (l j : ℕ), l.Prime ∧ 0 < j ∧ m = l ^ j := by
  obtain ⟨l, j, hl, hj, hlj⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 h
  exact ⟨l, j, Nat.prime_iff.2 hl, hj, hlj.symm⟩

/-- If the cofactor is not a prime power then the whole bad-gap fibre vanishes. -/
theorem Hbad_eq_zero_of_not_primePow {z : ℝ} {x M v m : ℕ} (hx : 1 ≤ x) (hM0 : M ≠ 0)
    (hMx : M ≤ x) (hv : IsMinKernel x v) (hvm : v * m = M) (hzv : z < (v : ℝ))
    (hm : ¬ IsPrimePow m) : Hbad z x M = 0 := by
  rw [Hbad_eq_vonMangoldt hx hM0 hMx hv hvm hzv]
  have : Λ m = 0 := by
    by_contra hne
    exact hm (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hne)
  rw [this, mul_zero]

/-- In particular the trivial cofactor `m = 1` gives a vanishing bad-gap fibre. -/
theorem Hbad_eq_zero_of_cofactor_one {z : ℝ} {x M v : ℕ} (hx : 1 ≤ x) (hM0 : M ≠ 0)
    (hMx : M ≤ x) (hv : IsMinKernel x v) (hvm : v * 1 = M) (hzv : z < (v : ℝ)) :
    Hbad z x M = 0 := by
  rw [Hbad_eq_vonMangoldt hx hM0 hMx hv hvm hzv]
  simp

end Gate1B.R11.Frontier
