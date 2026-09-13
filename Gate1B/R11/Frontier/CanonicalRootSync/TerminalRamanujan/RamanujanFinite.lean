/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the finite Ramanujan sum (T2)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

The finite Ramanujan sum

```
c_q(N) = ∑_{d ∣ (q,N)} d μ(q/d)
```

is defined here (the repository carries no Ramanujan-sum definition of this shape), together
with its antidiagonal form, and the **divisor identity**

```
∑_{q ∣ d} c_q(N) = d · 1_{d ∣ N},
```

which is the exact input of the finite Ramanujan expansion of the next module.  Everything is
an exact identity over `ℤ`; no asymptotics occur.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Mathlib

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset ArithmeticFunction

/-! ## 1. The two forms of `c_q(N)` -/

/-- **The finite Ramanujan sum** `c_q(N) = ∑_{d ∣ (q,N)} d μ(q/d)`. -/
def ram (q N : ℕ) : ℤ := ∑ d ∈ (Nat.gcd q N).divisors, (d : ℤ) * moebius (q / d)

/-- The antidiagonal form `c_q(N) = ∑_{uv = q} μ(u) · v · 1_{v ∣ N}`. -/
def ramAlt (q N : ℕ) : ℤ :=
  ∑ x ∈ q.divisorsAntidiagonal, (moebius x.1) * (if x.2 ∣ N then (x.2 : ℤ) else 0)

/-- The divisors of `gcd q N` are exactly the divisors of `q` that also divide `N`. -/
theorem divisors_gcd_eq_filter {q N : ℕ} (hq : q ≠ 0) :
    (Nat.gcd q N).divisors = q.divisors.filter (· ∣ N) := by
  ext i
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h1, hq⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨⟨h1, h2⟩, fun h => hq (Nat.eq_zero_of_gcd_eq_zero_left h)⟩

/-- The two forms of the Ramanujan sum agree. -/
theorem ram_eq_ramAlt {q : ℕ} (N : ℕ) (hq : q ≠ 0) : ram q N = ramAlt q N := by
  rw [ramAlt, Nat.sum_divisorsAntidiagonal' (f := fun u v => (moebius u) *
    (if v ∣ N then (v : ℤ) else 0))]
  rw [ram, divisors_gcd_eq_filter (N := N) hq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases h : i ∣ N <;> simp [h, mul_comm]

/-! ## 2. The divisor identity -/

/-- **The Ramanujan divisor identity** `∑_{q ∣ d} c_q(N) = d · 1_{d ∣ N}` — the exact finite
input of the Ramanujan expansion. -/
theorem sum_ram_divisors (N : ℕ) {d : ℕ} (hd : 0 < d) :
    ∑ q ∈ d.divisors, ram q N = if d ∣ N then (d : ℤ) else 0 := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (f := fun q => ramAlt q N) (g := fun n => if n ∣ N then (n : ℤ) else 0)).2 ?_ d hd
  · rw [← key]
    exact Finset.sum_congr rfl fun q hq =>
      ram_eq_ramAlt N (Nat.pos_of_mem_divisors hq).ne'
  · intro n _
    rw [ramAlt]
    exact Finset.sum_congr rfl fun x _ => by simp

/-- `c_1(N) = 1`. -/
theorem ram_one (N : ℕ) : ram 1 N = 1 := by
  simp [ram]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
