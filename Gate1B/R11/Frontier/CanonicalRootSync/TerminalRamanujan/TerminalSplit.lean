/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the low / top split  (T4)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

The abstract cutoff `q₀` with `0 ≤ q₀ ≤ Q_max` splits the finite Ramanujan expansion into

```
F = F_low + F_top,    F_top(N) = ∑_{q₀ < q ≤ Q_max} a(q) c_q(N).
```

Only the **exact algebraic identity** is proved here.  No analytic comparison of the two pieces
is attempted: the moment-level statement lives in `RowOperator.lean` and is explicitly of the
shape *budget hypotheses ⇒ reduction*.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.RamanujanCoeff

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset

/-- **The low band** `F_low(N) = ∑_{0 < q ≤ q₀} a(q) c_q(N)`. -/
def Flow (I : Cutoffs) (q0 N : ℕ) : ℚ :=
  ∑ q ∈ Finset.Ioc 0 q0, aCoeff I q * ((ram q N : ℤ) : ℚ)

/-- **The terminal band** `F_top(N) = ∑_{q₀ < q ≤ Q_max} a(q) c_q(N)`. -/
def Ftop (I : Cutoffs) (q0 N : ℕ) : ℚ :=
  ∑ q ∈ Finset.Ioc q0 I.Qmax, aCoeff I q * ((ram q N : ℤ) : ℚ)

/-- **The exact decomposition** `F = F_low + F_top`, valid for every admissible cutoff
`0 ≤ q₀ ≤ Q_max`. -/
theorem Fsum_eq_low_add_top (I : Cutoffs) {q0 N : ℕ} (hq0 : q0 ≤ I.Qmax) (hN : 0 < N) :
    Fsum I N = Flow I q0 N + Ftop I q0 N := by
  rw [Fsum_eq_ramanujan_expansion I hN, Flow, Ftop]
  exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le q0) hq0).symm

/-- Degenerate cutoff `q₀ = 0`: everything is terminal. -/
theorem Ftop_zero_cutoff (I : Cutoffs) {N : ℕ} (hN : 0 < N) : Ftop I 0 N = Fsum I N := by
  rw [Fsum_eq_ramanujan_expansion I hN, Ftop]

/-- Degenerate cutoff `q₀ = Q_max`: the terminal band is empty. -/
theorem Ftop_full_cutoff (I : Cutoffs) (N : ℕ) : Ftop I I.Qmax N = 0 := by
  rw [Ftop]
  simp

/-- The low band is the complementary sum: `F_low = F − F_top`. -/
theorem Flow_eq_sub (I : Cutoffs) {q0 N : ℕ} (hq0 : q0 ≤ I.Qmax) (hN : 0 < N) :
    Flow I q0 N = Fsum I N - Ftop I q0 N := by
  rw [Fsum_eq_low_add_top I hq0 hN]; ring

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
