import RequestProject.NANC.Gate01Consolidation.NonzeroOrthogonality

/-!
# BANK F / G — shift-inverse transfer and divisor representation multiplicity

**BANK F.**  With `v = n + h q`:

* `(h, n) = 1` and `(q, n) = 1` imply `(v, n) = 1` (`coprime_shift`);
* **SHIFTINV** `q̄ ≡ h v̄ (mod n)`, stated with explicit inverses so that the
  purely congruential content is separated from any complex exponential
  (`shift_inverse`);
* **SHIFT_PHASE** the corollary for additive characters,
  `e_n(−2 a q̄) = e_n(−2 a h v̄)` (`shift_phase`).

Ledger:

```text
SHIFT_INVERSE_ALGEBRA  = PROVED
SHIFT_INVERSE_ANALYTIC_GAIN = OPEN
```

No analytic saving is claimed anywhere.

**BANK G.**  `ShiftRepresentationMultiplicityBound`: the number of admissible
shift parameters `h ≤ H` occurring in a representation `v − n = h q` is bounded
by the number of divisors of `v − n`.  The analytic divisor-growth statement
`τ(n) = X^{o(1)}` is *not* formalised here; the project's existing
`DivisorGrowthInterface` covers it.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-! ## BANK F — shift inverse -/

/-- If `(h, n) = 1` and `(q, n) = 1` then `v = n + h q` is coprime to `n`. -/
theorem coprime_shift {n q h : ℕ} (hh : Nat.Coprime h n) (hq : Nat.Coprime q n) :
    Nat.Coprime (n + h * q) n := by
  have hprod : Nat.Coprime (h * q) n := Nat.Coprime.mul_left hh hq
  have : Nat.Coprime (h * q + n) n := by
    simpa using (Nat.coprime_add_self_right (m := h * q) (n := n)).mpr hprod
  simpa [Nat.add_comm] using this

/-- **SHIFTINV.**  If `v = n + h q`, `q q̄ ≡ 1 (mod n)` and `v v̄ ≡ 1 (mod n)`
then `q̄ ≡ h v̄ (mod n)`.  Pure modular arithmetic: the inverses are given
explicitly, so no coprimality hypothesis is needed on top of them. -/
theorem shift_inverse {n q h v qbar vbar : ℤ} (hv : v = n + h * q)
    (hq : q * qbar ≡ 1 [ZMOD n]) (hvb : v * vbar ≡ 1 [ZMOD n]) :
    qbar ≡ h * vbar [ZMOD n] := by
  have h1 : n ∣ q * qbar - 1 := Int.ModEq.dvd hq.symm
  have h2 : n ∣ v * vbar - 1 := Int.ModEq.dvd hvb.symm
  have key : h * vbar - qbar
      = -(n * (vbar * qbar)) - vbar * h * (q * qbar - 1) + qbar * (v * vbar - 1) := by
    subst hv; ring
  have : n ∣ h * vbar - qbar := by
    rw [key]
    exact dvd_add (dvd_sub ⟨-(vbar * qbar), by ring⟩ (h1.mul_left _)) (h2.mul_left _)
  exact Int.modEq_iff_dvd.mpr this

/-- **SHIFT_PHASE.**  The additive-character corollary of SHIFTINV.  This is a
*separate* statement: the modular identity above carries all the arithmetic
content, and no analytic gain is asserted. -/
theorem shift_phase {n : ℕ} (hn : 0 < n) {q h v qbar vbar : ℤ} (a : ℤ)
    (hv : (v : ℤ) = n + h * q) (hq : q * qbar ≡ 1 [ZMOD (n : ℤ)])
    (hvb : v * vbar ≡ 1 [ZMOD (n : ℤ)]) :
    ec n (-2 * a * qbar) = ec n (-2 * a * (h * vbar)) := by
  have hmod : qbar ≡ h * vbar [ZMOD (n : ℤ)] := shift_inverse hv hq hvb
  exact ec_congr hn (Int.ModEq.mul_left (-2 * a) hmod)

/-! ## BANK G — shift representation multiplicity -/

/-- **ShiftRepresentationMultiplicityBound.**  For `n < v`, the admissible shift
parameters `h ≤ H` in a representation `v − n = h q` are divisors of `v − n`,
hence there are at most `τ(v − n)` of them. -/
theorem shiftRepresentationMultiplicityBound (n v H : ℕ) (hlt : n < v) :
    ((Finset.range (H + 1)).filter (fun h => 0 < h ∧ h ∣ (v - n))).card
      ≤ (v - n).divisors.card := by
  refine Finset.card_le_card ?_
  intro h hh
  rw [Finset.mem_filter] at hh
  obtain ⟨-, -, hdvd⟩ := hh
  refine Nat.mem_divisors.mpr ⟨hdvd, ?_⟩
  omega

/-- The same bound in the pair form `(h, q)`: every admissible pair is a divisor
pair of `v − n`. -/
theorem shift_pairs_subset_divisorsAntidiagonal (n v H : ℕ) :
    ((Nat.divisorsAntidiagonal (v - n)).filter (fun hq => hq.1 ≤ H))
      ⊆ Nat.divisorsAntidiagonal (v - n) := Finset.filter_subset _ _

end Gate01Consolidation
end TwinPrimeProject
