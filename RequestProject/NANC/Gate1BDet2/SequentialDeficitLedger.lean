import RequestProject.NANC.Gate1BDet2.SplitSchurExponentLedger

/-!
# Gate 1B / determinant-2 bank, Module 25: the sequential deficit ledger

**PURE RATIONAL ARITHMETIC.**  Two rational identities are banked, together with
the guards that keep them from being over-read.

1. At the binding endpoint,

     `(1/2)(3·(5/18) − 13/18) = 1/18`,

   which is the exponent-level form of `sqrt(R³/Q) = X^{1/18}` when
   `R = X^{5/18}`, `Q = X^{13/18}`.  Only the *exponent* identity is asserted;
   no `X`-statement and no analytic estimate is claimed.

2. `1/12 − 1/36 = 1/18`.

   This explains the numerical recurrence of `1/18` when one *informally*
   combines the Schur ledger loss `1/12` with two copies of a `1/72` pointwise
   five-prime saving.  **It does not prove that those savings can legally be
   stacked**: the analytic independence needed for such stacking is not proved
   anywhere in this development (Guard B of the ledger).

Status label: `X_ONE_OVER_18 : METHOD_SPECIFIC_LEDGER_ONLY`.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace SplitSchur

/-! ## 1. The binding-endpoint identity -/

/-- **`SEQUENTIAL_X_ONE_OVER_18` (endpoint form).**
`(1/2)(3 Rₑ − ω) = 1/18` at `Rₑ = 5/18`, `ω = 13/18`.  This is the exponent of
`sqrt(R³/Q)`; it is a rational identity only. -/
theorem half_three_Re_sub_omega : (1 / 2 : ℚ) * (3 * ReSplit - omegaSplit) = 1 / 18 := by
  norm_num [ReSplit, omegaSplit]

/-- The same identity with the numerals written out. -/
theorem half_three_five_eighteenths_sub_thirteen_eighteenths :
    (1 / 2 : ℚ) * (3 * (5 / 18) - 13 / 18) = 1 / 18 := by norm_num

/-! ## 2. The Schur / five-prime numerical coincidence -/

/-- **`1/12 − 1/36 = 1/18`.**

Docstring guard: this identity explains why `1/18` reappears when the Schur
ledger loss `1/12` is informally combined with two copies of the `1/72`
pointwise five-prime saving (`2 · 1/72 = 1/36`).  The *arithmetic* is banked;
the *analytic stacking* is not, and is not proved anywhere here. -/
theorem one_twelfth_sub_one_thirtysixth : (1 / 12 : ℚ) - 1 / 36 = 1 / 18 := by norm_num

/-- The five-prime bookkeeping half of the previous identity: two copies of
`1/72` make `1/36`.  Again a rational identity only. -/
theorem two_mul_one_seventysecond : 2 * (1 / 72 : ℚ) = 1 / 36 := by norm_num

/-- The Schur loss entering the coincidence is exactly `δ₀`. -/
theorem delta0_sub_two_seventysecond : deltak 0 - 2 * (1 / 72 : ℚ) = 1 / 18 := by
  rw [delta0]; norm_num

/-! ## 3. Guards -/

/-- **Guard A (no intrinsic-deficit claim).**  The number `1/18` produced above
is a value of the *method* ledger.  Formally: it is the value of the rational
expression `(1/2)(3Rₑ − ω)`, and equally of `δ₀ − 2·(1/72)`; nothing in this
development attaches it to any analytic lower bound for Gate 1B. -/
theorem one_over_18_is_a_ledger_value :
    (1 / 2 : ℚ) * (3 * ReSplit - omegaSplit) = 1 / 18 ∧
      deltak 0 - 2 * (1 / 72 : ℚ) = 1 / 18 :=
  ⟨half_three_Re_sub_omega, delta0_sub_two_seventysecond⟩

/-- **Guard B (no stacking).**  The numerical coincidence is not an implication:
the rational identity `1/12 − 1/36 = 1/18` holds regardless of whether the two
savings are independent, so it cannot by itself license multiplying them.  This
is recorded as the plain observation that the identity is an identity of
rationals, provable without any hypothesis about the analytic quantities. -/
theorem stacking_is_not_implied_by_the_identity :
    ((1 / 12 : ℚ) - 1 / 36 = 1 / 18) ∧ (∀ q : ℚ, q - q = 0) :=
  ⟨one_twelfth_sub_one_thirtysixth, fun q => sub_self q⟩

end SplitSchur
end Gate1BDet2
end TwinPrimeProject
