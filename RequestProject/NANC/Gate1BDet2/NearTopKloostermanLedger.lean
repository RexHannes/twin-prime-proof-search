import RequestProject.NANC.Gate1BDet2.DeltaExponentLedger

/-!
# Gate 1B / determinant-2 bank, Module 13: near-top Kloosterman exponent ledger

**RATIONAL / ALGEBRAIC ONLY.**

This module banks the exact rational arithmetic that was used in the numerical
diagnostic attached to the Blomer–Pascadi bilinear Kloosterman bound at the
binding endpoint.  It states **nothing** about whether that analytic theorem
applies, fails, or transfers to the present coefficient classes.

The relevant relative dual exponent at the binding endpoint `ω = 13/18` is

  `t = H_e / Q_e = 2 − 1/ω = 8/13`   (Module 12),

and the diagnostic quantity is `t/3 − 1/5`, which equals `1/195 > 0`.

Status metadata (comments only, no Lean content):

* Blomer–Pascadi applicability is an **analytic** question, not settled here.
* The source has a **joint `h(uv+2)` argument**, so the bilinear shape must be
  matched before any Kloosterman input can be invoked.
* **Coefficient-class matching remains external.**
* The published all-modulus bilinear Kloosterman bounds (including a
  `c^{-1/32}`-type saving in the square-root critical range) are *not*
  formalized here and are not installed as axioms; only the exponent arithmetic
  below is banked.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace NearTop

open Delta

/-- The near-top relative dual exponent at the binding endpoint. -/
def tEndpoint : ℚ := 8 / 13

/-- `t` is exactly the relative dual exponent `H_e / Q_e` computed in the
δ-conductor ledger at `ω = 13/18`. -/
theorem tEndpoint_eq_He_div_Qe : tEndpoint = He omegaLow / Qe omegaLow :=
  He_div_Qe_at_omegaLow.symm

/-- **The banked endpoint arithmetic:** `8/39 − 1/5 = 1/195`. -/
theorem bp_endpoint_one_over_195 : tEndpoint / 3 - 1 / 5 = 1 / 195 := by
  norm_num [tEndpoint]

/-- The intermediate value `t/3 = 8/39`. -/
theorem tEndpoint_div_three : tEndpoint / 3 = 8 / 39 := by norm_num [tEndpoint]

/-- The diagnostic quantity is strictly positive. -/
theorem bp_endpoint_pos : 0 < tEndpoint / 3 - 1 / 5 := by
  rw [bp_endpoint_one_over_195]; norm_num

/-- The generic form of the diagnostic: `t/3 − 1/5 > 0` exactly when
`t > 3/5`; the endpoint value `8/13` satisfies this. -/
theorem diagnostic_pos_iff (t : ℚ) : 0 < t / 3 - 1 / 5 ↔ 3 / 5 < t := by
  constructor <;> intro h <;> linarith

theorem tEndpoint_gt_three_fifths : (3 : ℚ) / 5 < tEndpoint := by
  norm_num [tEndpoint]

/-- **Guard.**  This module contains no analytic claim: the statements above are
rational identities, and they remain true for exponents that have no analytic
meaning at all. -/
theorem near_top_ledger_is_purely_rational :
    tEndpoint / 3 - 1 / 5 = 1 / 195 ∧ ((0 : ℚ) / 3 - 1 / 5 = -(1 / 5)) :=
  ⟨bp_endpoint_one_over_195, by norm_num⟩

end NearTop
end Gate1BDet2
end TwinPrimeProject
