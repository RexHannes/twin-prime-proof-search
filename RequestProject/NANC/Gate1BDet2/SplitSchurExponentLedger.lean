import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 24: the split Schur exponent ledger

**PURE RATIONAL ARITHMETIC.**  Nothing in this module is analytic; every
statement is an identity or inequality between explicit rational numbers.  The
names below are *labels* for exponents appearing in the common-shift Schur
bookkeeping; the module asserts nothing about any sum, any `X`, or any saving.

At `ω = 13/18` and `Rₑ = 5/18`, for `k = 0, 1, 2`:

  `x_k = (4+k)/9`,  `s_k = (5−k)/9`,  `H_k = ω − x_k`,

and the method-specific Schur endpoint loss is

  `δ_k = (x_k − Rₑ)/2`.

The critical caveat is recorded on `k0_minimizes_schur_endpoint_loss`: the
comparison `δ₀ < δ₁ < δ₂` is a statement about *this coefficient-blind Schur
ledger only*, and is **not** an intrinsic Gate-1B power deficit.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace SplitSchur

/-! ## 1. The parameters -/

/-- The split parameter `ω = 13/18` (a label, not an analytic quantity). -/
def omegaSplit : ℚ := 13 / 18

/-- The complementary modulus exponent `Rₑ = 5/18`. -/
def ReSplit : ℚ := 5 / 18

/-- `x_k = (4+k)/9`. -/
def xk (k : ℕ) : ℚ := (4 + (k : ℚ)) / 9

/-- `s_k = (5−k)/9`. -/
def sk (k : ℕ) : ℚ := (5 - (k : ℚ)) / 9

/-- `H_k = ω − x_k`. -/
def Hk (k : ℕ) : ℚ := omegaSplit - xk k

/-- `δ_k = (x_k − Rₑ)/2`, the method-specific Schur endpoint loss. -/
def deltak (k : ℕ) : ℚ := (xk k - ReSplit) / 2

/-! ## 2. `K_SPLIT_ENDPOINT_LEDGER`: the three columns -/

theorem x0 : xk 0 = 4 / 9 := by norm_num [xk]
theorem s0 : sk 0 = 5 / 9 := by norm_num [sk]
theorem H0 : Hk 0 = 5 / 18 := by norm_num [Hk, xk, omegaSplit]

theorem x1 : xk 1 = 5 / 9 := by norm_num [xk]
theorem s1 : sk 1 = 4 / 9 := by norm_num [sk]
theorem H1 : Hk 1 = 1 / 6 := by norm_num [Hk, xk, omegaSplit]

theorem x2 : xk 2 = 2 / 3 := by norm_num [xk]
theorem s2 : sk 2 = 1 / 3 := by norm_num [sk]
theorem H2 : Hk 2 = 1 / 18 := by norm_num [Hk, xk, omegaSplit]

/-- `x_k + s_k = 1` for every `k`: the split is a genuine partition of the total
length at the exponent level. -/
theorem xk_add_sk (k : ℕ) : xk k + sk k = 1 := by
  simp only [xk, sk]; ring

/-! ## 3. Complementary-modulus ratios -/

theorem Re_div_s0 : ReSplit / sk 0 = 1 / 2 := by norm_num [ReSplit, sk]
theorem Re_div_s1 : ReSplit / sk 1 = 5 / 8 := by norm_num [ReSplit, sk]
theorem Re_div_s2 : ReSplit / sk 2 = 5 / 6 := by norm_num [ReSplit, sk]

/-! ## 4. `SCHUR_METHOD_ENDPOINT_LOSSES` -/

theorem delta0 : deltak 0 = 1 / 12 := by norm_num [deltak, xk, ReSplit]
theorem delta1 : deltak 1 = 5 / 36 := by norm_num [deltak, xk, ReSplit]
theorem delta2 : deltak 2 = 7 / 36 := by norm_num [deltak, xk, ReSplit]

theorem delta0_lt_delta1 : deltak 0 < deltak 1 := by rw [delta0, delta1]; norm_num

theorem delta1_lt_delta2 : deltak 1 < deltak 2 := by rw [delta1, delta2]; norm_num

/-- **`K0_SCHUR_OPTIMAL_AMONG_012`.**  Among `k = 0, 1, 2`, the split `k = 0`
carries the smallest endpoint loss of this Schur ledger:
`δ₀ = 1/12 < δ₁ = 5/36 < δ₂ = 7/36`.

**CRITICAL.**  This is *not* an intrinsic Gate-1B power deficit.  It is only a
rational exponent ledger for the coefficient-blind common-shift Schur method:
it compares three bookkeeping quantities and says nothing about what any
analytic argument can or cannot achieve.  In particular this development does
*not* assert that Gate 1B needs a saving of size `X^{1/12}`. -/
theorem k0_minimizes_schur_endpoint_loss :
    deltak 0 < deltak 1 ∧ deltak 1 < deltak 2 ∧
      ∀ k ∈ ({1, 2} : Finset ℕ), deltak 0 < deltak k := by
  refine ⟨delta0_lt_delta1, delta1_lt_delta2, ?_⟩
  intro k hk
  fin_cases hk
  · exact delta0_lt_delta1
  · exact delta0_lt_delta1.trans delta1_lt_delta2

/-! ## 5. Guard -/

/-- **Guard.**  The ledger has no analytic content: it is a family of rational
identities, and the statements above remain true when every analytic
interpretation is stripped away. -/
theorem split_ledger_is_purely_rational :
    xk 0 = 4 / 9 ∧ sk 0 = 5 / 9 ∧ Hk 0 = 5 / 18 ∧ deltak 0 = 1 / 12 :=
  ⟨x0, s0, H0, delta0⟩

end SplitSchur
end Gate1BDet2
end TwinPrimeProject
