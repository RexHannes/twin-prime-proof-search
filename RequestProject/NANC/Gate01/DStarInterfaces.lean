import RequestProject.NANC.Gate01.CompletionInterface

/-!
# Gate 0–1: the structured `D*` open analytic inputs and the conditional
reduction `D* + COMP + finite strata ⇒ AVG-COV`

`structured-D*`,

`∑*_{m ∼ M} |∑_{h,p,q} u_{h,p,q} e_m(2h r̄ p̄ q̄) e_q(2kh p̄ m̄ m̄') |² ≪ H L⁴ X^{o(1)}`,

and its stronger arbitrary-coefficient variant are **open analytic inputs**.
They appear here only as the `bound` field of an interface structure; no
inhabitant with true analytic content is constructed, and no theorem of this
development asserts them.

The only mathematics proved in this file is:

* the modus-ponens packaging of the conditional reduction
  `D* + COMP + generic finite strata ⇒ AVG-COV`, which is banked *as an
  implication* and needs a supplied derivation step;
* the finite bookkeeping arithmetic behind it: `R K = M`, the diagonal
  comparison `(M H L²)/(H L⁴) = M/L²`, and the exponent inequality
  `M/L² = X^{1/3 - 2b} ≤ X^{-1/3}` for `b ≥ 1/3`, `X > 1`.

Status labels:
`STRUCTURED_DSTAR_OPEN_ANALYTIC_INPUT`,
`ARBITRARY_DSTAR_STRONGER_OPEN_ANALYTIC_INPUT`,
`DSTAR_IMP_AVG_COV_CONDITIONAL_BANKED`,
`AVG_COV` remains OPEN_ANALYTIC.
-/

namespace RouteAFibreFrame
namespace Gate01

/-! ### Open analytic inputs -/

/-- Interface carrying the structured `D*` statement (structured coefficients
`u_{h,p,q} = b_p d_q ν_{p,q}(h)` with `|b_p|, |d_q| ≤ 1`).  Open analytic
input. -/
structure StructuredDStarInput where
  /-- The structured `D*` proposition, supplied from outside Lean. -/
  bound : Prop

/-- Interface carrying the stronger arbitrary-coefficient `D*` statement
(`|u_{h,p,q}| ≤ 1`).  Open analytic input, strictly stronger than the
structured one. -/
structure ArbitraryDStarInput where
  /-- The arbitrary-coefficient `D*` proposition, supplied from outside Lean. -/
  bound : Prop

/-- Interface carrying the averaged covariance statement
`∑_e |C_e(b,d)|² ≪ M D² H X^{o(1)}`.  Open analytic. -/
structure AvgCovStatement where
  /-- The AVG-COV proposition. -/
  bound : Prop

/-- Interface carrying the generic finite strata used in the reduction: the
canonical congruence, the generic CRT residue, the `h = 0` cancellation, the
same-prime and exceptional-row strata.  Unlike `D*` and COMP, each of these is
*proved* in this development; the field records the form in which the reduction
consumes them. -/
structure GenericFiniteStrataInput where
  /-- The conjunction of the finite strata statements. -/
  content : Prop

/-! ### The finite strata actually proved -/

/-- The finite strata of the Gate 0–1 bank, as a single proposition. -/
def genericFiniteStrataStatement : Prop :=
  (∀ c r w0 a0 j : ℤ, c * w0 + 2 = r * a0 →
      r * (a0 + j * w0) ≡ 2 [ZMOD c + j * r])
  ∧ (∀ q m mPrime A B k p nPrime : ℤ, IsCoprime q m → A = p * nPrime →
      m * B = mPrime * A - 2 * k →
      (q ∣ B ↔ mPrime * (p * nPrime) ≡ 2 * k [ZMOD q]))
  ∧ (∀ W0 p q : ℚ, p ≠ 0 → q ≠ 0 →
      W0 / (p * q) - (1 / q) * (W0 / p) - (1 / p) * (W0 / q)
        + (1 / p) * (1 / q) * W0 = 0)
  ∧ (∀ P m mPrime A B k : ℤ, k ≠ 0 → 2 * |k| < P →
      mPrime * A - m * B = 2 * k → P ∣ A → P ∣ B → False)

/-- The finite strata statement is proved. -/
theorem genericFiniteStrataStatement_holds : genericFiniteStrataStatement := by
  refine ⟨fun c r w0 a0 j h => canonical_congruence c r w0 a0 j h, ?_, ?_, ?_⟩
  · intro q m mPrime A B k p nPrime hcop hfac hedge
    exact q_dvd_B_iff hcop hfac hedge
  · intro W0 p q hp hq
    exact h_zero_centering_cancellation W0 p q _ _ _ _ hp hq rfl rfl rfl rfl
  · intro P m mPrime A B k hk hP hdet hA hB
    exact same_prime_no_joint_hit hk hP hdet hA hB

/-- The finite strata packaged as the interface input consumed by the
reduction. -/
def genericFiniteStrata : GenericFiniteStrataInput := ⟨genericFiniteStrataStatement⟩

/-- Its content is true. -/
theorem genericFiniteStrata_content_holds : genericFiniteStrata.content :=
  genericFiniteStrataStatement_holds

/-! ### The conditional reduction -/

/-- A *derivation interface* for the reduction: the (external) argument turning
`D*`, COMP and the finite strata into AVG-COV.  It is supplied, never
constructed here. -/
structure AvgCovDerivation (dstar : StructuredDStarInput) (comp : CompInterface)
    (strata : GenericFiniteStrataInput) (avg : AvgCovStatement) where
  /-- The supplied deduction step. -/
  deduce : dstar.bound → comp.representation → strata.content → avg.bound

/-- **`D* + COMP + finite strata ⇒ AVG-COV`, banked as an implication only.**
Given the derivation interface and proofs of the two analytic inputs, AVG-COV
follows.  Since neither `D*` nor COMP is proved anywhere here, this does *not*
prove AVG-COV. -/
theorem avgCov_of_dstar_comp {dstar : StructuredDStarInput} {comp : CompInterface}
    {avg : AvgCovStatement}
    (der : AvgCovDerivation dstar comp genericFiniteStrata avg)
    (hd : dstar.bound) (hc : comp.representation) : avg.bound :=
  der.deduce hd hc genericFiniteStrata_content_holds

/-- The stronger arbitrary-coefficient input implies the structured one exactly
when the implication between the two supplied propositions is supplied; this is
recorded as an interface field, not invented. -/
structure ArbitraryImpliesStructured (arb : ArbitraryDStarInput)
    (str : StructuredDStarInput) where
  /-- The supplied specialisation step. -/
  specialise : arb.bound → str.bound

/-! ### Finite bookkeeping arithmetic -/

/-- `R K = M`: the number of `(r,k)` pairs, recorded as an identity of the
bookkeeping parameters. -/
theorem rk_count (R K M : ℝ) (h : R * K = M) : R * K = M := h

/-- The diagonal comparison `(M H L²)/(H L⁴) = M / L²`. -/
theorem diagonal_ratio (M H L : ℝ) (hH : H ≠ 0) (hL : L ≠ 0) :
    (M * H * L ^ 2) / (H * L ^ 4) = M / L ^ 2 := by
  field_simp

/-- The exponent inequality `1/3 - 2b ≤ -1/3` for `b ≥ 1/3`. -/
theorem diagonal_exponent_le (b : ℝ) (hb : (1 : ℝ) / 3 ≤ b) : (1 : ℝ) / 3 - 2 * b ≤ -(1 / 3) := by
  linarith

/-- **Bookkeeping comparison.**  With `M = X^{1/3}` and `L = X^b`, `X > 1` and
`b ≥ 1/3`, the diagonal ratio satisfies `M / L² = X^{1/3 - 2b} ≤ X^{-1/3}`. -/
theorem diagonal_ratio_bound (X b : ℝ) (hX : 1 < X) (hb : (1 : ℝ) / 3 ≤ b) :
    X ^ ((1 : ℝ) / 3) / (X ^ b) ^ (2 : ℕ) ≤ X ^ (-(1 : ℝ) / 3) := by
  have hX0 : (0 : ℝ) < X := lt_trans zero_lt_one hX
  have h1 : (X ^ b) ^ (2 : ℕ) = X ^ (2 * b) := by
    rw [← Real.rpow_natCast (X ^ b) 2, ← Real.rpow_mul hX0.le]
    ring_nf
  rw [h1, ← Real.rpow_sub hX0]
  refine Real.rpow_le_rpow_of_exponent_le hX.le ?_
  linarith

end Gate01
end RouteAFibreFrame
