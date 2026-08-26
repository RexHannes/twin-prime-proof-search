/-
# Gate-1A §14 (and A18/A19): root-depth error accounting

The old informal rule "square the error" is **not** encoded here.  What is
encoded is the exact norm inequality with its cross term, and its clean
corollary: an amplitude-level error is absorbed precisely when it is at most
the *square root* of the required saving.

We also record the two legal recombination-error routes of the ledger,
as exponent comparisons over ℚ:

* **Route A (theta EXACTLY RETAINED)** — amplitude error `U^{-2}`,
  exponent `epsExp a b = 2a + 2b - 4/3`;
* **Route B (theta DISCARDED WITH `U^{-1}`)** — amplitude error `U^{-1}`,
  exponent `uInvExp a b = a + b - 2/3`.

Both are proved admissible over the frozen polytope; Route B is the weaker
one and is admissible exactly because `a ≤ 1/3` there.
-/
import Mathlib
import Gate1A.Exponents

namespace Gate1A

namespace ErrorAlgebra

/-- **`square_norm_add_error`.**  The exact cross-term accounting:
if `‖Main‖ ≤ √δ·B` and `‖Err‖ ≤ ε·B` then `‖Main+Err‖² ≤ (√δ+ε)²·B²`.

The cross term `2√δ·ε·B²` is *not* dropped and the error is *not* squared. -/
theorem square_norm_add_error {E : Type*} [NormedAddCommGroup E]
    (main err : E) (delta eps B : ℝ) (heps : 0 ≤ eps) (hB : 0 ≤ B)
    (hm : ‖main‖ ≤ Real.sqrt delta * B) (he : ‖err‖ ≤ eps * B) :
    ‖main + err‖ ^ 2 ≤ (Real.sqrt delta + eps) ^ 2 * B ^ 2 := by
  have h1 : ‖main + err‖ ≤ (Real.sqrt delta + eps) * B := by
    calc ‖main + err‖ ≤ ‖main‖ + ‖err‖ := norm_add_le _ _
      _ ≤ Real.sqrt delta * B + eps * B := add_le_add hm he
      _ = (Real.sqrt delta + eps) * B := by ring
  have h2 : (0 : ℝ) ≤ (Real.sqrt delta + eps) * B :=
    mul_nonneg (by positivity) hB
  calc ‖main + err‖ ^ 2 ≤ ((Real.sqrt delta + eps) * B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (Real.sqrt delta + eps) ^ 2 * B ^ 2 := by ring

/-- **`error_absorbed_of_le_sqrtSaving`.**  If the *amplitude* error is at most
the square root of the required saving, `ε ≤ √δ`, then

`‖Main + Err‖² ≤ 4·δ·B²`.

This is the precise reason the recombination error must be compared with
`√(H/M)` at the amplitude/operator level, not with `H/M`. -/
theorem error_absorbed_of_le_sqrtSaving {E : Type*} [NormedAddCommGroup E]
    (main err : E) (delta eps B : ℝ) (hdelta : 0 ≤ delta) (heps : 0 ≤ eps)
    (hB : 0 ≤ B) (hm : ‖main‖ ≤ Real.sqrt delta * B) (he : ‖err‖ ≤ eps * B)
    (habs : eps ≤ Real.sqrt delta) :
    ‖main + err‖ ^ 2 ≤ 4 * delta * B ^ 2 := by
  have h := square_norm_add_error main err delta eps B heps hB hm he
  refine h.trans ?_
  have hsq : Real.sqrt delta ^ 2 = delta := Real.sq_sqrt hdelta
  have hle : (Real.sqrt delta + eps) ^ 2 ≤ 4 * delta := by
    have h1 : Real.sqrt delta + eps ≤ 2 * Real.sqrt delta := by linarith
    have h0 : (0 : ℝ) ≤ Real.sqrt delta + eps := by positivity
    calc (Real.sqrt delta + eps) ^ 2 ≤ (2 * Real.sqrt delta) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = 4 * delta := by rw [mul_pow, hsq]; norm_num
  exact mul_le_mul_of_nonneg_right hle (sq_nonneg B)

/-! ### The two legal recombination-error routes (A18/A19) -/



/-- **Route A — theta EXACTLY RETAINED.**  The amplitude error is `U^{-2}`,
with exponent `epsExp = 2a+2b-4/3`, and it satisfies the amplitude-level
comparison `epsExp ≤ reqExp/2` over the whole frozen polytope. -/
theorem route_A_theta_retained_admissible {a b : ℚ} (h : Polytope a b) :
    epsExp a b ≤ reqExp a b / 2 := by
  obtain ⟨ha, hb, hab⟩ := h
  simp only [epsExp, reqExp]
  linarith

/-- **Route B — theta DISCARDED WITH `U^{-1}`.**  The amplitude error is
`U^{-1}`, with exponent `uInvExp = a+b-2/3`.  It still satisfies
`uInvExp ≤ reqExp/2` over the frozen polytope; the underlying reason is the
inequality `a ≤ 1/3`, which follows from `a + b ≤ 5/8` and `b ≥ 1/3`. -/
theorem route_B_theta_discarded_admissible {a b : ℚ} (h : Polytope a b) :
    uInvExp a b ≤ reqExp a b / 2 := by
  obtain ⟨ha, hb, hab⟩ := h
  simp only [uInvExp, reqExp]
  linarith

/-- The structural reason Route B is admissible: `a ≤ 1/3` on the polytope. -/
theorem polytope_a_le_third {a b : ℚ} (h : Polytope a b) : a ≤ 1 / 3 := by
  obtain ⟨ha, hb, hab⟩ := h
  linarith

/-- Route A is never worse than Route B: `epsExp ≤ uInvExp` on the polytope
(both exponents are negative and `epsExp = 2·uInvExp`). -/
theorem route_A_stronger_than_route_B {a b : ℚ} (h : Polytope a b) :
    epsExp a b ≤ uInvExp a b := by
  obtain ⟨ha, hb, hab⟩ := h
  simp only [epsExp, uInvExp]
  linarith

end ErrorAlgebra

end Gate1A
