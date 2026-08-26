/-
# Gate 1B v8.3 — H7 two-dimensional regroup

**Status: PROVED_ALGEBRAIC.**

At defect order seven exactly two model coordinates remain, so the two-model
shell is already in regrouped form with `B₇ = C₇`:

    C₇ * x₁ * x₂ - q * ℓ = -2.

COMMENTS ONLY: this is the same geometric QK5 skeleton as orders five and six —
the difference is only which model coordinates were absorbed into `B`.

Nothing analytic is declared.  In particular `H7_QK5_ANALYTIC_PASS` is **not**
asserted anywhere: the two-dimensional completion estimate remains open.
-/
import Mathlib
import Gate1B.SafeAlgebra.HighOrderRegroupGeometry

namespace Gate1B.SafeAlgebra

/-- The H7 regrouped coefficient: no model is absorbed, `B₇ = C₇`. -/
def h7_defineB (C7 : ℤ) : ℤ := C7

/-- **H7 two-model (QK5-skeleton) shell identity.** -/
theorem h7_qk5_shell (C7 x1 x2 q ell : ℤ) :
    C7 * x1 * x2 - q * ell = -2 ↔ h7_defineB C7 * x1 * x2 - q * ell = -2 := Iff.rfl

/-- The H7 shell is the `j = 7` instance of the generic two-model regroup:
zero models are absorbed. -/
theorem h7_absorbs_nothing : remainingModels 7 = 2 ∧ absorbedModels 7 = 0 :=
  ⟨(regroup_order_seven).1, (regroup_order_seven).2.1⟩

/-- Congruence form of the H7 shell. -/
theorem h7_qk5_congruence (C7 x1 x2 q : ℤ) :
    (∃ ell : ℤ, C7 * x1 * x2 - q * ell = -2) ↔ q ∣ (C7 * x1 * x2 + 2) := by
  constructor
  · rintro ⟨ell, h⟩; exact ⟨ell, by linarith⟩
  · rintro ⟨ell, h⟩; exact ⟨ell, by linarith⟩

end Gate1B.SafeAlgebra
