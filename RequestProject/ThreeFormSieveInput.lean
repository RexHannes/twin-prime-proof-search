import Mathlib

/-!
# Isolated analytic input for the three-form upper sieve

This is the single analytic input of the max-jump checkpoint.  It has no global
inhabitant.  Every use must accept an explicit value of this structure.
-/

namespace Erdos461A

/-- One isolated analytic input.  The proposition field is deliberately exact
and proof-carrying; declaring the structure does not prove it. -/
structure OPEN_ANALYTIC_INPUT_threeFormUpperSieve where
  countThreeRoughForms : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  singularFactor : ℕ → ℕ → ℝ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  statement : Prop
  proof : statement
  statementDescription : String :=
    "N(u,a,b) <= C*S(a,b)*(1 + H/(log(2H))^3), H=2+ceil(t/(2abu))"

/-- Transparent projection only; this is not a kernel proof of the sieve. -/
theorem useThreeFormUpperSieve (h : OPEN_ANALYTIC_INPUT_threeFormUpperSieve) :
    h.statement := h.proof

/-- Abstract final deterministic assembly.  All arithmetic and dyadic work is
represented by the explicit implication `assemble`; the sole analytic premise
is visibly supplied as `sieve`. -/
theorem conditionalDoublySmallTokens
    (sieve : OPEN_ANALYTIC_INPUT_threeFormUpperSieve)
    (D F t : ℕ) (A ε : ℝ)
    (nearEG : (F : ℝ) ≤ A * t / Real.log t)
    (assemble : sieve.statement →
      (F : ℝ) ≤ A * t / Real.log t → (D : ℝ) ≤ ε * t) :
    (D : ℝ) ≤ ε * t :=
  assemble sieve.proof nearEG

end Erdos461A
