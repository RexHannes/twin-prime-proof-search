import NANC.K0RoughRecombination
import Mathlib

namespace NANC

open scoped BigOperators

/-- Substituting the global recombination identity into one-sided transference
leaves exactly the stated remainder inequality; it supplies no prime lower
bound by itself. -/
theorem global_recombination_transference_tautology
    (A B L Xi E C : ℚ) (hL : L = B - A + Xi + E) :
    A ≥ C * B - L ↔ Xi + E ≥ (C - 1) * B := by
  constructor <;> intro h <;> linarith

end NANC
