/-
# Gate1B / R11 : physical `b_X` comparison typing (§7)

Two *different typed placements* of the same physical smoothing:

* `bFull n = 2 * W n * B n` — the full one-sign comparison, paired with the bare source
  `OmegaBase`;
* `bLoc  n = 2 * B n`      — the bracket-local comparison, paired with the canonical source
  `OmegaCan n = W n * OmegaBase n`.

The content is the exact algebraic identity `OmegaBase * bFull = OmegaCan * bLoc`.  `bFull`
and `bLoc` are deliberately **not** defined to be equal functions, and this file records a
witness showing that they are genuinely different.
-/
import Mathlib

namespace Gate1B.R11

open Finset

variable (OmegaBase Wn B : ℕ → ℝ)

/-- The canonical source: the bare source carrying the smoothing weight. -/
def OmegaCan (n : ℕ) : ℝ := Wn n * OmegaBase n

/-- The full one-sign comparison function. -/
def bFull (n : ℕ) : ℝ := 2 * Wn n * B n

/-- The bracket-local comparison function. -/
def bLoc (n : ℕ) : ℝ := 2 * B n

/-- **Comparison weight typing.**  Pairing the bare source with the full comparison equals
pairing the canonical source with the bracket-local comparison.  Purely algebraic. -/
theorem comparison_weight_typing (n : ℕ) :
    OmegaBase n * bFull Wn B n = OmegaCan OmegaBase Wn n * bLoc B n := by
  unfold OmegaCan bFull bLoc
  ring

/-- The same typing identity summed over an arbitrary finite index set. -/
theorem comparison_weight_typing_sum (s : Finset ℕ) :
    ∑ n ∈ s, OmegaBase n * bFull Wn B n = ∑ n ∈ s, OmegaCan OmegaBase Wn n * bLoc B n :=
  Finset.sum_congr rfl fun n _ => comparison_weight_typing OmegaBase Wn B n

/-- `bFull` and `bLoc` are **not** the same function: they differ as soon as the smoothing
weight is not identically `1`.  (Firewall against collapsing the two typed placements.) -/
theorem bFull_ne_bLoc :
    ∃ (Wn B : ℕ → ℝ), bFull Wn B ≠ bLoc B := by
  refine ⟨fun _ => 0, fun _ => 1, ?_⟩
  intro h
  have := congrFun h 0
  simp [bFull, bLoc] at this

/-- Conversely, the two placements agree exactly on the trivial-smoothing locus. -/
theorem bFull_eq_bLoc_iff (n : ℕ) :
    bFull Wn B n = bLoc B n ↔ 2 * (Wn n - 1) * B n = 0 := by
  unfold bFull bLoc
  constructor <;> intro h <;> nlinarith [h]

end Gate1B.R11
