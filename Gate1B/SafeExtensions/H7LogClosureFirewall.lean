/-
# Gate 1B v8.4 — no-log promotion firewall

**Status: PROVED_FINITE (firewall implication) + documentation.**

RECORD.  A capacity statement of the shape

    `D ≤ Y⁹ · X^{o(1)}`

does **not** instantiate the interface required by the Gate 1B compiler,

    `D ≤ Y⁹ · log^{-A} X`   (for every `A`).

Exponent-zero capacity removes the fixed positive-power wall and nothing more.
No theorem in this bank infers an arbitrary-log saving from exponent-zero
capacity, and none may be added that does.

The single declaration below is the firewall itself: a natural-scale bound is
compatible with the failure of any prescribed strictly smaller target.
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- **No-log promotion firewall.**  For every natural-scale value `S > 0` and
every log-saving factor `t < 1`, there is data satisfying the natural-scale
bound `D ≤ S` but violating the target `D ≤ t · S`.  Hence "exponent 0" never
implies "log saving". -/
theorem no_log_saving_from_natural_scale {S t : ℝ} (hS : 0 < S) (ht : t < 1) :
    ∃ D : ℝ, D ≤ S ∧ ¬ (D ≤ t * S) := by
  refine ⟨S, le_refl S, ?_⟩
  intro hcon
  nlinarith

end Gate1B.SafeExtensions
