/-
# Universal / D0WP — polynomial-phase repair metadata

**Status of the analytic statement: `PAPER_CLOSED_EXTERNAL`.  Status of this
module: metadata plus two elementary kernel checks.**

The repair of the pure-Möbius polynomial-phase input is recorded, not
re-proved:

* the `D`-scale interval is split into subintervals of length `D^{2/3}`;
* the MSTT threshold is met because `2/3 > 5/8`;
* the Taylor degree satisfies `degree + 1 > 3 C₀ / η`;
* the smooth weight is removed by partial summation.

Kernel-checked here: the threshold inequality, and the existence of an admissible
Taylor degree.  The analytic theorem itself is *not* formalised, and nothing in
this module may be read as proving it.
-/
import Mathlib

namespace Universal.D0WP

/-- The recorded repair metadata of the polynomial-phase input. -/
structure PolyphaseRepairMetadata where
  /-- Subinterval exponent (`D^{2/3}`). -/
  splitExponent : ℚ
  /-- MSTT threshold exponent (`5/8`). -/
  msttThreshold : ℚ
  /-- The fixed exponent `η > 0`. -/
  eta : ℝ
  /-- The vertical exponent `C₀`. -/
  C0 : ℝ
  /-- The Taylor degree. -/
  degree : ℕ
  /-- The smooth weight is removed by partial summation. -/
  weightRemovedByPartialSummation : Bool

/-- The recorded metadata of the current repair. -/
def currentPolyphaseRepair (eta C0 : ℝ) (degree : ℕ) : PolyphaseRepairMetadata :=
  { splitExponent := 2/3
    msttThreshold := 5/8
    eta := eta
    C0 := C0
    degree := degree
    weightRemovedByPartialSummation := true }

/-- **MSTT threshold check (kernel-proved).** -/
theorem mstt_threshold_ok : (2 : ℚ) / 3 > 5 / 8 := by norm_num

/-- **Admissible Taylor degree exists (kernel-proved).**  There is always a
degree with `degree + 1 > 3 C₀ / η`. -/
theorem exists_taylor_degree (eta C0 : ℝ) :
    ∃ degree : ℕ, ((degree : ℝ) + 1) > 3 * C0 / eta := by
  obtain ⟨n, hn⟩ := exists_nat_gt (3 * C0 / eta)
  exact ⟨n, by linarith⟩

/-- The Taylor-degree condition, as recorded. -/
def PolyphaseRepairMetadata.taylorConditionHolds (m : PolyphaseRepairMetadata) : Prop :=
  ((m.degree : ℝ) + 1) > 3 * m.C0 / m.eta

end Universal.D0WP
