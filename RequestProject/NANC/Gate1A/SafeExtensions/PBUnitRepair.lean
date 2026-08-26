/-
# NANC Gate 1A v9.4 — PB unit repair on the `q`-frequency line

The corrected fixed-quotient congruence changes the `q`-side Fourier
coordinate by a **unit**: `mu_new = r · mu_old`.  This file banks the finite
consequences of that repair.

* A Kloosterman-type sum over the unit group is invariant under the
  simultaneous unit rescaling `(a, b) ↦ (a u⁻¹, b u)`
  (`klSum_unit_scaling`) — this is the exact algebraic reason the unit repair
  costs nothing.
* The frequency relabelling is a bijection of `ZMod q` and an `ℓ²` isometry;
  these facts are re-exported from the v9.2 bank rather than re-proved.
* A guard: the relabelling is *not* the identity in general, so the old and
  corrected frequency labels must never be identified.

No analytic estimate is asserted; in particular no Weil bound is used or
claimed.
-/
import Mathlib
import RequestProject.NANC.Gate1A.SafeExtensions.CorrectedFixedQuotient

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

/-! ## 1. Unit scaling of a Kloosterman-type sum -/

/-- A Kloosterman-type sum over the units of `ZMod q` with an abstract phase
`e` (no property of `e` is used). -/
noncomputable def klSum {q : ℕ} [NeZero q] (e : ZMod q → ℂ) (a b : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ, e (a * (x : ZMod q) + b * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- **Unit scaling invariance.**  `S(a u⁻¹, b u) = S(a, b)` for every unit `u`. -/
theorem klSum_unit_scaling {q : ℕ} [NeZero q] (e : ZMod q → ℂ) (a b : ZMod q) (u : (ZMod q)ˣ) :
    klSum e (a * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) (b * (u : ZMod q)) = klSum e a b := by
  unfold klSum
  refine (Fintype.sum_bijective (fun y : (ZMod q)ˣ => u * y) (Equiv.mulLeft u).bijective _ _ ?_).symm
  intro y
  have h2 : (((u * y)⁻¹ : (ZMod q)ˣ) : ZMod q)
      = ((y⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    rw [mul_inv_rev]; push_cast; ring
  have hu : (u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by simp
  have hu' : ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q) = 1 := by simp
  congr 1
  rw [h2]
  push_cast
  calc a * (y : ZMod q) + b * ((y⁻¹ : (ZMod q)ˣ) : ZMod q)
      = a * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) * (y : ZMod q)
        + b * ((y⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
        rw [hu, hu']; ring
    _ = _ := by ring

/-! ## 2. The `q`-frequency repair (re-export of the v9.2 bank) -/

/-- **PB `q`-frequency unit repair**: `mu_new = r · mu_old` permutes the
frequency line. -/
theorem pbQFrequency_unitRepair {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) :
    Function.Bijective (fun mu : ZMod q => (r : ZMod q) * mu) :=
  V92.oldNewQCoordinate_unitEquiv r

/-- **PB `q`-frequency repair is norm preserving.** -/
theorem pbQFrequency_normPreserved {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (co : ZMod q → ℂ) :
    ∑ mu : ZMod q, ‖co ((r : ZMod q) * mu)‖ ^ 2 = ∑ mu : ZMod q, ‖co mu‖ ^ 2 :=
  V92.oldNewQCoordinate_l2Preserved r co

/-- **PB `q`-frequency repair preserves the number of active frequencies.** -/
theorem pbQFrequency_card_preserved {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (S : Finset (ZMod q)) :
    (S.image fun mu => (r : ZMod q) * mu).card = S.card :=
  V92.oldNewQCoordinate_card_preserved r S

/-! ## 3. Guard: the repair is a genuine relabelling -/

/-- The unit repair is **not** the identity in general: for `q = 5`, `r = 2`
the frequency `1` is moved.  Hence old and corrected `q`-frequency labels may
never be identified, even though every norm and cardinality is preserved. -/
theorem pbQFrequency_repair_not_identity :
    ((ZMod.unitOfCoprime 2 (by decide) : (ZMod 5)ˣ) : ZMod 5) * 1 ≠ 1 := by
  decide

end TwinPrimeProject.NANC.Gate1A.V94
