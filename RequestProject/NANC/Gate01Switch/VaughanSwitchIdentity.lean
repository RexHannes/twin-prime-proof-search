import RequestProject.NANC.Gate01Switch.SwitchedOperator

/-!
# Gate01Switch: audit of the Vaughan divisor-switch identity

## Source audit result: **EXACT MATCH**

`RequestProject/VaughanPacketAlgebra.lean` proves

`exactP1P2P3Decomposition : shiftedPairing K Λ c = P1 - P2 + P3`

(under `ShiftedSupportAbove V c`, i.e. the shifted coefficient is supported on
`N > V`).  The specification's proposed shape `P₃ = Λ - P₁ + P₂` is therefore
literally the source identity rearranged, and is proved here as
`vaughanSwitchIdentity`.  No analytic "circularity" theorem is derived; this is
exact algebra only.

## Residue bridge

The archive discrepancy `finiteDiscrepancy K q a c E` uses the *fixed natural*
residue `a`.  For a single modulus `q` whose residue `a % q` equals the
canonical representative of `-2`, it coincides with the switched discrepancy
`discrMinusTwo`; this is `finiteDiscrepancy_eq_discrMinusTwo`.  No single
natural `a` works for all `q` simultaneously, which is exactly why the switched
bank defines the progression by divisibility.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open Finset

/-- **The Vaughan divisor-switch identity, source form.**  `P₃ = Λ - P₁ + P₂`. -/
theorem vaughanSwitchIdentity (K U V : ℕ) (c : ℕ → ℝ) (hc : ShiftedSupportAbove V c) :
    VaughanP3 K U V c = shiftedPairing K ArithmeticFunction.vonMangoldt c
      - VaughanP1 K U c + VaughanP2 K U V c := by
  have h := exactP1P2P3Decomposition K U V c hc
  linarith

/-- The archive's fixed-residue discrepancy agrees with the switched
residue-`-2` discrepancy at a modulus `q` whose residue is `-2`. -/
theorem finiteDiscrepancy_eq_discrMinusTwo {K q a : ℕ} (hq : 0 < q)
    (ha : a % q = negTwoResidue q) (c E : ℕ → ℝ) :
    finiteDiscrepancy K q a c E = discrMinusTwo K q c E := by
  rw [finiteDiscrepancy, discrMinusTwo, residueMinusTwoSet, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : q ∣ n + 2
  · rw [if_pos h, if_pos (by rw [ha]; exact (dvd_add_two_iff_mod_eq hq n).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((dvd_add_two_iff_mod_eq hq n).mpr (by rw [← ha]; exact hc)))]

end Gate01Switch
end TwinPrimeProject
