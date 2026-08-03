import Mathlib

namespace NANC

/-- Correct cofactor-weighted CRT reconstruction at the congruence level.
`qi` are the lifted local inverses; `hreconstruct` is the standard CRT
idempotent reconstruction. The cofactors `mi` occur explicitly. -/
theorem t0_crt_cofactor_split (m : ℕ) (h q qinv : ZMod m)
    (mi qi : Fin 3 → ZMod m) (hq : IsUnit q)
    (hqinv : q * qinv = 1)
    (hreconstruct : q * (∑ i, mi i * qi i) = 1) :
    2 * h * qinv = ∑ i, 2 * h * mi i * qi i := by
  have hinv : qinv = ∑ i, mi i * qi i := by
    apply hq.mul_left_cancel
    rw [hqinv, hreconstruct]
  rw [hinv]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end NANC
