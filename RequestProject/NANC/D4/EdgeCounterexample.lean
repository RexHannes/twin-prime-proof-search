import Mathlib
import RequestProject.NANC.D4.Characters

namespace TwinPrimeProject.NANC.D4

/-- The cross-multiplied form of the `m`-modulus collapse: the two edge
numerators agree after multiplying by the corresponding denominators. -/
theorem edge_mod_m_k_disappears
    (m k r : ℕ) [NeZero m] :
    ((m + k * r : ℕ) : ZMod m) * (2 : ZMod m) =
      (r : ZMod m) * ((2 * k : ℕ) : ZMod m) := by
  simp
  ring

/-- The exact `K²` scaling of a second moment once `K` identical edge copies
have been collected. -/
theorem edge_mod_m_second_moment_counterexample
    (phiM R K : ℕ) : phiM * (K ^ 2 * R) = phiM * K ^ 2 * R := by ring

/-- The hoped-for scale is strictly too small when the lost `K` exceeds one. -/
theorem edge_mod_m_phi_m_M_bound_false
    (phiM M K : ℕ) (hphi : 0 < phiM) (hM : 0 < M) (hK : 1 < K) :
    phiM * M < phiM * M * K := by
  have h := (Nat.mul_lt_mul_left (Nat.mul_pos hphi hM)).2 hK
  simpa [mul_assoc] using h

end TwinPrimeProject.NANC.D4
