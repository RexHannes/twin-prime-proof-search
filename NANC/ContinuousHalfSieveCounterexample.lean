import Mathlib

namespace NANC

def Dsemi (x : ℝ) : ℝ := 2 * x
def Dprime : ℝ := 1

theorem continuous_half_sieve_semiprime_positive (x : ℝ)
    (hx : 0 < x ∧ x ≤ 1 / 2) : 0 < Dsemi x := by
  simp [Dsemi, hx.1]

theorem continuous_half_sieve_balanced_semiprime_equals_prime :
    Dsemi (1 / 2) = Dprime := by norm_num [Dsemi, Dprime]

end NANC
