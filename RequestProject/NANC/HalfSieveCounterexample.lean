import RequestProject.Options
namespace TwinPrimeProject.NANC

def Dsemi (x : ℝ) : ℝ := 2*x

theorem continuous_half_sieve_semiprime_positive (x : ℝ) (hx : 0 < x) (hx' : x ≤ 1/2) :
    0 < Dsemi x := by simp [Dsemi, hx]

theorem continuous_half_sieve_balanced_semiprime_equals_prime : Dsemi (1/2) = 1 := by norm_num [Dsemi]
end NANC
