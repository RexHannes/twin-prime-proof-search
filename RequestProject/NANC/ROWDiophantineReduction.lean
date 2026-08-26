import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem row_resonance_equation_kv_eq_qu_sub_pt
    (m m' r p q v t u k : ℤ) (hm' : m' = m + k*r)
    (h1 : m*v+2 = r*p*t) (h2 : m'*v+2 = r*q*u) (hr : r ≠ 0) :
    k*v = q*u-p*t := by
  have hd : r*(k*v) = r*(q*u-p*t) := by
    rw [hm'] at h2
    linear_combination h2 - h1
  exact mul_left_cancel₀ hr hd

theorem row_resonance_r_cancels
    (r k v q u p t : ℤ) (hr : r ≠ 0)
    (h : r*(k*v) = r*(q*u-p*t)) : k*v = q*u-p*t :=
  mul_left_cancel₀ hr h
end TwinPrimeProject.NANC
