import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem cdv_B_eq_A_add_k_w (m m' k r w A B : ℤ)
    (hm' : m' = m+k*r) (hA : r*A = m*w+2) (hB : r*B = m'*w+2)
    (hr : r ≠ 0) : B = A+k*w := by
  apply (mul_left_cancel₀ hr)
  rw [hB, mul_add, hA, hm']; ring

theorem cdv_mprimeA_sub_mB (m m' k r w A B : ℤ)
    (hm' : m' = m+k*r) (hA : r*A = m*w+2) (hB : r*B = m'*w+2)
    (hr : r ≠ 0) : m'*A-m*B = 2*k := by
  apply (mul_left_cancel₀ hr)
  calc
    r * (m' * A - m * B) = m'*(r*A)-m*(r*B) := by ring
    _ = m'*(m*w+2)-m*(m'*w+2) := by rw [hA,hB]
    _ = r*(2*k) := by rw [hm']; ring

theorem cdv_D_eq_N_div_R_eq_L2_div_H_exponents (a b : ℚ) :
    2/3-a = 2*b-(a+2*b-2/3) := by ring
end NANC
