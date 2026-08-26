import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem row_pq_diagonal_ratio (a b : ℚ) :
    (1/3 + 2*b + 2*(a+2*b-2/3)) - (4*b + 1/3 + (a+2*b-2/3)) = a-2/3 := by ring

theorem row_pq_diagonal_saving_highP3 (a : ℚ) (ha : a < 2/3) : a-2/3 < 0 := by linarith
end TwinPrimeProject.NANC
