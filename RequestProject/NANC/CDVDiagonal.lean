import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem cdv_time_diagonal_scale (L H D : ℚ) (hD : D = L^2/H) (hH : H ≠ 0) (hD0 : D ≠ 0) :
    L^4/D = L^2*H := by rw [hD]; field_simp
end NANC
