import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem short_mass_shift_avoidance_zero_mode_incompatibility
    (X M R : ℚ) (hX : 0 < X) (hM : 0 < M) (hR : M < R) : X*M/R < X := by
  apply (div_lt_iff₀ (lt_trans hM hR)).2
  nlinarith
end NANC
