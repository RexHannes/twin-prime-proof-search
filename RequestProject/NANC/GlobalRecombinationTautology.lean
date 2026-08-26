import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem global_recombination_transference_tautology
    (A B L Ξ E C : ℚ) (hL : L = B - A + Ξ + E) (htrans : A ≥ C * B - L) :
    Ξ + E ≥ (C - 1) * B := by linarith
end NANC
