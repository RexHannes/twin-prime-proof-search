import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem t0_collision_margin (a b : ℚ) (hab : a ≤ b) (hs : a+b ≤ 5/8) :
    (2/3+2*b)-(2*a+3*b-1/3)=1-2*a-b ∧ 1/16 ≤ 1-2*a-b := by constructor <;> linarith
end NANC
