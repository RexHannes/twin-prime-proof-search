import RequestProject.Options
namespace TwinPrimeProject.NANC
structure ROWThetaSymbol where
  rTerm : ℚ
  pTerm : ℚ
  qTerm : ℚ

def rowTheta (x : ROWThetaSymbol) : ℚ := -2 * (x.rTerm + x.pTerm + x.qTerm)

theorem row_theta_only_q_term_depends_on_mprime
    (x y : ROWThetaSymbol) (hr : x.rTerm = y.rTerm) (hp : x.pTerm = y.pTerm) :
    rowTheta x - rowTheta y = -2 * (x.qTerm - y.qTerm) := by
  simp [rowTheta, hr, hp]; ring
end NANC
