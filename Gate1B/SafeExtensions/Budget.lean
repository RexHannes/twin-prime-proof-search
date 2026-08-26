/-
# Gate 1B safe extension — sufficient congestion budget

Exact ordered-field algebra: how large the abstract congestion factor `𝔠` is allowed to be
if the target `T` is to be met.  This is a statement about the REQUIRED budget; it does not
claim that the actual arithmetic congestion satisfies it.
-/
import Gate1B.SafeAlgebra.NPLDiagonalReduction

namespace Gate1B.SafeExtensions

open Gate1B.SafeAlgebra

/-- **Sufficient congestion budget.**  Under the norm ledger `A₂ ≤ c_A U`, `B₂ ≤ c_B V`,
`C₂ ≤ c_C Q`, `E ≤ 𝔠 B₂C₂`, `U V = X`, a congestion `𝔠 ≤ T / (c_A c_B c_C X Q)` suffices
for `A₂ E ≤ T`. -/
theorem gate1B_sufficient_congestion (A2 B2 C2 E U V Q X cA cB cC cong T : ℝ)
    (hB2nn : 0 ≤ B2) (hC2nn : 0 ≤ C2) (hEnn : 0 ≤ E)
    (hcongnn : 0 ≤ cong) (hcAnn : 0 ≤ cA) (hUnn : 0 ≤ U)
    (hpos : 0 < cA * cB * cC * X * Q)
    (hA2 : A2 ≤ cA * U) (hB2 : B2 ≤ cB * V) (hC2 : C2 ≤ cC * Q)
    (hE : E ≤ cong * B2 * C2) (hUV : U * V = X)
    (hbudget : cong ≤ T / (cA * cB * cC * X * Q)) : A2 * E ≤ T := by
  have hT : cA * cB * cC * cong * X * Q ≤ T := by
    have := mul_le_mul_of_nonneg_left hbudget (le_of_lt hpos)
    calc cA * cB * cC * cong * X * Q = (cA * cB * cC * X * Q) * cong := by ring
      _ ≤ (cA * cB * cC * X * Q) * (T / (cA * cB * cC * X * Q)) := this
      _ = T := mul_div_cancel₀ T (ne_of_gt hpos)
  exact gate1B_congestionBudget_closes A2 B2 C2 E U V Q X cA cB cC cong T
    hB2nn hC2nn hEnn hcongnn hcAnn hUnn hA2 hB2 hC2 hE hUV hT

end Gate1B.SafeExtensions
