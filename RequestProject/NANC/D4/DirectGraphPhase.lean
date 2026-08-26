import Mathlib
import RequestProject.NANC.D4.CRT
import RequestProject.NANC.D4.Characters

namespace TwinPrimeProject.NANC.D4

/-- The edge and `D` character factors recombine to the corrected direct-graph
character monomial. -/
theorem direct_graph_character_decomposition
    {G : Type*} [CommGroup G] (χ : G →* ℂˣ)
    (mkr twoK p₁ p₂ N : G) :
    (χ mkr : ℂ) * starRingEnd ℂ (χ twoK : ℂ) *
        ((χ (p₁ * p₂) : ℂ) * starRingEnd ℂ (χ N : ℂ)) =
      (χ mkr : ℂ) * (χ (p₁ * p₂) : ℂ) *
        starRingEnd ℂ (χ (twoK * N) : ℂ) := by
  simp only [map_mul, Units.val_mul, map_star]
  ring

/-- A direct accessor exposing the edge factor used after CRT and reciprocal
character expansion. -/
def directGraphEdgeFactor
    {G : Type*} [CommGroup G] (χ : G →* ℂˣ) (mkr twoK : G) : ℂ :=
  (χ mkr : ℂ) * starRingEnd ℂ (χ twoK : ℂ)

/-- The complementary factor carries `p₁p₂` and the graph numerator `N`. -/
def directGraphDFactor
    {G : Type*} [CommGroup G] (χ : G →* ℂˣ) (p₁ p₂ N : G) : ℂ :=
  (χ (p₁ * p₂) : ℂ) * starRingEnd ℂ (χ N : ℂ)

end TwinPrimeProject.NANC.D4
