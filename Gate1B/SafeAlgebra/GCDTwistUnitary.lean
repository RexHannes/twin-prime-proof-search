/-
# Gate 1B v8.2 — unitarity of the GCD square twist

The GCD-stratified twist family is obtained from a single vector `K` by the
square twists `P_a K = K(· a⁻²)`.  Since each twist is a reindexing by a group
bijection, the family is *isometric*: every member has the same ℓ² energy, and
every Gram entry is bounded by that one common energy.

All statements are re-expressions of `Universal.SafeAlgebra` results for the
GCD family; no analytic bound on `K` itself is claimed.
-/
import Mathlib
import Universal.SafeAlgebra.PermutationEnergy

namespace Gate1B.SafeAlgebra

open Universal.SafeAlgebra

variable {G : Type*} [Group G] [Fintype G]

/-- The GCD twist family attached to a vector `K`, indexed by the twist
parameter. -/
noncomputable def gcdTwistFamily (K : G → ℂ) : G → (G → ℂ) := fun a => squareTwist K a

/-- **Isometry of the GCD twist family.** -/
theorem gcdTwistFamily_energy (K : G → ℂ) (a : G) :
    l2Energy (gcdTwistFamily K a) = l2Energy K :=
  squareTwist_l2Energy K a

/-- **Uniform Gram bound for the GCD twist family.** -/
theorem gcdTwistFamily_gram_bound (K : G → ℂ) (a b : G) :
    ‖gramEntry (gcdTwistFamily K a) (gcdTwistFamily K b)‖ ≤ l2Energy K :=
  squareTwist_gram_bound K a b

/-- The family energy of the whole twist family is exactly `#G` times the single
common energy: twisting creates no new mass. -/
theorem gcdTwistFamily_total_energy (K : G → ℂ) :
    ∑ a : G, l2Energy (gcdTwistFamily K a) = (Fintype.card G : ℝ) * l2Energy K := by
  simp [gcdTwistFamily_energy, Finset.card_univ]

end Gate1B.SafeAlgebra
