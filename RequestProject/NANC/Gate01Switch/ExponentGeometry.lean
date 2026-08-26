import Mathlib

/-!
# Gate01Switch: rational exponent geometry of the switched branch

Exact `ℚ` arithmetic only.  No `X^{o(1)}` is formalized, and no analytic
statement is attached to any inequality here.

`u = 5/18 - η/2` with a rational parameter `η ≥ 0`; the exponents
`α, β, ω, ρ` satisfy `α + β = ω`, `ρ = 1 - ω`, `u < α`, `u < β`, together with
the hard switched range assumption `13/18 ≤ ω`.
-/

namespace TwinPrimeProject
namespace Gate01Switch

/-- A rational exponent point of the switched branch. -/
structure SwitchedExponents where
  eta : ℚ
  alpha : ℚ
  beta : ℚ
  omega : ℚ
  rho : ℚ
  deriving DecidableEq, Repr

namespace SwitchedExponents

/-- The threshold `u = 5/18 - η/2`. -/
def u (e : SwitchedExponents) : ℚ := 5 / 18 - e.eta / 2

end SwitchedExponents

/-- The hard switched exponent region: only arithmetic inequalities. -/
def HardSwitchedExponentRegion (e : SwitchedExponents) : Prop :=
  0 ≤ e.eta ∧ e.alpha + e.beta = e.omega ∧ e.rho = 1 - e.omega ∧
    e.u < e.alpha ∧ e.u < e.beta ∧ 13 / 18 ≤ e.omega

/-- The short-short cell: both exponents below `4/9`. -/
def ShortShort (e : SwitchedExponents) : Prop := e.alpha < 4 / 9 ∧ e.beta < 4 / 9

/-- **Geometry 1.**  If both exponents are short then `ω < 8/9`. -/
theorem geometry₁ {e : SwitchedExponents} (hreg : HardSwitchedExponentRegion e)
    (hss : ShortShort e) : e.omega < 8 / 9 := by
  obtain ⟨-, hsum, -, -, -, -⟩ := hreg
  obtain ⟨ha, hb⟩ := hss
  linarith

/-- **Geometry 2.**  If `ω ≥ 8/9` then at least one exponent is long. -/
theorem geometry₂ {e : SwitchedExponents} (hreg : HardSwitchedExponentRegion e)
    (hω : 8 / 9 ≤ e.omega) : 4 / 9 ≤ e.alpha ∨ 4 / 9 ≤ e.beta := by
  obtain ⟨-, hsum, -, -, -, -⟩ := hreg
  by_contra h
  push_neg at h
  obtain ⟨ha, hb⟩ := h
  linarith

/-- The short-short hard region is exactly the `ω`-band `[13/18, 8/9)` cut out
by the two short conditions. -/
theorem hard_shortShort_omega_band {e : SwitchedExponents}
    (hreg : HardSwitchedExponentRegion e) (hss : ShortShort e) :
    13 / 18 ≤ e.omega ∧ e.omega < 8 / 9 :=
  ⟨hreg.2.2.2.2.2, geometry₁ hreg hss⟩

/-- An explicit witness: `η = 0`, `α = β = 2/5`, `ω = 4/5`, `ρ = 1/5`. -/
def witness : SwitchedExponents := ⟨0, 2 / 5, 2 / 5, 4 / 5, 1 / 5⟩

/-- **Geometry 3.**  The short-short hard polytope is internally consistent:
the stated rational inequalities are simultaneously satisfiable.  No analytic
closure of the complement is claimed. -/
theorem hardSwitchedExponentRegion_nonempty :
    HardSwitchedExponentRegion witness ∧ ShortShort witness := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
  · simp only [witness, SwitchedExponents.u]
    norm_num

/-- The threshold is at most `5/18`, with equality exactly at `η = 0`. -/
theorem u_le (e : SwitchedExponents) (h : 0 ≤ e.eta) : e.u ≤ 5 / 18 := by
  simp only [SwitchedExponents.u]; linarith

/-- Inside the hard region, `ρ = 1 - ω ≤ 5/18`. -/
theorem rho_le {e : SwitchedExponents} (hreg : HardSwitchedExponentRegion e) :
    e.rho ≤ 5 / 18 := by
  obtain ⟨-, -, hrho, -, -, hω⟩ := hreg
  rw [hrho]; linarith

end Gate01Switch
end TwinPrimeProject
