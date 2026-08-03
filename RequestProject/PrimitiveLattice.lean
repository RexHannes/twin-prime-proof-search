import Mathlib

/-!
# Primitive two-outer lattice identities

Exact algebraic structure of the primitive two-outer problem for the balanced
Möbius bilinear sum.  Everything here is an exact polynomial identity over `ℤ`
and is `LEAN_PROVED`.

Setup.  Two copies satisfy
`q₁ r₁ = m₁ n + 2`, `q₂ r₂ = m₂ n + 2`.

* `TWO_OUTER_LATTICE_IDENTITY`  (§4)
* `PRIMITIVE_INNER_LATTICE_COUNT`  (§6, `r_i = a_i b_i`)
-/

namespace Banking.PrimitiveLattice

/-- `TWO_OUTER_LATTICE_IDENTITY` (§4).

Eliminating the common variable `n` from `q₁r₁ = m₁n+2` and `q₂r₂ = m₂n+2`
gives the exact lattice relation `m₂q₁r₁ − m₁q₂r₂ = 2(m₂ − m₁)`.

Status: `LEAN_PROVED`. -/
theorem two_outer_lattice_identity
    (m₁ m₂ n q₁ r₁ q₂ r₂ : ℤ)
    (h₁ : q₁ * r₁ = m₁ * n + 2) (h₂ : q₂ * r₂ = m₂ * n + 2) :
    m₂ * q₁ * r₁ - m₁ * q₂ * r₂ = 2 * (m₂ - m₁) := by
  have : m₂ * (q₁ * r₁) - m₁ * (q₂ * r₂) = 2 * (m₂ - m₁) := by rw [h₁, h₂]; ring
  linarith [this]

/-- `PRIMITIVE_INNER_LATTICE_COUNT` (§6).

Writing the inner variables as `r₁ = a₁b₁`, `r₂ = a₂b₂` and setting
`D₁ = m₂q₁`, `D₂ = m₁q₂`, `h₀ = 2(m₂−m₁)`, the lattice relation becomes the
inner Diophantine equation `D₁a₁b₁ − D₂a₂b₂ = h₀`.

Status: `LEAN_PROVED`. -/
theorem primitive_inner_lattice_count
    (m₁ m₂ n q₁ q₂ a₁ b₁ a₂ b₂ : ℤ)
    (h₁ : q₁ * (a₁ * b₁) = m₁ * n + 2) (h₂ : q₂ * (a₂ * b₂) = m₂ * n + 2) :
    (m₂ * q₁) * a₁ * b₁ - (m₁ * q₂) * a₂ * b₂ = 2 * (m₂ - m₁) := by
  have : m₂ * (q₁ * (a₁ * b₁)) - m₁ * (q₂ * (a₂ * b₂)) = 2 * (m₂ - m₁) := by
    rw [h₁, h₂]; ring
  linarith [this]

/-- The purely formal inner equation with abbreviations `D₁, D₂, h₀`
(used as the standing hypothesis in `PrimitiveProgression`). -/
def InnerEquation (D₁ a₁ b₁ D₂ a₂ b₂ h₀ : ℤ) : Prop :=
  D₁ * a₁ * b₁ - D₂ * a₂ * b₂ = h₀

theorem inner_equation_of_lattice
    (m₁ m₂ n q₁ q₂ a₁ b₁ a₂ b₂ : ℤ)
    (h₁ : q₁ * (a₁ * b₁) = m₁ * n + 2) (h₂ : q₂ * (a₂ * b₂) = m₂ * n + 2) :
    InnerEquation (m₂ * q₁) a₁ b₁ (m₁ * q₂) a₂ b₂ (2 * (m₂ - m₁)) :=
  primitive_inner_lattice_count m₁ m₂ n q₁ q₂ a₁ b₁ a₂ b₂ h₁ h₂

end Banking.PrimitiveLattice
