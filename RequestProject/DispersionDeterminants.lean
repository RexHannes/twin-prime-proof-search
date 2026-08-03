import Mathlib

/-!
# Dispersion determinants (§10)

`PRIMITIVE_PHASE_DETERMINANTS`.  After the selected Cauchy–Schwarz arrangement,
two `2×2` determinants control the phase differences:

`D_I  = det [[j, m₁'q₂'a₂'], [j', m₁q₂a₂]]  = j·(m₁q₂a₂) − j'·(m₁'q₂'a₂')`,
`D_II = det [[j, q₂'a₂'],   [j', q₂a₂]]     = j·(q₂a₂)   − j'·(q₂'a₂')`.

Lean formalizes the *polynomial determinant definitions* and their elementary
consequences only.  The analytic phase-difference formula is
`PROVISIONAL_REDUCTION` and is NOT asserted here.
-/

namespace Banking.DispersionDeterminants

/-- `D_I` (§10). -/
def D_I (j jp m₁ q₂ a₂ m₁p q₂p a₂p : ℤ) : ℤ :=
  j * (m₁ * q₂ * a₂) - jp * (m₁p * q₂p * a₂p)

/-- `D_II` (§10). -/
def D_II (j jp q₂ a₂ q₂p a₂p : ℤ) : ℤ :=
  j * (q₂ * a₂) - jp * (q₂p * a₂p)

/-- Elementary consequence: the two determinants agree once the `m₁`-rows are
factored out in the symmetric case `m₁ = m₁'`. -/
theorem D_I_eq_m1_mul_D_II_of_eq_m1
    (j jp m₁ q₂ a₂ q₂p a₂p : ℤ) :
    D_I j jp m₁ q₂ a₂ m₁ q₂p a₂p = m₁ * D_II j jp q₂ a₂ q₂p a₂p := by
  unfold D_I D_II; ring

/-- Elementary consequence: antisymmetry of `D_I` under swapping the two copies. -/
theorem D_I_swap (j jp m₁ q₂ a₂ m₁p q₂p a₂p : ℤ) :
    D_I jp j m₁p q₂p a₂p m₁ q₂ a₂ = - D_I j jp m₁ q₂ a₂ m₁p q₂p a₂p := by
  unfold D_I; ring

/-- Elementary consequence: antisymmetry of `D_II`. -/
theorem D_II_swap (j jp q₂ a₂ q₂p a₂p : ℤ) :
    D_II jp j q₂p a₂p q₂ a₂ = - D_II j jp q₂ a₂ q₂p a₂p := by
  unfold D_II; ring

/-- The exact-coefficient diagonal `(B,j) = (B',j')` sends `D_I = D_II = 0`
(here specialized to the aligned data). -/
theorem D_II_diagonal (j q₂ a₂ : ℤ) : D_II j j q₂ a₂ q₂ a₂ = 0 := by
  unfold D_II; ring

theorem D_I_diagonal (j m₁ q₂ a₂ : ℤ) : D_I j j m₁ q₂ a₂ m₁ q₂ a₂ = 0 := by
  unfold D_I; ring

/-- Degenerate stratum characterization: `D_II = 0` with `m₁ = m₁'` forces
`D_I = 0` as well. -/
theorem D_I_zero_of_D_II_zero_eq_m1
    (j jp m₁ q₂ a₂ q₂p a₂p : ℤ)
    (h : D_II j jp q₂ a₂ q₂p a₂p = 0) :
    D_I j jp m₁ q₂ a₂ m₁ q₂p a₂p = 0 := by
  rw [D_I_eq_m1_mul_D_II_of_eq_m1, h, mul_zero]

end Banking.DispersionDeterminants
