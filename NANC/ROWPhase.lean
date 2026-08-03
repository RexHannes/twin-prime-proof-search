import Mathlib

namespace NANC

/-- Symbolic ROW phase, with each reciprocal component retained in its own
residue ring. In this representation only the final summand depends on `m'`. -/
def rowTheta (r p q m m' : ℕ) : ZMod r × ZMod p × ZMod q :=
  (-2 * ((m * p * q : ℕ) : ZMod r)⁻¹,
   -2 * ((m * r * q : ℕ) : ZMod p)⁻¹,
   -2 * ((m' * r * p : ℕ) : ZMod q)⁻¹)

@[simp] theorem rowTheta_first_independent_of_mprime
    (r p q m m₁' m₂' : ℕ) :
    (rowTheta r p q m m₁').1 = (rowTheta r p q m m₂').1 := rfl

@[simp] theorem rowTheta_second_independent_of_mprime
    (r p q m m₁' m₂' : ℕ) :
    (rowTheta r p q m m₁').2.1 = (rowTheta r p q m m₂').2.1 := rfl

end NANC
