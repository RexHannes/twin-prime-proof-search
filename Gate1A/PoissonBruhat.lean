/-
# Gate-1A (A9): the corrected 2D Poisson–Bruhat normalisation

The corrected normalisation is an **exponent identity**, and it is proved
here over ℚ against the frozen scale ledger of `Gate1A/Exponents.lean`:

    M² H / (R L²) = 1
    (M K / (R L⁴)) · (M H)² = 1

Both hold identically on the whole `(a,b)` plane, not merely on the
polytope: they are consequences of the frozen definitions
`H = X^(a+2b-2/3)`, `K = X^(1/3-a)`, `M = X^(1/3)`.

The remaining *analytic* content of A9 — the Schwartz lattice `ℓ¹` bound
`pb_schwartz_lattice_l1` and the operator bound `pb_source_operator_bound`
— is **not** proved here.  It is carried as an explicit interface field in
`Gate1A/SourceInterfaces.lean`; the countermodel
`scalar_l1_mass_not_operator_norm` (A10) is exactly the reason the `ℓ¹`
lattice mass may not be substituted for the operator bound.
-/
import Mathlib
import Gate1A.Exponents

namespace Gate1A

namespace PoissonBruhat

/-- `M² H = R L²`: the first Poisson–Bruhat normalisation, in exponents. -/
theorem pb_normalisation_one (a b : ℚ) :
    2 * mExp + hExp a b - (a + 2 * b) = 0 := by
  simp only [mExp, hExp]
  ring

/-- `(M K / (R L⁴)) · (M H)² = 1`: the second (corrected) Poisson–Bruhat
normalisation, in exponents. -/
theorem pb_normalisation_two (a b : ℚ) :
    (mExp + kExp a - (a + 4 * b)) + 2 * (mExp + hExp a b) = 0 := by
  simp only [mExp, kExp, hExp]
  ring

/-- The two normalisations are equivalent given the frozen ledger: the
second is the first applied twice together with `R K = M`. -/
theorem pb_normalisations_equivalent (a b : ℚ) :
    (mExp + kExp a - (a + 4 * b)) + 2 * (mExp + hExp a b)
      = 2 * (2 * mExp + hExp a b - (a + 2 * b)) := by
  simp only [mExp, kExp, hExp]
  ring

end PoissonBruhat

end Gate1A
