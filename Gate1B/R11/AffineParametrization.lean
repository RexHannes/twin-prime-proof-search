/-
# Gate1B / R11 : the affine `t`-parametrization of the matched determinant

The determinant algebra `A·B + 2 = k·d`, the four cross gcds and the Bézout parametrization
are banked in `Gate1B.R11.Determinant`.  This module records the parametrization in the
exact biconditional form requested by the compiler: with `gcd(A,k) = 1` and one solution
`(B₀, d₀)`, the integer solutions of `A·B + 2 = k·d` are **exactly**

```
B = B₀ + k t,   d = d₀ + A t,   t ∈ ℤ unique.
```
-/
import Gate1B.R11.Determinant

namespace Gate1B.R11

/-- **Affine `t`-parametrization of the matched determinant (exact characterisation).** -/
theorem determinant_minusTwo_solution_parametrization {A k B0 d0 : ℤ} (hk : k ≠ 0)
    (hcop : IsCoprime k A) (h0 : A * B0 + 2 = k * d0) (B d : ℤ) :
    A * B + 2 = k * d ↔ ∃! t : ℤ, B = B0 + k * t ∧ d = d0 + A * t := by
  constructor
  · intro h
    exact determinant_solution_parametrization_unique hk hcop h0 h
  · rintro ⟨t, ⟨hB, hd⟩, -⟩
    subst hB
    subst hd
    exact determinant_solution_parametrization h0 t

end Gate1B.R11
