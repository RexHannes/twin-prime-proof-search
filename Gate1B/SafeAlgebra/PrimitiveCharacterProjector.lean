/-
# Gate 1B v8.4 — the primitive `c₀` projector

**Status: CONDITIONAL_FINITE (Möbius inversion proved; the primitive
decomposition of the full character sum is an explicit hypothesis).**

Target identity, for squarefree `c₀` and a unit `A` mod `c₀`:

  `∑_{χ primitive mod c₀} χ(A) = ∑_{d ∣ c₀, d ∣ A-1} μ(c₀/d) φ(d)`.

Mathlib does not currently expose the conductor API needed to *define* the set
of primitive characters mod `c₀` together with the induction decomposition, so
the input

  `∑_{d ∣ n} (∑_{χ primitive mod d} χ(A)) = ∑_{χ mod n} χ(A)
     = φ(n) · 1_{A ≡ 1 (mod n)}`

is carried as the explicit hypothesis `hdecomp` on the abstract function
`primSum`.  The conclusion — the Möbius inversion — is fully proved; nothing is
axiomatised.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open scoped ArithmeticFunction.Moebius
open ArithmeticFunction Finset

open scoped Classical in
/-- **Primitive projector via Möbius inversion.**  If the divisor sums of
`primSum` reproduce the full character sums `φ(n) · 1_{n ∣ A-1}`, then

  `primSum c₀ = ∑_{d ∣ c₀, d ∣ A-1} μ(c₀/d) φ(d)`. -/
theorem primitiveChar_sum_squarefree (A : ℤ) (primSum : ℕ → ℂ)
    (hdecomp : ∀ n : ℕ, n > 0 → ∑ d ∈ n.divisors, primSum d
      = if (n : ℤ) ∣ A - 1 then ((n.totient : ℕ) : ℂ) else 0)
    {c0 : ℕ} (hc0 : 0 < c0) :
    primSum c0
      = ∑ d ∈ Finset.filter (fun d : ℕ => (d : ℤ) ∣ A - 1) c0.divisors,
          (μ (c0 / d) : ℂ) * ((d.totient : ℕ) : ℂ) := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℂ)
    (f := primSum)
    (g := fun n : ℕ => if (n : ℤ) ∣ A - 1 then ((n.totient : ℕ) : ℂ) else 0)).1 hdecomp c0 hc0
  rw [← key, Nat.sum_divisorsAntidiagonal'
    (f := fun i j : ℕ => (μ i : ℂ) * (if (j : ℤ) ∣ A - 1 then ((j.totient : ℕ) : ℂ) else 0)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases h : (d : ℤ) ∣ A - 1 <;> simp [h]

end Gate1B.SafeAlgebra
