/-
# Gate 1B v8.4 — generic-sector `μ` spending

**Status: PROVED_ALGEBRAIC (given the projector identity).**

In the generic sector `gcd(c₀, A-1) = 1` only the divisor `d = 1` contributes to
the projector, so

  `(μ(c₀)/c₀) ∑_{χ primitive mod c₀} χ(A) = 1/c₀`.

FIREWALL.  `μ(c₀)` **disappears algebraically** in the generic projector sector.
It must not be counted afterwards as an independent sign resource (see
`Gate1B/SafeExtensions/V84ResourceLedger.lean` and `CountermodelsV84.lean`,
item C).
-/
import Mathlib
import Gate1B.SafeAlgebra.PrimitiveProjectorMu

namespace Gate1B.SafeAlgebra

open scoped ArithmeticFunction.Moebius
open ArithmeticFunction Finset

/-- In the generic sector, a common divisor of `c₀` and `A - 1` is `1`. -/
theorem generic_common_divisor_eq_one {c0 : ℕ} {A : ℤ}
    (hcop : Int.gcd (c0 : ℤ) (A - 1) = 1) {d : ℕ} (hd : d ∣ c0) (hdA : (d : ℤ) ∣ A - 1) :
    d = 1 := by
  have h1 : (d : ℤ) ∣ (c0 : ℤ) := Int.natCast_dvd_natCast.2 hd
  have h2 : (d : ℤ) ∣ ((Int.gcd (c0 : ℤ) (A - 1) : ℕ) : ℤ) := by
    exact_mod_cast Int.dvd_gcd h1 hdA
  rw [hcop] at h2
  exact Nat.eq_one_of_dvd_one (by exact_mod_cast h2)

open scoped Classical in
/-- The generic-sector divisor set of the projector is `{1}`. -/
theorem generic_filter_eq_singleton {c0 : ℕ} {A : ℤ} (hc0 : 0 < c0)
    (hcop : Int.gcd (c0 : ℤ) (A - 1) = 1) :
    Finset.filter (fun d : ℕ => (d : ℤ) ∣ A - 1) c0.divisors = {1} := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, -⟩, hdA⟩
    exact generic_common_divisor_eq_one hcop hd hdA
  · rintro rfl
    exact ⟨⟨one_dvd _, hc0.ne'⟩, by simp⟩

open scoped Classical in
/-- **Generic projector value.**  `(μ(c₀)/c₀) primSum c₀ = 1/c₀` when
`gcd(c₀, A-1) = 1`. -/
theorem primitiveProjector_generic_eq_inv (A : ℤ) (primSum : ℕ → ℂ)
    (hdecomp : ∀ n : ℕ, n > 0 → ∑ d ∈ n.divisors, primSum d
      = if (n : ℤ) ∣ A - 1 then ((n.totient : ℕ) : ℂ) else 0)
    {c0 : ℕ} (hc0 : 0 < c0) (hsf : Squarefree c0)
    (hcop : Int.gcd (c0 : ℤ) (A - 1) = 1) :
    ((μ c0 : ℂ) / (c0 : ℂ)) * primSum c0 = 1 / (c0 : ℂ) := by
  rw [mu_weighted_primitiveProjector A primSum hdecomp hc0 hsf,
    generic_filter_eq_singleton hc0 hcop]
  simp

end Gate1B.SafeAlgebra
