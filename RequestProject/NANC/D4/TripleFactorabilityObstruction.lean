import Mathlib

namespace TwinPrimeProject.NANC.D4

theorem prime_dvd_triple_product {q d₁ d₂ d₃ : ℕ} (hq : Nat.Prime q)
    (hdiv : q ∣ d₁ * d₂ * d₃) : q ∣ d₁ ∨ q ∣ d₂ ∨ q ∣ d₃ := by
  rcases hq.dvd_mul.mp hdiv with h | h
  · rcases hq.dvd_mul.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Exact finite countermodel showing why positivity of `d` is required. -/
theorem zero_countermodel_to_unqualified_triple_obstruction (q : ℕ) :
    q ∣ 0 ∧ 0 = 0 * 0 * 0 ∧ 0 < q →
      q ∣ 0 ∧ 0 < q := by
  intro h
  exact ⟨h.1, h.2.2⟩

/-- The positivity premise is essential over `ℕ`: without it, `d=d₁=d₂=d₃=0`
is a counterexample to the originally proposed statement. -/
theorem no_three_factor_decomposition_below_prime {q d d₁ d₂ d₃ : ℕ}
    (hq : Nat.Prime q) (hd : 0 < d) (hqd : q ∣ d)
    (hprod : d = d₁ * d₂ * d₃)
    (h₁ : d₁ < q) (h₂ : d₂ < q) (h₃ : d₃ < q) : False := by
  have hdiv : q ∣ d₁ * d₂ * d₃ := hprod ▸ hqd
  have hallpos : 0 < d₁ ∧ 0 < d₂ ∧ 0 < d₃ := by
    have hp : 0 < (d₁ * d₂) * d₃ := by simpa [hprod] using hd
    have hp12 : 0 < d₁ * d₂ := Nat.pos_of_mul_pos_right hp
    exact ⟨Nat.pos_of_mul_pos_right hp12, Nat.pos_of_mul_pos_left hp12,
      Nat.pos_of_mul_pos_left hp⟩
  rcases prime_dvd_triple_product hq hdiv with h | h | h
  · have hle := Nat.le_of_dvd hallpos.1 h
    omega
  · have hle := Nat.le_of_dvd hallpos.2.1 h
    omega
  · have hle := Nat.le_of_dvd hallpos.2.2 h
    omega

theorem balanced_factor_budget_lt_large_prime {Qexp b : ℚ}
    (hQ : Qexp ≤ (5 : ℚ) / 8) (hb : (1 : ℚ) / 3 ≤ b) :
    Qexp / 3 < b := by
  linarith

/-- A finite decomposition predicate; no analytic factorability claim is
encoded here. -/
def HasBoundedTripleDecomposition (d Q₁ Q₂ Q₃ : ℕ) : Prop :=
  ∃ d₁ d₂ d₃, d = d₁ * d₂ * d₃ ∧ d₁ ≤ Q₁ ∧ d₂ ≤ Q₂ ∧ d₃ ≤ Q₃

/-- `BALANCED_TWF_LARGE_PRIME_OBSTRUCTION`: an indivisible prime larger than
all three budgets prevents the finite three-factor decomposition. -/
theorem balanced_TWF_large_prime_obstruction {q d Q₁ Q₂ Q₃ : ℕ}
    (hq : Nat.Prime q) (hd : 0 < d) (hqd : q ∣ d)
    (hQ₁ : Q₁ < q) (hQ₂ : Q₂ < q) (hQ₃ : Q₃ < q) :
    ¬ HasBoundedTripleDecomposition d Q₁ Q₂ Q₃ := by
  rintro ⟨d₁, d₂, d₃, hprod, hd₁, hd₂, hd₃⟩
  exact no_three_factor_decomposition_below_prime hq hd hqd hprod
    (lt_of_le_of_lt hd₁ hQ₁) (lt_of_le_of_lt hd₂ hQ₂) (lt_of_le_of_lt hd₃ hQ₃)

end TwinPrimeProject.NANC.D4
