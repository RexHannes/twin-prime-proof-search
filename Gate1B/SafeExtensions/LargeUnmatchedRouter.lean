/-
# Gate 1B safe extension — the large-unmatched structural router (FUF)

Pure finite arithmetic of natural numbers.

* `eq_one_or_prime_of_all_primeFactors_gt_sqrt` — if `0 < n < Y²` and every
  prime divisor of `n` exceeds `Y`, then `n = 1` or `n` is prime.
* `largeUnmatchedFactor_unique` — the two-variable coprime corollary.
* `fufLargeRouter_finite` — the Gate wrapper for `h_i = a r_i`.

**Scope.**  This is a structural routing fact only.  Nothing here closes, or
claims to close, the analytic large-unmatched branch.
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- **Large-unmatched router.**  If `0 < n < Y²` and every prime factor of `n`
is `> Y`, then `n` is either `1` or prime: two large prime factors would already
exceed `Y²`. -/
theorem eq_one_or_prime_of_all_primeFactors_gt_sqrt {n Y : ℕ} (hn : 0 < n) (hlt : n < Y ^ 2)
    (hbig : ∀ p, p.Prime → p ∣ n → Y < p) : n = 1 ∨ n.Prime := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne1, hnp⟩ := hcon
  have hn1 : n ≠ 1 := hne1
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
  set p := n.minFac with hpdef
  set m := n / p with hmdef
  have hnm : n = p * m := (Nat.mul_div_cancel' hpdvd).symm
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hnm; omega
    · exact h
  have hm1 : m ≠ 1 := by
    intro h
    rw [h, mul_one] at hnm
    exact hnp (hnm ▸ hp)
  have hq : (m.minFac).Prime := Nat.minFac_prime hm1
  have hqdvd : m.minFac ∣ n := (Nat.minFac_dvd m).trans ⟨p, by rw [hnm]; ring⟩
  have hYp : Y < p := hbig p hp hpdvd
  have hYq : Y < m.minFac := hbig _ hq hqdvd
  have hqm : m.minFac ≤ m := Nat.minFac_le hm0
  have : Y ^ 2 < n := by
    have h1 : Y * Y < p * m := by
      calc Y * Y < p * m.minFac :=
            Nat.mul_lt_mul_of_lt_of_le hYp (le_of_lt hYq) (by omega)
        _ ≤ p * m := Nat.mul_le_mul_left p hqm
    rw [hnm, pow_two]
    exact h1
  omega

-- The squarefree specialisation needs no separate statement: squarefreeness is
-- not used by `eq_one_or_prime_of_all_primeFactors_gt_sqrt`, so the theorem
-- above already applies verbatim to squarefree `n`.

/-- **Uniqueness of the large unmatched factor.**  For coprime `r₁, r₂` each
below `Y²` with all prime factors above `Y`, each `rᵢ` is `1` or a single prime,
and if both are prime they are distinct. -/
theorem largeUnmatchedFactor_unique {Y r₁ r₂ : ℕ} (hcop : Nat.Coprime r₁ r₂)
    (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hlt₁ : r₁ < Y ^ 2) (hlt₂ : r₂ < Y ^ 2)
    (hbig₁ : ∀ p, p.Prime → p ∣ r₁ → Y < p) (hbig₂ : ∀ p, p.Prime → p ∣ r₂ → Y < p) :
    (r₁ = 1 ∨ r₁.Prime) ∧ (r₂ = 1 ∨ r₂.Prime) ∧ (r₁.Prime → r₂.Prime → r₁ ≠ r₂) := by
  refine ⟨eq_one_or_prime_of_all_primeFactors_gt_sqrt h₁ hlt₁ hbig₁,
    eq_one_or_prime_of_all_primeFactors_gt_sqrt h₂ hlt₂ hbig₂, ?_⟩
  rintro hp₁ - rfl
  have : r₁ ∣ Nat.gcd r₁ r₁ := Nat.dvd_gcd dvd_rfl dvd_rfl
  rw [Nat.Coprime] at hcop
  rw [hcop] at this
  exact Nat.Prime.one_lt hp₁ |>.ne' (Nat.eq_one_of_dvd_one this)

/-- **Gate wrapper (FUF large branch, structural).**  With `hᵢ = a rᵢ`, coprime
unmatched cofactors `rᵢ < Y²` whose prime factors all exceed `Y`, each `hᵢ` is
either `a` itself or `a` times a *single* unmatched prime above `Y`. -/
theorem fufLargeRouter_finite {Y a r₁ r₂ h₁ h₂ : ℕ}
    (hh₁ : h₁ = a * r₁) (hh₂ : h₂ = a * r₂) (hcop : Nat.Coprime r₁ r₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt₁ : r₁ < Y ^ 2) (hlt₂ : r₂ < Y ^ 2)
    (hbig₁ : ∀ p, p.Prime → p ∣ r₁ → Y < p) (hbig₂ : ∀ p, p.Prime → p ∣ r₂ → Y < p) :
    (h₁ = a ∨ ∃ q, q.Prime ∧ Y < q ∧ h₁ = a * q) ∧
    (h₂ = a ∨ ∃ q, q.Prime ∧ Y < q ∧ h₂ = a * q) := by
  obtain ⟨hA, hB, -⟩ := largeUnmatchedFactor_unique hcop hr₁ hr₂ hlt₁ hlt₂ hbig₁ hbig₂
  constructor
  · rcases hA with h | h
    · exact Or.inl (by rw [hh₁, h, mul_one])
    · exact Or.inr ⟨r₁, h, hbig₁ r₁ h dvd_rfl, hh₁⟩
  · rcases hB with h | h
    · exact Or.inl (by rw [hh₂, h, mul_one])
    · exact Or.inr ⟨r₂, h, hbig₂ r₂ h dvd_rfl, hh₂⟩

end Gate1B.SafeExtensions
