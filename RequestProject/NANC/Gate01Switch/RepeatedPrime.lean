import RequestProject.NANC.Gate01Switch.PrimePowerStructure

/-!
# Gate01Switch: the repeated-prime split `p ∣ d` / `p ∤ d`

On the prime branch (`ℓ = p` prime) we split exactly according to whether `p`
divides the Möbius variable `d`.

* `repeated_prime_factorization` — for `p` prime, `p ∣ d` and `μ(d) ≠ 0`:
  `d = p d₀` with `p ∤ d₀`, `d₀` squarefree and `d` squarefree;
* `repeated_cofactor_unique` — uniqueness of `d₀`;
* `pairSum_split_repeated` — the exact finite equality
  `S_prime = S_repeatedP + S_generic`;
* `pairSum_generic_eq_squarefree` — the generic stratum may be restricted to
  squarefree `d` (the other terms have `μ(d) = 0`), so the generic predicate is
  exactly `p prime, p ∤ d, d squarefree`;
* `RepeatedPrimeSparseBound` — the analytic sparse bound, an **explicit
  interface**, never inhabited.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open ArithmeticFunction Finset

variable (S : Finset (ℕ × ℕ)) (G : ℕ → ℕ → ℝ)

/-- The repeated-prime part of the prime branch: `p ∣ d`. -/
def repeatedPart (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (primePart S).filter (fun x => x.2 ∣ x.1)

/-- The generic part of the prime branch: `p ∤ d`. -/
def genericPart (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (primePart S).filter (fun x => ¬ x.2 ∣ x.1)

theorem repeatedPart_disjoint_genericPart : Disjoint (repeatedPart S) (genericPart S) :=
  Finset.disjoint_filter_filter_not _ _ _

/-- **Exact finite decomposition** `S_prime = S_repeatedP + S_generic`. -/
theorem pairSum_split_repeated :
    pairSum (primePart S) G = pairSum (repeatedPart S) G + pairSum (genericPart S) G :=
  (Finset.sum_filter_add_sum_filter_not (primePart S) _ _).symm

/-! ## Finite algebra of the repeated branch -/

/-- **Repeated-prime prime-power extraction.**  If `p` is prime, `p ∣ d` and
`μ(d) ≠ 0`, then `d = p d₀` with `d₀ = d / p`, `p ∤ d₀`, and both `d₀` and `d`
squarefree. -/
theorem repeated_prime_factorization {p d : ℕ} (hp : p.Prime) (hdvd : p ∣ d)
    (hmu : moebius d ≠ 0) :
    d = p * (d / p) ∧ ¬ p ∣ (d / p) ∧ Squarefree (d / p) ∧ Squarefree d := by
  have hsq : Squarefree d := by
    by_contra h
    exact hmu (moebius_eq_zero_of_not_squarefree h)
  have hfac : d = p * (d / p) := (Nat.mul_div_cancel' hdvd).symm
  refine ⟨hfac, ?_, ?_, hsq⟩
  · intro hcon
    obtain ⟨j, hj⟩ := hcon
    have : p * p ∣ d := by
      refine ⟨j, ?_⟩
      rw [hfac, hj]; ring
    have := hsq p (by simpa [pow_two] using this)
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  · exact hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd)

/-- Uniqueness of the repeated cofactor. -/
theorem repeated_cofactor_unique {p d d₀ d₁ : ℕ} (hp : p.Prime)
    (h₀ : d = p * d₀) (h₁ : d = p * d₁) : d₀ = d₁ :=
  Nat.eq_of_mul_eq_mul_left hp.pos (h₀ ▸ h₁)

/-- On the generic branch only squarefree `d` contributes, so the generic
predicate is exactly `p prime ∧ p ∤ d ∧ d squarefree`. -/
theorem pairSum_generic_eq_squarefree :
    pairSum (genericPart S) G =
      pairSum ((genericPart S).filter (fun x => Squarefree x.1)) G := by
  rw [pairSum, pairSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : Squarefree x.1
  · rw [if_pos h]
  · rw [if_neg h, moebius_eq_zero_of_not_squarefree h]
    push_cast
    ring

/-! ## Explicit analytic interface (never inhabited) -/

/-- **EXPLICIT INTERFACE — never inhabited.**  The sparse analytic bound for the
repeated-prime stratum, `|S_repeatedP| ≤ bound`. -/
def RepeatedPrimeSparseBound (Srep bound : ℝ) : Prop := |Srep| ≤ bound

end Gate01Switch
end TwinPrimeProject
