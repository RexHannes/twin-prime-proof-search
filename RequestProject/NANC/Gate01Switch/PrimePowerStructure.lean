import RequestProject.NANC.Gate01Switch.DivisorPairs

/-!
# Gate01Switch: the exact prime / higher-prime-power split

The `ℓ`-variable of the opened switched operator carries the von Mangoldt
weight `Λ(ℓ)`, which vanishes off prime powers.  We split the pair set exactly
into `ℓ` prime and `ℓ` non-prime; on the support of `Λ` the second class is
exactly `ℓ = p^ν` with `ν ≥ 2`.

* `pairSum_split_prime` — the exact finite equality
  `S_sw = S_prime + S_higherPrimePower`;
* `higherPrimePower_support` — exhaustion: a contributing non-prime `ℓ` is
  `p^ν` with `ν ≥ 2`;
* `PrimePowerSparseBound` — the analytic sparse bound, an **explicit
  interface**, never inhabited.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open ArithmeticFunction Finset

variable (S : Finset (ℕ × ℕ)) (G : ℕ → ℕ → ℝ)

/-- The prime part of a divisor-pair set: `ℓ` prime. -/
def primePart (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := S.filter (fun x => x.2.Prime)

/-- The higher-prime-power part: `ℓ` not prime. -/
def higherPrimePowerPart (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  S.filter (fun x => ¬ x.2.Prime)

theorem primePart_disjoint_higherPrimePowerPart :
    Disjoint (primePart S) (higherPrimePowerPart S) :=
  Finset.disjoint_filter_filter_not S S _

theorem primePart_union_higherPrimePowerPart :
    primePart S ∪ higherPrimePowerPart S = S :=
  Finset.filter_union_filter_not_eq _ S

/-- **Exact finite decomposition** `S_sw = S_prime + S_higherPrimePower`. -/
theorem pairSum_split_prime :
    pairSum S G = pairSum (primePart S) G + pairSum (higherPrimePowerPart S) G :=
  (Finset.sum_filter_add_sum_filter_not S _ _).symm

/-- **Exhaustion on the `Λ`-support**: a contributing non-prime `ℓ` is a prime
power with exponent at least `2`. -/
theorem higherPrimePower_support {x : ℕ × ℕ} (hx : x ∈ higherPrimePowerPart S)
    (hΛ : Λ x.2 ≠ 0) : ∃ p ν : ℕ, p.Prime ∧ 2 ≤ ν ∧ x.2 = p ^ ν := by
  have hnp : ¬ x.2.Prime := (Finset.mem_filter.mp hx).2
  have hpp : IsPrimePow x.2 := by
    by_contra h
    exact hΛ (vonMangoldt_eq_zero_iff.mpr h)
  obtain ⟨p, k, hp, hk, hxk⟩ := hpp
  refine ⟨p, k, hp.nat_prime, ?_, hxk.symm⟩
  rcases Nat.lt_or_ge k 2 with h | h
  · exfalso
    have hk1 : k = 1 := by omega
    have hx2 : x.2 = p := by rw [← hxk, hk1, pow_one]
    exact hnp (by rw [hx2]; exact hp.nat_prime)
  · exact h

/-- Terms off the `Λ`-support contribute nothing, so the higher-prime-power
stratum may be restricted to genuine `p^ν`, `ν ≥ 2`. -/
theorem pairSum_higherPrimePower_eq_primePow :
    pairSum (higherPrimePowerPart S) G =
      pairSum ((higherPrimePowerPart S).filter (fun x => IsPrimePow x.2)) G := by
  rw [pairSum, pairSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : IsPrimePow x.2
  · rw [if_pos h]
  · rw [if_neg h, vonMangoldt_eq_zero_iff.mpr h]
    ring

/-! ## Explicit analytic interface (never inhabited) -/

/-- **EXPLICIT INTERFACE — never inhabited.**  The sparse analytic bound for the
higher-prime-power stratum, `|S_higherPrimePower| ≤ bound`.  Nothing in this
development constructs a proof of this proposition; it exists only as a
hypothesis to be supplied from outside. -/
def PrimePowerSparseBound (Shpp bound : ℝ) : Prop := |Shpp| ≤ bound

end Gate01Switch
end TwinPrimeProject
