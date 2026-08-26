/-
# Gate 1B v8.2 — squarefree source router

Finite arithmetic routing lemma: if `d` is squarefree, `p` is prime, and `d * p`
fails to be squarefree, then the obstruction is exactly `p ∣ d`.  Equivalently,
`d * p` is squarefree as soon as `p ∤ d`.

This routes a source into the two strata `p ∣ d` / `p ∤ d`; it makes no
analytic claim about either stratum.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- **The router.**  A squarefree `d` times a prime `p` is squarefree unless
`p ∣ d`. -/
theorem squarefree_mul_prime_of_not_dvd {d p : ℕ} (hd : Squarefree d) (hp : p.Prime)
    (hpd : ¬ p ∣ d) : Squarefree (d * p) :=
  Nat.squarefree_mul_iff.mpr
    ⟨(Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)), hd, hp.squarefree⟩

/-- **The contrapositive routing statement.**  If `d * p` is not squarefree then
`p ∣ d`. -/
theorem dvd_of_not_squarefree_mul_prime {d p : ℕ} (hd : Squarefree d) (hp : p.Prime)
    (hnot : ¬ Squarefree (d * p)) : p ∣ d := by
  by_contra hpd
  exact hnot (squarefree_mul_prime_of_not_dvd hd hp hpd)

/-- The two strata are exhaustive and mutually exclusive. -/
theorem squarefree_router_dichotomy {d p : ℕ} (hd : Squarefree d) (hp : p.Prime) :
    (p ∣ d ∧ ¬ Squarefree (d * p)) ∨ (¬ p ∣ d ∧ Squarefree (d * p)) := by
  by_cases hpd : p ∣ d
  · refine Or.inl ⟨hpd, ?_⟩
    intro hsq
    have : p * p ∣ d * p := mul_dvd_mul hpd dvd_rfl
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
  · exact Or.inr ⟨hpd, squarefree_mul_prime_of_not_dvd hd hp hpd⟩

end Gate1B.SafeAlgebra
