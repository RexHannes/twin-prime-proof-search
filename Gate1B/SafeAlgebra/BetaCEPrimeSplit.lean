/-
# Gate 1B v8.4 — clean prime split `c = p * c₀` and the lane-C β factorisation

**Status: PROVED_FINITE / PROVED_ALGEBRAIC.**

Setting: `q = c * e` with `gcd(c, e) = 1` and `q` squarefree; `p` is a prime
dividing `q` with `p ∤ e` (the lane-E emptiness of `LaneEEmpty.lean`).  Then

* `p ∣ c`, so `c = p * c₀`;
* if also `q = d * p` then `d = c₀ * e`;
* `μ(d) = μ(c₀) μ(e)`.

The *analytic* β weight is **not** formalised.  Instead an abstract restricted
conductor coefficient

  `rhoCE c e = ∑_{p c₀ = c, physicalSupport p c₀ e} μ(c₀) logWeight p`

is defined, together with the source sum `betaSource` built from exactly the
same restricted range, and the factorisation `betaSource c e = μ(e) rhoCE c e`
is proved.  The physical range restriction stays explicit as the predicate
`physicalSupport`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## The clean prime split -/

/-- If `p` is a prime dividing `q = c * e` and `p ∤ e`, then `p ∣ c`. -/
theorem prime_dvd_conductor {p c e q : ℕ} (hp : p.Prime) (hq : q = c * e)
    (hdvd : p ∣ q) (hpe : ¬ p ∣ e) : p ∣ c := by
  subst hq
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact h
  · exact absurd h hpe

/-- The cofactor `c₀` of the clean prime split `c = p * c₀`. -/
theorem exists_cleanSplit {p c : ℕ} (hdvd : p ∣ c) : ∃ c0, c = p * c0 :=
  hdvd

/-- If `q = d * p` and `q = c * e` with `c = p * c₀` and `p ≠ 0`, then
`d = c₀ * e`. -/
theorem complement_eq {p c c0 d e q : ℕ} (hp : 0 < p) (h1 : q = d * p)
    (h2 : q = c * e) (h3 : c = p * c0) : d = c0 * e := by
  have : d * p = (c0 * e) * p := by
    rw [← h1, h2, h3]; ring
  exact Nat.eq_of_mul_eq_mul_right hp this

/-- Multiplicativity of `μ` on the clean split: `μ(c₀ e) = μ(c₀) μ(e)` when
`c₀` and `e` are coprime. -/
theorem moebius_split {c0 e : ℕ} (h : Nat.Coprime c0 e) :
    μ (c0 * e) = μ c0 * μ e :=
  isMultiplicative_moebius.map_mul_of_coprime h

/-- The split cofactor `c₀` stays coprime to `e`. -/
theorem coprime_cleanSplit {p c c0 e : ℕ} (hce : Nat.Coprime c e) (h3 : c = p * c0) :
    Nat.Coprime c0 e :=
  Nat.Coprime.coprime_dvd_left (h3 ▸ Dvd.intro_left p rfl) hce

/-- **Lane-C μ-split.**  Under the standing hypotheses, `μ(d) = μ(c₀) μ(e)`. -/
theorem moebius_complement {p c c0 d e q : ℕ} (hp : 0 < p) (hce : Nat.Coprime c e)
    (h1 : q = d * p) (h2 : q = c * e) (h3 : c = p * c0) :
    μ d = μ c0 * μ e := by
  rw [complement_eq hp h1 h2 h3, moebius_split (coprime_cleanSplit hce h3)]

/-! ## The restricted conductor coefficient

`physicalSupport p c₀ e` is the explicit physical range restriction of the
source (dyadic ranges, coprimality, lane conditions).  It is carried as an
abstract decidable predicate: no analytic property of it is used. -/

variable (physicalSupport : ℕ → ℕ → ℕ → Prop)
variable (logWeight : ℕ → ℂ)

open scoped Classical in
/-- The abstract restricted conductor coefficient
`ρ(c,e) = ∑_{p c₀ = c, physical} μ(c₀) logWeight p`. -/
noncomputable def rhoCE (c e : ℕ) : ℂ :=
  ∑ p ∈ c.divisors,
    if p.Prime ∧ physicalSupport p (c / p) e then (μ (c / p) : ℂ) * logWeight p else 0

open scoped Classical in
/-- The abstract source sum defining `β(c e)`: the same restricted range, but
carrying `μ(d) = μ(c₀ e)`, the Möbius factor of the *full* complement. -/
noncomputable def betaSource (c e : ℕ) : ℂ :=
  ∑ p ∈ c.divisors,
    if p.Prime ∧ physicalSupport p (c / p) e then (μ (c / p * e) : ℂ) * logWeight p else 0

open scoped Classical in
/-- **Lane-C β factorisation.**  If `gcd(c, e) = 1` then
`β(c e) = μ(e) · ρ(c, e)`. -/
theorem betaCE_laneC_factor {c e : ℕ} (hce : Nat.Coprime c e) :
    betaSource physicalSupport logWeight c e
      = (μ e : ℂ) * rhoCE physicalSupport logWeight c e := by
  classical
  unfold betaSource rhoCE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  by_cases hcond : p.Prime ∧ physicalSupport p (c / p) e
  · have hdvd : p ∣ c := (Nat.mem_divisors.1 hp).1
    have hsplit : c = p * (c / p) := (Nat.mul_div_cancel' hdvd).symm
    have hcop : Nat.Coprime (c / p) e := coprime_cleanSplit hce hsplit
    rw [if_pos hcond, if_pos hcond, moebius_split hcop]
    push_cast
    ring
  · rw [if_neg hcond, if_neg hcond, mul_zero]

end Gate1B.SafeAlgebra
