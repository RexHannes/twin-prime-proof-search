import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 1: modulus sign collapse

This module banks the *atomic* Möbius sign identity behind the collapse of the
distinguished-prime weighted cell coefficient,

  `λ_{D,P}(q) = − μ(q) · L_{D,P}(q)`,

together with its immediate consequence that, for a fixed squarefree `q`, every
admissible distinguished-prime summand carries the *same* Möbius sign (so no
cancellation between distinguished `p`-representations of the same `q` can be
claimed).

Everything is finite and deterministic.  The prime weight `w` is abstract: it
takes values in an arbitrary commutative ring `R`, so `Real.log` is *not*
hard-coded.

## Audit note on `Squarefree q`

The atomic lemma `moebius_cofactor_of_prime_eq_neg` does **not** need
`Squarefree q`: `q = d * p`, `p` prime and `Nat.Coprime d p` already suffice,
because `μ` is multiplicative on coprime arguments and `μ p = −1`.
Squarefreeness of `q` is used only where the *coprimality* `Nat.Coprime (q/p) p`
has to be produced from `p ∣ q` alone (`coprime_div_prime_of_squarefree`).
-/

namespace TwinPrimeProject
namespace Gate1BDet2

open ArithmeticFunction ArithmeticFunction.Moebius

/-! ## 1. The atomic Möbius prime-cofactor sign identity -/

/-- **Möbius prime-cofactor sign identity.**  If `q = d * p` with `p` prime and
`d` coprime to `p`, then `μ d = − μ q`.

Note the hypotheses: no squarefreeness of `q` is assumed (it is not needed). -/
theorem moebius_cofactor_of_prime_eq_neg {q d p : ℕ} (hq : q = d * p)
    (hp : Nat.Prime p) (hdp : Nat.Coprime d p) :
    μ d = - μ q := by
  subst hq
  rw [isMultiplicative_moebius.map_mul_of_coprime hdp, moebius_apply_prime hp]
  ring

/-- The same identity in the equivalent orientation `μ q = − μ d`. -/
theorem moebius_eq_neg_cofactor {q d p : ℕ} (hq : q = d * p)
    (hp : Nat.Prime p) (hdp : Nat.Coprime d p) :
    μ q = - μ d := by
  rw [moebius_cofactor_of_prime_eq_neg hq hp hdp]; ring

/-- For a squarefree `q` and a prime `p ∣ q`, the complementary divisor `q / p`
is coprime to `p`.  (This is the only place squarefreeness is used.) -/
theorem coprime_div_prime_of_squarefree {q p : ℕ} (hq : Squarefree q)
    (hp : Nat.Prime p) (hpq : p ∣ q) : Nat.Coprime (q / p) p := by
  rw [Nat.coprime_comm]
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
  intro hdvd
  have hsq : p * p ∣ q := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, ?_⟩
    have hq' : p * (q / p) = q := Nat.mul_div_cancel' hpq
    rw [← hq', hc]; ring
  have := hq p hsq
  rw [Nat.isUnit_iff] at this
  exact hp.one_lt.ne' this

/-- **Cofactor sign identity on squarefree support.**  For squarefree `q` and a
prime `p ∣ q`, `μ (q / p) = − μ q`. -/
theorem moebius_div_prime_of_squarefree {q p : ℕ} (hq : Squarefree q)
    (hp : Nat.Prime p) (hpq : p ∣ q) : μ (q / p) = - μ q :=
  moebius_cofactor_of_prime_eq_neg (Nat.div_mul_cancel hpq).symm hp
    (coprime_div_prime_of_squarefree hq hp hpq)

/-! ## 2. The weighted distinguished-prime cell -/

variable {R : Type*} [CommRing R]

/-- The admissible distinguished primes of `q`: those `p ∈ Pbox` which are prime,
divide `q`, and whose complementary divisor lies in `Dbox`.  All support
conditions are exposed. -/
def admissiblePrimeDivisors (Pbox Dbox : Finset ℕ) (q : ℕ) : Finset ℕ :=
  Pbox.filter (fun p => p.Prime ∧ p ∣ q ∧ q / p ∈ Dbox)

@[simp] theorem mem_admissiblePrimeDivisors {Pbox Dbox : Finset ℕ} {q p : ℕ} :
    p ∈ admissiblePrimeDivisors Pbox Dbox q ↔
      p ∈ Pbox ∧ Nat.Prime p ∧ p ∣ q ∧ q / p ∈ Dbox := by
  simp [admissiblePrimeDivisors]

/-- The unweighted (log-free) cell `L_{D,P}(q) = ∑_{p} w p`, with abstract prime
weight `w : ℕ → R`. -/
def LCell (Pbox Dbox : Finset ℕ) (w : ℕ → R) (q : ℕ) : R :=
  ∑ p ∈ admissiblePrimeDivisors Pbox Dbox q, w p

/-- The Möbius-weighted cell coefficient
`λ_{D,P}(q) = ∑_{p} μ(q/p) · w p`. -/
def lambdaCell (Pbox Dbox : Finset ℕ) (w : ℕ → R) (q : ℕ) : R :=
  ∑ p ∈ admissiblePrimeDivisors Pbox Dbox q, (μ (q / p) : R) * w p

/-- **Cell sign collapse.**  On squarefree source support,
`λ_{D,P}(q) = − μ(q) · L_{D,P}(q)`. -/
theorem lambdaCell_eq_neg_moebius_mul_LCell {Pbox Dbox : Finset ℕ} {w : ℕ → R}
    {q : ℕ} (hq : Squarefree q) :
    lambdaCell Pbox Dbox w q = -(μ q : R) * LCell Pbox Dbox w q := by
  unfold lambdaCell LCell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [mem_admissiblePrimeDivisors] at hp
  obtain ⟨-, hpp, hpq, -⟩ := hp
  rw [moebius_div_prime_of_squarefree hq hpp hpq]
  push_cast
  ring

/-! ## 3. No same-`q` distinguished-prime Möbius cancellation -/

/-- **Constant sign.**  For a fixed squarefree `q`, all admissible distinguished
primes carry the same Möbius coefficient `μ (q / p) = − μ q`.  Hence no
cancellation between the distinguished `p`-representations of a single `q` may
be claimed. -/
theorem admissible_moebius_constant {Pbox Dbox : Finset ℕ} {q p₁ p₂ : ℕ}
    (hq : Squarefree q)
    (h₁ : p₁ ∈ admissiblePrimeDivisors Pbox Dbox q)
    (h₂ : p₂ ∈ admissiblePrimeDivisors Pbox Dbox q) :
    μ (q / p₁) = μ (q / p₂) := by
  rw [mem_admissiblePrimeDivisors] at h₁ h₂
  rw [moebius_div_prime_of_squarefree hq h₁.2.1 h₁.2.2.1,
    moebius_div_prime_of_squarefree hq h₂.2.1 h₂.2.2.1]

/-- On squarefree support with `q ≠ 1` the common Möbius coefficient is a unit
sign `± 1`; in particular it never vanishes, so the collapse
`λ = − μ(q) L` loses no information. -/
theorem moebius_div_prime_ne_zero {q p : ℕ} (hq : Squarefree q)
    (hp : Nat.Prime p) (hpq : p ∣ q) : μ (q / p) ≠ 0 := by
  rw [moebius_div_prime_of_squarefree hq hp hpq]
  simpa using (moebius_ne_zero_iff_squarefree).2 hq

end Gate1BDet2
end TwinPrimeProject
