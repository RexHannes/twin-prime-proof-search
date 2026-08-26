import RequestProject.NANC.Gate01Switch.FixedCellConvolution

/-!
# Gate01Switch: a finite *local* well-factorability obstruction

`SupportedUpTo γ Q` says `γ` vanishes above `Q`.  A `(Q₁, Q₂)`-factorization of
`λ` is a Dirichlet convolution `λ = γ₁ * γ₂` with `supp γ₁ ⊆ [1, Q₁]` and
`supp γ₂ ⊆ [1, Q₂]`.

The theorem below is **purely local**: at a single modulus `q` with no
nontrivial divisor `≤ Q₁` and `q > Q₂`, every such factorization forces
`λ(q) = 0`.  Consequently `λ(q) ≠ 0` refutes the existence of a
`(Q₁, Q₂)`-factorization *at that `q`*.

**Scope warning.**  This is a conditional local obstruction only.  No global
statement that `lambda3` fails to be well-factorable is proved, and none is
claimed; the ledger records `WELL_FACTORABLE_GLOBAL_CONCLUSION` as
`WF_GLOBAL_NOT_PROVED`.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open Finset

/-- `γ` is supported in `[1, Q]`. -/
def SupportedUpTo (g : ℕ → ℝ) (Q : ℕ) : Prop := ∀ n, Q < n → g n = 0

/-- `λ` has a `(Q₁, Q₂)`-factorization. -/
def HasFactorization (lam : ℕ → ℝ) (Q₁ Q₂ : ℕ) : Prop :=
  ∃ g₁ g₂ : ℕ → ℝ, SupportedUpTo g₁ Q₁ ∧ SupportedUpTo g₂ Q₂ ∧
    ∀ n, lam n = dconv g₁ g₂ n

/-- **Local vanishing.**  If `λ = γ₁ * γ₂` with the stated supports, and `q`
has no nontrivial divisor `≤ Q₁` while `q > Q₂`, then `λ(q) = 0`. -/
theorem factorization_vanishes_at {lam : ℕ → ℝ} {Q₁ Q₂ q : ℕ}
    (hfac : HasFactorization lam Q₁ Q₂)
    (hcoarse : ∀ d, d ∣ q → d ≤ Q₁ → d = 1) (hq : Q₂ < q) :
    lam q = 0 := by
  obtain ⟨g₁, g₂, hs₁, hs₂, hlam⟩ := hfac
  rw [hlam q, dconv]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  obtain ⟨hprod, -⟩ := hx
  by_cases h : x.1 ≤ Q₁
  · have hx1 : x.1 = 1 := hcoarse x.1 ⟨x.2, hprod.symm⟩ h
    have hx2 : x.2 = q := by rw [← hprod, hx1, one_mul]
    rw [hx2, hs₂ q hq, mul_zero]
  · rw [hs₁ x.1 (by omega), zero_mul]

/-- **The local obstruction, in the stated form.**  For `q = p₁p₂` with `p₁, p₂`
prime and `> Q₁`, `q > Q₂`, `q` free of nontrivial divisors `≤ Q₁`, and
`λ(q) ≠ 0`, no `(Q₁, Q₂)`-factorization can represent `λ`.

The primality of `p₁, p₂` and the shape `q = p₁p₂` are the hypotheses requested
in the specification; the proof only needs the coarseness hypothesis
`hcoarse` and `q > Q₂` (see `factorization_vanishes_at`). -/
theorem no_factorization_of_coarse_semiprime {lam : ℕ → ℝ} {Q₁ Q₂ q p₁ p₂ : ℕ}
    (_hq : q = p₁ * p₂) (_hp₁ : p₁.Prime) (_hp₂ : p₂.Prime)
    (_hp₁Q : Q₁ < p₁) (_hp₂Q : Q₁ < p₂) (hqQ : Q₂ < q)
    (hcoarse : ∀ d, d ∣ q → d ≤ Q₁ → d = 1) (hlam : lam q ≠ 0) :
    ¬ HasFactorization lam Q₁ Q₂ :=
  fun hfac => hlam (factorization_vanishes_at hfac hcoarse hqQ)

/-- A semiprime with both prime factors above `Q₁` and `Q₁ ≥ 1` is indeed
coarse, so the coarseness hypothesis above is not vacuous. -/
theorem coarse_of_semiprime {q p₁ p₂ Q₁ : ℕ} (hq : q = p₁ * p₂) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (hp₁Q : Q₁ < p₁) (hp₂Q : Q₁ < p₂) :
    ∀ d, d ∣ q → d ≤ Q₁ → d = 1 := by
  intro d hd hdQ
  rcases (Nat.dvd_mul.mp (hq ▸ hd)) with ⟨a, b, ha, hb, hab⟩
  have ha' : a = 1 ∨ a = p₁ := (Nat.dvd_prime hp₁).mp ha
  have hb' : b = 1 ∨ b = p₂ := (Nat.dvd_prime hp₂).mp hb
  rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rw [h1, h2] at hab
  · omega
  · omega
  · omega
  · exfalso
    have hle : p₁ ≤ p₁ * p₂ := Nat.le_mul_of_pos_right _ hp₂.pos
    obtain ⟨s, hs⟩ : ∃ s, p₁ * p₂ = s := ⟨_, rfl⟩
    rw [hs] at hab hle
    omega

end Gate01Switch
end TwinPrimeProject
