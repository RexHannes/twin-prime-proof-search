/-
# Gate1B / R11 / Frontier : the genuine three-factor selected modulus owner

Append-only module of the *residue-aware* delta.  Nothing pre-existing is edited, renamed or
weakened.

This module fixes, as **exact finite algebra**, two things:

* the selected coefficient `lambdaStar` of a genuine three-factor modulus owner

  ```
  d = d₁ d₂ d₃ ,      lambdaStar d = ∑_{d₁d₂d₃ = d} γ₁(d₁) γ₂(d₂) γ₃(d₃) ,
  ```

  together with its exact support law and the pairwise-coprimality of the three factors on
  squarefree moduli;

* the **selected centered consumer**

  ```
  δ_d(n) = 1_{d | n+2} ,   u_d(n) = 1_{(n,d)=1} ,   centered_d(n) = δ_d(n) − u_d(n)/φ(d) ,
  ```

  in the repository's exact rational coefficient setting.

**No analytic bound is asserted anywhere in this module.**  The numerical rectangular estimate is
carried as the interface `PascadiRectangularInput`, a `Prop`-valued structure which is *never*
inhabited here and is *not* an axiom.
-/
import Mathlib

namespace Gate1B.R11.Frontier

open Finset

/-! ## 1. Dirichlet convolution of exact rational coefficients -/

/-- Dirichlet convolution of exact rational coefficient sequences. -/
def dmulQ (f g : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2

@[simp] theorem dmulQ_zero (f g : ℕ → ℚ) : dmulQ f g 0 = 0 := by
  simp [dmulQ]

/-- **The selected three-factor coefficient.**  `lambdaStar γ₁ γ₂ γ₃ d` is the sum of
`γ₁(d₁) γ₂(d₂) γ₃(d₃)` over all ordered factorisations `d = d₁ d₂ d₃`. -/
def lambdaStar (g1 g2 g3 : ℕ → ℚ) : ℕ → ℚ := dmulQ (dmulQ g1 g2) g3

/-- The exact triple-sum form of the selected coefficient. -/
theorem lambdaStar_apply (g1 g2 g3 : ℕ → ℚ) (d : ℕ) :
    lambdaStar g1 g2 g3 d
      = ∑ p ∈ d.divisorsAntidiagonal, ∑ q ∈ p.1.divisorsAntidiagonal,
          g1 q.1 * g2 q.2 * g3 p.2 := by
  unfold lambdaStar dmulQ
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]

/-- Exact support: the selected coefficient vanishes at `0`. -/
@[simp] theorem lambdaStar_zero (g1 g2 g3 : ℕ → ℚ) : lambdaStar g1 g2 g3 0 = 0 := by
  simp [lambdaStar]

/-- Exact value at `1`. -/
theorem lambdaStar_one (g1 g2 g3 : ℕ → ℚ) :
    lambdaStar g1 g2 g3 1 = g1 1 * g2 1 * g3 1 := by
  simp [lambdaStar, dmulQ, Nat.divisorsAntidiagonal_one]

/-- **Exact support law.**  A nonzero value of the selected coefficient exhibits an actual
three-factor factorisation with all three source coefficients nonzero. -/
theorem lambdaStar_support {g1 g2 g3 : ℕ → ℚ} {d : ℕ} (h : lambdaStar g1 g2 g3 d ≠ 0) :
    ∃ d1 d2 d3, d1 * d2 * d3 = d ∧ g1 d1 ≠ 0 ∧ g2 d2 ≠ 0 ∧ g3 d3 ≠ 0 := by
  rw [lambdaStar, dmulQ] at h
  obtain ⟨p, hp, hpne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hpd : p.1 * p.2 = d := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have h1 : dmulQ g1 g2 p.1 ≠ 0 := fun h0 => hpne (by rw [h0, zero_mul])
  have h2 : g3 p.2 ≠ 0 := fun h0 => hpne (by rw [h0, mul_zero])
  rw [dmulQ] at h1
  obtain ⟨q, hq, hqne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hqp : q.1 * q.2 = p.1 := (Nat.mem_divisorsAntidiagonal.mp hq).1
  exact ⟨q.1, q.2, p.2, by rw [hqp, hpd], fun h0 => hqne (by rw [h0, zero_mul]),
    fun h0 => hqne (by rw [h0, mul_zero]), h2⟩

/-- **Coprimality of the three selected factors on squarefree moduli.**  On a squarefree modulus
the three factors of the owner are automatically pairwise coprime, and each is squarefree. -/
theorem threeFactor_pairwise_coprime {d1 d2 d3 d : ℕ} (hd : Squarefree d)
    (hfac : d1 * d2 * d3 = d) :
    Nat.Coprime d1 d2 ∧ Nat.Coprime d1 d3 ∧ Nat.Coprime d2 d3 ∧
      Squarefree d1 ∧ Squarefree d2 ∧ Squarefree d3 := by
  subst hfac
  rw [Nat.squarefree_mul_iff] at hd
  obtain ⟨hcop12_3, hd12, hd3⟩ := hd
  rw [Nat.squarefree_mul_iff] at hd12
  obtain ⟨hcop12, hd1, hd2⟩ := hd12
  refine ⟨hcop12, ?_, ?_, hd1, hd2, hd3⟩
  · exact Nat.Coprime.coprime_dvd_left (Dvd.intro d2 rfl) hcop12_3
  · exact Nat.Coprime.coprime_dvd_left (Dvd.intro_left d1 rfl) hcop12_3

/-- The number of ordered three-factor factorisations, `τ₃`. -/
def tau3 (d : ℕ) : ℕ := ∑ p ∈ d.divisorsAntidiagonal, p.1.divisorsAntidiagonal.card

/-- **Divisor bound.**  Unit-bounded source coefficients give a `τ₃`-bounded selected
coefficient: the only cost of the three-factor structure is a divisor factor. -/
theorem abs_lambdaStar_le_tau3 {g1 g2 g3 : ℕ → ℚ} (h1 : ∀ n, |g1 n| ≤ 1)
    (h2 : ∀ n, |g2 n| ≤ 1) (h3 : ∀ n, |g3 n| ≤ 1) (d : ℕ) :
    |lambdaStar g1 g2 g3 d| ≤ (tau3 d : ℚ) := by
  rw [lambdaStar_apply, tau3]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  push_cast
  refine Finset.sum_le_sum fun p _ => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have : ∀ q ∈ p.1.divisorsAntidiagonal, |g1 q.1 * g2 q.2 * g3 p.2| ≤ (1 : ℚ) := by
    intro q _
    rw [abs_mul, abs_mul]
    calc |g1 q.1| * |g2 q.2| * |g3 p.2| ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul (h1 _) (h2 _) (abs_nonneg _) zero_le_one) (h3 _)
            (abs_nonneg _) (by positivity)
      _ = 1 := by ring
  refine le_trans (Finset.sum_le_sum this) ?_
  simp

/-! ## 2. The selected centered consumer -/

/-- `δ_d(n) = 1_{n ≡ −2 (mod d)}`, written in ℕ as `d ∣ n + 2`. -/
def deltaSel (d n : ℕ) : ℚ := if d ∣ n + 2 then 1 else 0

/-- `u_d(n) = 1_{(n,d)=1}`. -/
def uSel (d n : ℕ) : ℚ := if Nat.gcd n d = 1 then 1 else 0

/-- The selected **centered** kernel `centered_d(n) = δ_d(n) − u_d(n)/φ(d)`. -/
def centeredSel (d n : ℕ) : ℚ := deltaSel d n - uSel d n / (Nat.totient d : ℚ)

@[simp] theorem deltaSel_one (n : ℕ) : deltaSel 1 n = 1 := by simp [deltaSel]

@[simp] theorem uSel_one (n : ℕ) : uSel 1 n = 1 := by simp [uSel]

/-- The trivial modulus carries no centered mass. -/
@[simp] theorem centeredSel_one (n : ℕ) : centeredSel 1 n = 0 := by
  simp [centeredSel]

/-- Both parts of the centered kernel are `0`/`1`-valued and nonnegative. -/
theorem deltaSel_nonneg (d n : ℕ) : 0 ≤ deltaSel d n := by
  unfold deltaSel; split <;> norm_num

theorem uSel_nonneg (d n : ℕ) : 0 ≤ uSel d n := by
  unfold uSel; split <;> norm_num

/-- **The finite selected consumer.**  A finite modulus set, a finite `n`-window, the selected
coefficient and an arbitrary source coefficient.  No analytic bound is asserted. -/
def selectedConsumer (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (a : ℕ → ℚ) : ℚ :=
  ∑ d ∈ Ds, lam d * ∑ n ∈ Ns, a n * centeredSel d n

/-- The consumer is linear in the source coefficient. -/
theorem selectedConsumer_add (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (a b : ℕ → ℚ) :
    selectedConsumer lam Ds Ns (fun n => a n + b n)
      = selectedConsumer lam Ds Ns a + selectedConsumer lam Ds Ns b := by
  unfold selectedConsumer
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun n _ => ?_)
  ring

/-- The consumer is linear in the selected coefficient. -/
theorem selectedConsumer_smul (c : ℚ) (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (a : ℕ → ℚ) :
    selectedConsumer (fun d => c * lam d) Ds Ns a = c * selectedConsumer lam Ds Ns a := by
  unfold selectedConsumer
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-! ## 3. The external analytic interface

The numerical rectangular estimate for the three-factor selected owner is **not** formalised: it
is an external analytic theorem.  It is represented by the following `Prop`-valued interface,
which is never inhabited in this repository and is not an axiom. -/

/-- **`PascadiRectangularInput`** — the external analytic input for the selected three-factor
owner, as a theorem parameter.  Inhabiting it is exactly the (unformalised) analytic work. -/
structure PascadiRectangularInput (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (a : ℕ → ℚ)
    (x L S0 C : ℝ) : Prop where
  /-- The rectangular estimate for the selected consumer. -/
  rectangular : |((selectedConsumer lam Ds Ns a : ℚ) : ℝ)| ≤ C * x * L ^ (-S0)

/-- The interface is load-bearing exactly where it is used: this is its only consequence. -/
theorem selectedConsumer_bound_of_pascadi {lam : ℕ → ℚ} {Ds Ns : Finset ℕ} {a : ℕ → ℚ}
    {x L S0 C : ℝ} (h : PascadiRectangularInput lam Ds Ns a x L S0 C) :
    |((selectedConsumer lam Ds Ns a : ℚ) : ℝ)| ≤ C * x * L ^ (-S0) :=
  h.rectangular

end Gate1B.R11.Frontier
