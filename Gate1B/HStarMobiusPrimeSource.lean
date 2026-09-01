import Gate1B.HStarTwoAnchorPhysicalSource

/-!
# Gate 1B · clean **Möbius-prime source** typing and the finite `Λ♯` source

Exact arithmetic and exact finite algebra only.  Every analytic statement about
`Λ♯` is left as an explicit, **uninhabited** interface.

## Contents

* §1 the clean squarefree cell `q = d · wp` with `wp` prime, `wp ∤ d`, and its
  Möbius value;
* §2 the **common-`g` Möbius factorisation**: for `d i = g · e i` with `g`
  squarefree and coprime to both `e i`,
  `μ(d₁)μ(d₂) = μ(e₁)μ(e₂)` — the common `g`-sign appears squared.  **No
  cancellation is claimed in `e₁, e₂`** and the corresponding overclaim is
  explicitly refuted;
* §3 the **prime-typing firewall**: extracted Ford primes `π` and Vaughan
  primes `wp` are separate types with separate role tags; `wp > g ⇒ wp ∤ g`;
  no-cross-incidence for a shared gcd;
* §4 the finite source coefficient `LambdaSharp`, its support lemma and its
  deterministic multiplicity / Cauchy bounds;
* §5 the nonzero-shift autocorrelation: opening the source imposes
  `e₁wp₁ − e₂wp₂ = H`.  The cancellation itself is the **uninhabited**
  interface `LambdaSharpNonzeroShiftBound`, with a non-vacuity guard;
* §6 the **uninhabited** `LambdaSharpL2Input` interface.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarMobiusPrime

open Finset ArithmeticFunction

/-! ## 1. The clean squarefree cell -/

/-- A **clean squarefree cell** `q = d · wp` with `wp` prime and `wp ∤ d`. -/
structure CleanSquarefreeCell where
  d : ℕ
  wp : ℕ
  wp_prime : Nat.Prime wp
  wp_not_dvd_d : ¬ wp ∣ d

namespace CleanSquarefreeCell

variable (C : CleanSquarefreeCell)

/-- The modulus of the cell. -/
def q : ℕ := C.d * C.wp

theorem coprime_d_wp : Nat.Coprime C.d C.wp :=
  ((Nat.Prime.coprime_iff_not_dvd C.wp_prime).2 C.wp_not_dvd_d).symm

/-- **Möbius value of a clean cell.**  `μ(q) = −μ(d)`. -/
theorem moebius_q : moebius C.q = - moebius C.d := by
  rw [q, isMultiplicative_moebius.map_mul_of_coprime C.coprime_d_wp,
    moebius_apply_prime C.wp_prime]
  ring

end CleanSquarefreeCell

/-! ## 2. The common-`g` Möbius factorisation -/

/-- **BOXED.**  For `d i = g e i` with `g` squarefree and coprime to each `e i`,

`μ(d₁) μ(d₂) = μ(e₁) μ(e₂)`,

because the common `g`-sign occurs squared. -/
theorem moebius_common_g_cancel {g e1 e2 : ℕ} (hg : Squarefree g)
    (h1 : Nat.Coprime g e1) (h2 : Nat.Coprime g e2) :
    moebius (g * e1) * moebius (g * e2) = moebius e1 * moebius e2 := by
  rw [isMultiplicative_moebius.map_mul_of_coprime h1,
    isMultiplicative_moebius.map_mul_of_coprime h2]
  have hsq : moebius g ^ 2 = 1 := moebius_sq_eq_one_of_squarefree hg
  calc moebius g * moebius e1 * (moebius g * moebius e2)
      = moebius g ^ 2 * (moebius e1 * moebius e2) := by ring
    _ = moebius e1 * moebius e2 := by rw [hsq, one_mul]

/-- **Counterguard.**  No cancellation is available in the residual Möbius
factors: `μ(e₁)μ(e₂) = 1` is false in general (`e₁ = 2`, `e₂ = 1`). -/
theorem no_cancellation_in_residual_moebius :
    ∃ e1 e2 : ℕ, moebius e1 * moebius e2 ≠ 1 := by
  refine ⟨2, 1, ?_⟩
  rw [moebius_apply_prime Nat.prime_two]
  simp

/-! ## 3. The prime-typing firewall -/

/-- The two prime **roles** of the source.  They are distinct constructors and
are never identified. -/
inductive PrimeRole
  /-- An extracted Ford prime `π`. -/
  | fordExtracted
  /-- A Vaughan prime `wp`. -/
  | vaughan
  deriving DecidableEq, Repr

theorem primeRole_ford_ne_vaughan :
    PrimeRole.fordExtracted ≠ PrimeRole.vaughan := by decide

/-- An **extracted Ford prime**, carrying its own role tag. -/
structure FordPrime where
  val : ℕ
  val_prime : Nat.Prime val
  role : PrimeRole := PrimeRole.fordExtracted
  role_eq : role = PrimeRole.fordExtracted := by rfl

/-- A **Vaughan prime**, carrying its own role tag. -/
structure VaughanPrime where
  val : ℕ
  val_prime : Nat.Prime val
  role : PrimeRole := PrimeRole.vaughan
  role_eq : role = PrimeRole.vaughan := by rfl

/-- **Typing firewall.**  Equality of the underlying values does *not* identify
the two roles: the same prime can occur in both roles, and the roles remain
distinct. -/
theorem value_does_not_determine_role :
    ∃ (f : FordPrime) (v : VaughanPrime), f.val = v.val ∧ f.role ≠ v.role := by
  refine ⟨⟨3, Nat.prime_three, PrimeRole.fordExtracted, rfl⟩,
    ⟨3, Nat.prime_three, PrimeRole.vaughan, rfl⟩, rfl, ?_⟩
  exact primeRole_ford_ne_vaughan

/-- **Large Vaughan prime.**  A Vaughan prime exceeding the positive common
part `g` cannot divide `g`. -/
theorem vaughan_not_dvd_g_of_gt {wp g : ℕ} (hg : 0 < g) (hgt : g < wp) :
    ¬ wp ∣ g := fun hdvd => absurd (Nat.le_of_dvd hg hdvd) (Nat.not_le.2 hgt)

/-- **No cross-incidence.**  If `wp` divides `q₁` but not the gcd `g` of
`q₁, q₂`, then `wp` does not divide `q₂`. -/
theorem no_cross_incidence {wp q1 q2 g : ℕ} (hg : g = Nat.gcd q1 q2)
    (h1 : wp ∣ q1) (hng : ¬ wp ∣ g) : ¬ wp ∣ q2 := by
  intro h2
  exact hng (hg ▸ Nat.dvd_gcd h1 h2)

/-! ## 4. The finite `Λ♯` source coefficient -/

/-- The finite source coefficient

`Λ♯(m) = ∑_{e·wp = m, e ∈ E, wp ∈ P} μ(e) · logWeight(wp)`,

with an **abstract** complex prime weight `w` (no real logarithm is used, and
no analytic property of `w` is assumed). -/
noncomputable def LambdaSharp (E P : Finset ℕ) (w : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ e ∈ m.divisors, if e ∈ E ∧ m / e ∈ P then (moebius e : ℂ) * w (m / e) else 0

/-- **Support lemma.**  A nonzero value of `Λ♯` at `m` opens the source: `m`
factors as `e · p` with `e` in the Möbius set and `p` in the prime set. -/
theorem lambdaSharp_support {E P : Finset ℕ} {w : ℕ → ℂ} {m : ℕ}
    (h : LambdaSharp E P w m ≠ 0) : ∃ e ∈ E, ∃ p ∈ P, e * p = m := by
  classical
  by_contra hc
  push_neg at hc
  refine h (Finset.sum_eq_zero ?_)
  intro e he
  by_cases hcond : e ∈ E ∧ m / e ∈ P
  · exfalso
    have hdvd : e ∣ m := (Nat.mem_divisors.1 he).1
    exact hc e hcond.1 (m / e) hcond.2 (Nat.mul_div_cancel' hdvd)
  · simp [hcond]

/-- **Deterministic multiplicity bound.**  `‖Λ♯(m)‖ ≤ τ(m) · W` whenever the
prime weight is bounded by `W`. -/
theorem norm_lambdaSharp_le {E P : Finset ℕ} {w : ℕ → ℂ} {W : ℝ}
    (hw : ∀ p, ‖w p‖ ≤ W) (m : ℕ) :
    ‖LambdaSharp E P w m‖ ≤ (m.divisors.card : ℝ) * W := by
  classical
  have hW : 0 ≤ W := le_trans (norm_nonneg (w 1)) (hw 1)
  have hterm : ∀ e ∈ m.divisors,
      ‖(if e ∈ E ∧ m / e ∈ P then (moebius e : ℂ) * w (m / e) else 0)‖ ≤ W := by
    intro e _
    by_cases hcond : e ∈ E ∧ m / e ∈ P
    · rw [if_pos hcond, norm_mul]
      have hmu : ‖((moebius e : ℤ) : ℂ)‖ ≤ 1 := by
        have h := abs_moebius_le_one (n := e)
        rw [show ‖((moebius e : ℤ) : ℂ)‖ = |((moebius e : ℤ) : ℝ)| by simp]
        exact_mod_cast h
      calc ‖((moebius e : ℤ) : ℂ)‖ * ‖w (m / e)‖ ≤ 1 * W :=
            mul_le_mul hmu (hw _) (norm_nonneg _) zero_le_one
        _ = W := one_mul W
    · rw [if_neg hcond]; simpa using hW
  calc ‖LambdaSharp E P w m‖
      ≤ ∑ e ∈ m.divisors,
          ‖(if e ∈ E ∧ m / e ∈ P then (moebius e : ℂ) * w (m / e) else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _e ∈ m.divisors, W := Finset.sum_le_sum hterm
    _ = (m.divisors.card : ℝ) * W := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Deterministic finite Cauchy bound** for a weighted `Λ♯`-sum. -/
theorem lambdaSharp_cauchy {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => le_of_eq (norm_mul _ _)
  have hnn : 0 ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2
      ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)
  exact le_trans (by nlinarith [norm_nonneg (∑ i ∈ s, a i * b i), h1, hnn]) h2

/-! ## 5. The nonzero-shift autocorrelation -/

/-- The finite shifted autocorrelation of two `Λ♯`-sources over a finite index
set of `m`'s, with the second argument evaluated at the shifted point `n m`. -/
noncomputable def shiftAutocorrelation (E1 P1 E2 P2 : Finset ℕ) (w1 w2 : ℕ → ℂ)
    (S : Finset ℕ) (n : ℕ → ℕ) : ℂ :=
  ∑ m ∈ S, LambdaSharp E1 P1 w1 m * (starRingEnd ℂ) (LambdaSharp E2 P2 w2 (n m))

/-- **Opening the source imposes the shift equation.**  If both `Λ♯` factors are
nonzero at points differing by `H`, the underlying source variables satisfy

`e₁ wp₁ − e₂ wp₂ = H`. -/
theorem opened_shift_equation {E1 P1 E2 P2 : Finset ℕ} {w1 w2 : ℕ → ℂ}
    {m n : ℕ} {H : ℤ} (hm : LambdaSharp E1 P1 w1 m ≠ 0)
    (hn : LambdaSharp E2 P2 w2 n ≠ 0) (hH : (m : ℤ) - (n : ℤ) = H) :
    ∃ e1 ∈ E1, ∃ p1 ∈ P1, ∃ e2 ∈ E2, ∃ p2 ∈ P2,
      ((e1 : ℤ) * p1) - ((e2 : ℤ) * p2) = H := by
  obtain ⟨e1, he1, p1, hp1, h1⟩ := lambdaSharp_support hm
  obtain ⟨e2, he2, p2, hp2, h2⟩ := lambdaSharp_support hn
  refine ⟨e1, he1, p1, hp1, e2, he2, p2, hp2, ?_⟩
  have h1' : ((e1 * p1 : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast h1
  have h2' : ((e2 * p2 : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast h2
  push_cast at h1' h2'
  rw [h1', h2']
  exact hH

/-- **Non-vacuity guard.**  `Λ♯` is not identically zero: for `E = {1}`,
`P = {2}` and the constant weight `1`, `Λ♯(2) = 1`.  Hence a nonzero-shift
cancellation statement is a genuine analytic claim about a nonzero object. -/
theorem lambdaSharp_not_identically_zero :
    LambdaSharp {1} {2} (fun _ => 1) 2 = 1 := by
  simp [LambdaSharp, show Nat.divisors 2 = {1, 2} from by decide]

/-- **OPEN INTERFACE — never inhabited.**  A nonzero-shift cancellation bound
for the `Λ♯` autocorrelation.  No axiom asserts it, no instance is provided,
and no theorem of this bank constructs one. -/
structure LambdaSharpNonzeroShiftBound where
  /-- The implied constant. -/
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- The cancellation claim, uniform in the source data and in the nonzero
  shift `H`. -/
  cancellation :
    ∀ (E1 P1 E2 P2 : Finset ℕ) (w1 w2 : ℕ → ℂ) (Mlen H : ℕ), 0 < H →
      (∀ p, ‖w1 p‖ ≤ 1) → (∀ p, ‖w2 p‖ ≤ 1) →
      ‖shiftAutocorrelation E1 P1 E2 P2 w1 w2 (Finset.Icc (H + 1) Mlen)
          (fun m => m - H)‖
        ≤ const * (Mlen : ℝ) / Real.log ((Mlen : ℝ) + 2)

/-- **Deterministic consequence** of the (never supplied) nonzero-shift
interface: the same bound with an arbitrary bounded amplitude `A`. -/
theorem shift_bound_of_interface (I : LambdaSharpNonzeroShiftBound)
    (E1 P1 E2 P2 : Finset ℕ) (w1 w2 : ℕ → ℂ) (Mlen H : ℕ) (hH : 0 < H)
    (h1 : ∀ p, ‖w1 p‖ ≤ 1) (h2 : ∀ p, ‖w2 p‖ ≤ 1) {A : ℝ} (hA : 1 ≤ A) :
    ‖shiftAutocorrelation E1 P1 E2 P2 w1 w2 (Finset.Icc (H + 1) Mlen)
        (fun m => m - H)‖
      ≤ A * I.const * (Mlen : ℝ) / Real.log ((Mlen : ℝ) + 2) := by
  have hbase := I.cancellation E1 P1 E2 P2 w1 w2 Mlen H hH h1 h2
  have hmono : I.const * (Mlen : ℝ) / Real.log ((Mlen : ℝ) + 2)
      ≤ A * I.const * (Mlen : ℝ) / Real.log ((Mlen : ℝ) + 2) := by
    have hlog : 0 < Real.log ((Mlen : ℝ) + 2) := by
      refine Real.log_pos ?_
      have : (0 : ℝ) ≤ (Mlen : ℝ) := Nat.cast_nonneg Mlen
      linarith
    have hnum : I.const * (Mlen : ℝ) ≤ A * I.const * (Mlen : ℝ) := by
      have : (0 : ℝ) ≤ I.const * (Mlen : ℝ) :=
        mul_nonneg I.const_nonneg (by positivity)
      nlinarith [this]
    gcongr
  exact le_trans hbase hmono

/-! ## 6. The `Λ♯` mean-square interface -/

/-- **OPEN INTERFACE — never inhabited.**  The mean-square (`L²`) input
`∑_{m ≤ M} |Λ♯(m)|² ≪ M log W`.  It is *not* proved here: the underlying
number-theoretic counting inputs are not formalised in this repository. -/
structure LambdaSharpL2Input where
  const : ℝ
  const_nonneg : 0 ≤ const
  l2 :
    ∀ (E P : Finset ℕ) (w : ℕ → ℂ) (Mlen W : ℕ),
      (∀ p, ‖w p‖ ≤ Real.log ((W : ℝ) + 2)) →
      (∑ m ∈ Finset.Icc 1 Mlen, ‖LambdaSharp E P w m‖ ^ 2)
        ≤ const * (Mlen : ℝ) * Real.log ((W : ℝ) + 2)

end HStarMobiusPrime
end CurrentProgramme
end TwinPrimeProject
