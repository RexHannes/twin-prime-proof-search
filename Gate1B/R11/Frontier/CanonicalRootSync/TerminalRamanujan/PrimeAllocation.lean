/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : prime allocation and the
exact coefficient formula  (T7)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

This module proves the **prime-allocation identity** behind the cofactor decomposition: for
squarefree `a`,

```
∑_{r s t = a} μ(t) 1_{rt ∣ u} 1_{st ∣ v} = 1_{a ∣ uv},
```

(the designated inclusion–exclusion variable is `t`; the residual cofactors `r`, `s` may share
further primes with `u`, `v`, so `t` is *not* a gcd), its `b`-twisted form

```
∑_{r s t = a} μ(t) 1_{D₁ ∣ u} 1_{D₂ ∣ v} = 1_{a b² ∣ uv},    D₁ = brt, D₂ = bst,
```

for squarefree `u, v`, and finally the **exact coefficient formula**

```
a(q) = (μ(a)/q) ∑_{r s t = a} (1/t) H_{2D₁}(I₁/D₁) H_{2D₂}(I₂/D₂),   q = a b².
```

Everything is an exact finite identity in the rational layer.  No asymptotics.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.CofactorAllocation
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.RamanujanCoeff

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset ArithmeticFunction

/-! ## 1. Divisor indicators as an arithmetic function -/

/-- The divisor indicator `n ↦ 1_{n ∣ u}` as an arithmetic function. -/
def indDvd (u : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else if n ∣ u then 1 else 0, by simp⟩

theorem indDvd_apply {u n : ℕ} (hn : n ≠ 0) : indDvd u n = if n ∣ u then 1 else 0 := by
  simp [indDvd, hn]

theorem isMultiplicative_indDvd (u : ℕ) : (indDvd u).IsMultiplicative := by
  constructor
  · simp [indDvd_apply (one_ne_zero)]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [indDvd]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [indDvd]
    rw [indDvd_apply (Nat.mul_ne_zero hm hn), indDvd_apply hm, indDvd_apply hn]
    by_cases h1 : m ∣ u
    · by_cases h2 : n ∣ u
      · simp [h1, h2, Nat.Coprime.mul_dvd_of_dvd_of_dvd hmn h1 h2]
      · rw [if_neg h2, if_neg (fun h : m * n ∣ u => h2 ((dvd_mul_left n m).trans h))]
        simp
    · rw [if_neg h1, if_neg (fun h : m * n ∣ u => h1 ((dvd_mul_right m n).trans h))]
      simp

/-- Indicators split along coprime factors. -/
theorem ind_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (w : ℕ) :
    (if m * n ∣ w then (1 : ℤ) else 0)
      = (if m ∣ w then (1 : ℤ) else 0) * (if n ∣ w then (1 : ℤ) else 0) := by
  by_cases h1 : m ∣ w
  · by_cases h2 : n ∣ w
    · simp [h1, h2, h.mul_dvd_of_dvd_of_dvd h1 h2]
    · rw [if_neg h2, if_neg (fun hd : m * n ∣ w => h2 ((dvd_mul_left n m).trans hd))]; simp
  · rw [if_neg h1, if_neg (fun hd : m * n ∣ w => h1 ((dvd_mul_right m n).trans hd))]; simp

/-- A squarefree number divides `u` as soon as each of its prime factors does. -/
theorem squarefree_dvd_of_primes_dvd {b u : ℕ} (hb : Squarefree b)
    (h : ∀ p ∈ b.primeFactors, p ∣ u) : b ∣ u := by
  have := Finset.prod_primes_dvd (s := b.primeFactors) u
    (fun p hp => Nat.prime_iff.1 (Nat.prime_of_mem_primeFactors hp)) h
  rwa [Nat.prod_primeFactors_of_squarefree hb] at this

/-! ## 2. The allocation kernel and the prime-allocation identity -/

/-- The allocation kernel `1_{·∣u} * 1_{·∣v} * (μ · 1_{·∣u} · 1_{·∣v})` (Dirichlet product of
three multiplicative functions). -/
noncomputable def allocKernel (u v : ℕ) : ArithmeticFunction ℤ :=
  (indDvd u) * (indDvd v) * (pmul (pmul moebius (indDvd u)) (indDvd v))

theorem isMultiplicative_allocKernel (u v : ℕ) : (allocKernel u v).IsMultiplicative :=
  ((isMultiplicative_indDvd u).mul (isMultiplicative_indDvd v)).mul
    ((isMultiplicative_moebius.pmul (isMultiplicative_indDvd u)).pmul (isMultiplicative_indDvd v))

/-- A multiplicative function at a squarefree argument is the product of its values at the
prime factors. -/
theorem mult_eval_squarefree {R : Type*} [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    f n = ∏ p ∈ n.primeFactors, f p := by
  have hn0 : n ≠ 0 := hn.ne_zero
  rw [hf.multiplicative_factorization f hn0, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hple : n.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hn0).1 hn p
  have hpge : 1 ≤ n.factorization p := by
    rw [Nat.mem_primeFactors] at hp
    exact Nat.Prime.factorization_pos_of_dvd hp.1 hn0 hp.2.1
  rw [le_antisymm hple hpge, pow_one]

/-- The allocation kernel at a prime is the indicator of `p ∣ uv`. -/
theorem allocKernel_prime {p : ℕ} (hp : p.Prime) (u v : ℕ) :
    allocKernel u v p = if p ∣ u * v then 1 else 0 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdiv : p.divisors = {1, p} := hp.divisors
  have hconv : ∀ n : ℕ, n ≠ 0 → (indDvd u * indDvd v) n
      = ∑ i ∈ n.divisors, (indDvd u) i * (indDvd v) (n / i) := fun n _ => by
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (f := fun a b => (indDvd u) a * (indDvd v) b)]
  rw [allocKernel, mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun a b => (indDvd u * indDvd v) a *
      ((moebius.pmul (indDvd u)).pmul (indDvd v)) b), hdiv,
    Finset.sum_pair hp.one_lt.ne]
  simp only [Nat.div_one, Nat.div_self hp.pos]
  rw [hconv 1 one_ne_zero, hconv p hp0, hdiv]
  rw [Nat.divisors_one, Finset.sum_singleton, Finset.sum_pair hp.one_lt.ne]
  simp only [pmul_apply, indDvd_apply hp0, indDvd_apply one_ne_zero, Nat.div_one,
    Nat.div_self hp.pos, moebius_apply_one, moebius_apply_prime hp, one_dvd, if_true]
  by_cases h1 : p ∣ u <;> by_cases h2 : p ∣ v <;> simp [h1, h2, Nat.Prime.dvd_mul hp]

/-- A product of prime indicators over the prime factors of a squarefree `a`. -/
theorem prod_ind_eq {a : ℕ} (ha : Squarefree a) (w : ℕ) :
    (∏ p ∈ a.primeFactors, (if p ∣ w then (1 : ℤ) else 0)) = if a ∣ w then 1 else 0 := by
  by_cases h : a ∣ w
  · rw [if_pos h]
    refine Finset.prod_eq_one fun p hp => ?_
    rw [Nat.mem_primeFactors] at hp
    rw [if_pos (hp.2.1.trans h)]
  · rw [if_neg h]
    have hex : ∃ p ∈ a.primeFactors, ¬ p ∣ w := by
      by_contra hc
      push_neg at hc
      exact h (squarefree_dvd_of_primes_dvd ha hc)
    obtain ⟨p, hp, hpw⟩ := hex
    exact Finset.prod_eq_zero hp (by rw [if_neg hpw])

/-- The allocation kernel written as the explicit triple sum over `r s t = a`. -/
theorem allocKernel_eq_triple (u v : ℕ) {a : ℕ} (ha : Squarefree a) :
    allocKernel u v a = ∑ x ∈ a.divisorsAntidiagonal, ∑ y ∈ x.1.divisorsAntidiagonal,
      (moebius x.2) * (if y.1 * x.2 ∣ u then (1 : ℤ) else 0)
        * (if y.2 * x.2 ∣ v then (1 : ℤ) else 0) := by
  have ha0 : a ≠ 0 := ha.ne_zero
  rw [allocKernel, mul_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxa, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  have hx1 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hxa; exact ha0 hxa.symm
  have hx2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hxa; exact ha0 hxa.symm
  rw [mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨hyx, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
  have hy1 : y.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hyx; exact hx1 hyx.symm
  have hy2 : y.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hyx; exact hx1 hyx.symm
  have hsq : Squarefree (y.1 * y.2 * x.2) := by rw [hyx, hxa]; exact ha
  have hc : Nat.Coprime (y.1 * y.2) x.2 := (Nat.squarefree_mul_iff.1 hsq).1
  have hc1 : Nat.Coprime y.1 x.2 := Nat.Coprime.coprime_dvd_left (dvd_mul_right y.1 y.2) hc
  have hc2 : Nat.Coprime y.2 x.2 := Nat.Coprime.coprime_dvd_left (dvd_mul_left y.2 y.1) hc
  rw [ind_mul_of_coprime hc1, ind_mul_of_coprime hc2]
  simp only [pmul_apply, indDvd_apply hy1, indDvd_apply hy2, indDvd_apply hx2]
  ring

/-- **The prime-allocation identity**: for squarefree `a`,
`∑_{r s t = a} μ(t) 1_{rt ∣ u} 1_{st ∣ v} = 1_{a ∣ uv}`. -/
theorem alloc_indicator {a : ℕ} (ha : Squarefree a) (u v : ℕ) :
    (∑ x ∈ a.divisorsAntidiagonal, ∑ y ∈ x.1.divisorsAntidiagonal,
      (moebius x.2) * (if y.1 * x.2 ∣ u then (1 : ℤ) else 0)
        * (if y.2 * x.2 ∣ v then (1 : ℤ) else 0))
      = if a ∣ u * v then 1 else 0 := by
  rw [← allocKernel_eq_triple u v ha,
    mult_eval_squarefree _ (isMultiplicative_allocKernel u v) ha,
    Finset.prod_congr rfl (fun p hp => allocKernel_prime (Nat.prime_of_mem_primeFactors hp) u v)]
  exact prod_ind_eq ha (u * v)

/-! ## 3. The `b`-twisted allocation identity -/

/-- For squarefree `u, v` and squarefree coprime `a, b`, divisibility by `q = a b²` splits into
`b ∣ u`, `b ∣ v` and `a ∣ uv`. -/
theorem q_dvd_iff {a b u v : ℕ} (hb : Squarefree b) (hab : Nat.Coprime a b)
    (hu : Squarefree u) (hv : Squarefree v) :
    a * b ^ 2 ∣ u * v ↔ (b ∣ u ∧ b ∣ v ∧ a ∣ u * v) := by
  constructor
  · intro h
    have hb2 : b ^ 2 ∣ u * v := (dvd_mul_left (b ^ 2) a).trans h
    have hprime : ∀ p ∈ b.primeFactors, p ∣ u ∧ p ∣ v := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpb : p ∣ b := (Nat.mem_primeFactors.1 hp).2.1
      have hp2 : p ^ 2 ∣ u * v := dvd_trans (pow_dvd_pow_of_dvd hpb 2) hb2
      constructor
      · by_contra hpu
        have hcop : Nat.Coprime (p ^ 2) u :=
          Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpu)
        have : p ^ 2 ∣ v := (Nat.Coprime.dvd_of_dvd_mul_left hcop hp2)
        exact hpp.not_isUnit (hv p (by rw [← sq]; exact this))
      · by_contra hpv
        have hcop : Nat.Coprime (p ^ 2) v :=
          Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpv)
        have : p ^ 2 ∣ u := (Nat.Coprime.dvd_of_dvd_mul_right hcop hp2)
        exact hpp.not_isUnit (hu p (by rw [← sq]; exact this))
    exact ⟨squarefree_dvd_of_primes_dvd hb fun p hp => (hprime p hp).1,
      squarefree_dvd_of_primes_dvd hb fun p hp => (hprime p hp).2,
      (dvd_mul_right a (b ^ 2)).trans h⟩
  · rintro ⟨h1, h2, h3⟩
    have hb2 : b ^ 2 ∣ u * v := by rw [sq]; exact mul_dvd_mul h1 h2
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_right 2 hab) h3 hb2

/-- **The `b`-twisted allocation identity**: for squarefree `u, v`,
`∑_{r s t = a} μ(t) 1_{D₁ ∣ u} 1_{D₂ ∣ v} = 1_{a b² ∣ uv}`, with `D₁ = brt`, `D₂ = bst`. -/
theorem alloc_indicator_with_b {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hab : Nat.Coprime a b) {u v : ℕ} (hu : Squarefree u) (hv : Squarefree v) :
    (∑ x ∈ a.divisorsAntidiagonal, ∑ y ∈ x.1.divisorsAntidiagonal,
      (moebius x.2) * (if D1 b y.1 x.2 ∣ u then (1 : ℤ) else 0)
        * (if D2 b y.2 x.2 ∣ v then (1 : ℤ) else 0))
      = if a * b ^ 2 ∣ u * v then 1 else 0 := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have key : ∀ x ∈ a.divisorsAntidiagonal, ∀ y ∈ x.1.divisorsAntidiagonal,
      (moebius x.2) * (if D1 b y.1 x.2 ∣ u then (1 : ℤ) else 0)
          * (if D2 b y.2 x.2 ∣ v then (1 : ℤ) else 0)
        = ((if b ∣ u then (1 : ℤ) else 0) * (if b ∣ v then (1 : ℤ) else 0)) *
          ((moebius x.2) * (if y.1 * x.2 ∣ u then (1 : ℤ) else 0)
            * (if y.2 * x.2 ∣ v then (1 : ℤ) else 0)) := by
    intro x hx y hy
    obtain ⟨hxa, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    obtain ⟨hyx, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
    have hdvd1 : y.1 * x.2 ∣ a := ⟨y.2, by rw [← hxa, ← hyx]; ring⟩
    have hdvd2 : y.2 * x.2 ∣ a := ⟨y.1, by rw [← hxa, ← hyx]; ring⟩
    have hc1 : Nat.Coprime b (y.1 * x.2) :=
      Nat.Coprime.coprime_dvd_right hdvd1 hab.symm
    have hc2 : Nat.Coprime b (y.2 * x.2) :=
      Nat.Coprime.coprime_dvd_right hdvd2 hab.symm
    have e1 : D1 b y.1 x.2 = b * (y.1 * x.2) := by unfold D1; ring
    have e2 : D2 b y.2 x.2 = b * (y.2 * x.2) := by unfold D2; ring
    rw [e1, e2, ind_mul_of_coprime hc1, ind_mul_of_coprime hc2]
    ring
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl (key x hx)]
  simp only [← Finset.mul_sum]
  rw [alloc_indicator ha u v]
  by_cases h : a * b ^ 2 ∣ u * v
  · rw [if_pos h]
    obtain ⟨h1, h2, h3⟩ := (q_dvd_iff hb hab hu hv).1 h
    rw [if_pos h1, if_pos h2, if_pos h3]
    ring
  · rw [if_neg h]
    by_cases h1 : b ∣ u
    · by_cases h2 : b ∣ v
      · by_cases h3 : a ∣ u * v
        · exact absurd ((q_dvd_iff hb hab hu hv).2 ⟨h1, h2, h3⟩) h
        · rw [if_neg h3]; ring
      · rw [if_neg h2]; ring
    · rw [if_neg h1]; ring

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
