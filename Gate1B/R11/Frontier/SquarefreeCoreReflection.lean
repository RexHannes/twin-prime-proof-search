/-
# Gate1B / R11 / Frontier : the squarefree-core reflection and the local `e`-sum

Append-only module of the minimal-gap-kernel delta.

For `M = b·a` with `a` squarefree and `gcd(a,b) = 1` we kernel-prove the exact reflected divisor
identity

```
H_z(b·a) = μ(a) ∑_{e | rad b} μ(e) ∑_{g | a, z·g < a·e} μ(g) log(b·g/e),
```

with the **strict** inequality `z·g < a·e` preserved and with no multiplicity introduced (the
reflection is a bijection of divisor charts).

Section 2 records the **local `e`-sum** as an *alternative representation*:

```
∑_{e | rad b} μ(e) log(b·g/e) = log g          if b = 1,
                              = Λ(rad b)       otherwise,
```

hence `log p` for `b = p^ν` and `0` as soon as `ω(b) ≥ 2`.  It is never subtracted as a second
owner alongside a complete source chart.
-/
import Gate1B.R11.Frontier.CompleteDivisorFibre
import Gate1B.R11.Frontier.RoughConductorDescent

namespace Gate1B.R11.Frontier

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## 0. Radical arithmetic -/

theorem radNat_of_squarefree {a : ℕ} (ha : Squarefree a) : radNat a = a :=
  Nat.prod_primeFactors_of_squarefree ha

theorem radNat_eq_one_iff {b : ℕ} (hb : b ≠ 0) : radNat b = 1 ↔ b = 1 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hne
    have hmem : p ∈ b.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpb, hb⟩
    have hdvd : p ∣ radNat b := Finset.dvd_prod_of_mem _ hmem
    rw [h] at hdvd
    have h1 := Nat.le_of_dvd one_pos hdvd
    have h2 := hp.two_le
    omega
  · rintro rfl; simp [radNat]

theorem radNat_mul_coprime {b a : ℕ} (hb : b ≠ 0) (ha : a ≠ 0) (h : Nat.Coprime b a) :
    radNat (b * a) = radNat b * radNat a := by
  rw [radNat, radNat, radNat, Nat.primeFactors_mul hb ha,
    Finset.prod_union (Nat.Coprime.disjoint_primeFactors h)]

/-- Möbius of a complementary squarefree divisor. -/
theorem moebius_div_of_squarefree {a g : ℕ} (ha : Squarefree a) (hg : g ∣ a) :
    (μ (a / g) : ℤ) = μ a * μ g := by
  obtain ⟨k, rfl⟩ := hg
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
  have hcop : Nat.Coprime g k := (Nat.squarefree_mul_iff.1 ha).1
  rw [Nat.mul_div_cancel_left _ hg0,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  have hsq : Squarefree g := (Nat.squarefree_mul_iff.1 ha).2.1
  have h1 : (μ g : ℤ) = 1 ∨ (μ g : ℤ) = -1 := by
    have hne : (μ g : ℤ) ≠ 0 := by
      rw [ArithmeticFunction.moebius_ne_zero_iff_squarefree]; exact hsq
    rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.1 hne with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases h1 with h | h <;> rw [h] <;> ring

/-! ## 1. The reflected divisor identity -/

/-- The reflected form of the sharp divisor fibre. -/
noncomputable def reflectedSum (z : ℝ) (b a : ℕ) : ℝ :=
  (μ a : ℝ) * ∑ e ∈ (radNat b).divisors, (μ e : ℝ) *
    ∑ g ∈ a.divisors,
      (if z * (g : ℝ) < ((a * e : ℕ) : ℝ) then
        (μ g : ℝ) * Real.log (((b * g : ℕ) : ℝ) / (e : ℝ)) else 0)

/-- **Squarefree-core reflection.**  Exact finite identity, strict inequality preserved. -/
theorem Hdiv_reflection {z : ℝ} {b a : ℕ} (hb : b ≠ 0) (ha : Squarefree a)
    (hcop : Nat.Coprime a b) :
    Hdiv z (b * a) = reflectedSum z b a := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hba : b * a ≠ 0 := mul_ne_zero hb ha0
  have hrb0 : radNat b ≠ 0 := radNat_ne_zero b
  have hcop' : Nat.Coprime (radNat b) a :=
    Nat.Coprime.coprime_dvd_left (radNat_dvd b) hcop.symm
  rw [Hdiv_eq_sum_radNat z hba, radNat_mul_coprime hb ha0 hcop.symm, radNat_of_squarefree ha,
    sum_divisors_coprime_mul hrb0 ha0 hcop', Finset.sum_product, reflectedSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Nat.mem_divisors] at he
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he.1 (Nat.pos_of_ne_zero hrb0)
  have heb : e ∣ b := he.1.trans (radNat_dvd b)
  have hea : Nat.Coprime e a := Nat.Coprime.coprime_dvd_left heb hcop.symm
  -- reflect the inner divisor variable
  rw [← Nat.sum_div_divisors a (fun t => (if z < ((e * t : ℕ) : ℝ) then
      (μ (e * t) : ℝ) * Real.log (((b * a : ℕ) : ℝ) / ((e * t : ℕ) : ℝ)) else 0))]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Nat.mem_divisors] at hg
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg.1 (Nat.pos_of_ne_zero ha0)
  obtain ⟨g', hg'⟩ := hg.1
  have hdivg : a / g = g' := by rw [hg', Nat.mul_div_cancel_left _ hg0]
  have hg'0 : 0 < g' := by
    rcases Nat.eq_zero_or_pos g' with rfl | h
    · simp [hg'] at ha0
    · exact h
  have hgcop : Nat.Coprime e g' := Nat.Coprime.coprime_dvd_right ⟨g, by rw [hg']; ring⟩ hea
  -- the threshold
  have hthr : (z < ((e * (a / g) : ℕ) : ℝ)) ↔ (z * (g : ℝ) < ((a * e : ℕ) : ℝ)) := by
    rw [hdivg]
    have hcast : ((e * g' : ℕ) : ℝ) = (e : ℝ) * (g' : ℝ) := by push_cast; ring
    have hga : ((a * e : ℕ) : ℝ) = (g : ℝ) * ((e : ℝ) * (g' : ℝ)) := by
      rw [hg']; push_cast; ring
    rw [hcast, hga]
    have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  -- the Möbius factor
  have hmu : (μ (e * (a / g)) : ℝ) = (μ a : ℝ) * ((μ e : ℝ) * (μ g : ℝ)) := by
    rw [hdivg, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hgcop]
    have := moebius_div_of_squarefree ha ⟨g', hg'⟩
    rw [hdivg] at this
    have hcast : ((μ g' : ℤ) : ℝ) = ((μ a : ℤ) : ℝ) * ((μ g : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at hcast ⊢
    rw [hcast]; ring
  -- the logarithm
  have hlog : Real.log (((b * a : ℕ) : ℝ) / ((e * (a / g) : ℕ) : ℝ))
      = Real.log (((b * g : ℕ) : ℝ) / (e : ℝ)) := by
    rw [hdivg]
    congr 1
    have hcast1 : ((b * a : ℕ) : ℝ) = (b : ℝ) * ((g : ℝ) * (g' : ℝ)) := by
      rw [hg']; push_cast; ring
    have hcast2 : ((e * g' : ℕ) : ℝ) = (e : ℝ) * (g' : ℝ) := by push_cast; ring
    have hcast3 : ((b * g : ℕ) : ℝ) = (b : ℝ) * (g : ℝ) := by push_cast; ring
    rw [hcast1, hcast2, hcast3]
    have he' : (e : ℝ) ≠ 0 := by
      have : (0:ℝ) < (e : ℝ) := by exact_mod_cast he0
      exact ne_of_gt this
    have hg'' : (g' : ℝ) ≠ 0 := by
      have : (0:ℝ) < (g' : ℝ) := by exact_mod_cast hg'0
      exact ne_of_gt this
    field_simp
  by_cases hc : z * (g : ℝ) < ((a * e : ℕ) : ℝ)
  · rw [if_pos (hthr.2 hc), if_pos hc, hmu, hlog]; ring
  · rw [if_neg (fun h => hc (hthr.1 h)), if_neg hc]; ring

/-! ## 2. The local `e`-sum (alternative representation) -/

/-- **Local `e`-sum.**  An alternative representation, never a second owner. -/
theorem local_e_sum {b g : ℕ} (hb : b ≠ 0) (hg : 0 < g) :
    ∑ e ∈ (radNat b).divisors, (μ e : ℝ) * Real.log (((b * g : ℕ) : ℝ) / (e : ℝ))
      = if b = 1 then Real.log g else Λ (radNat b) := by
  have hrb0 : radNat b ≠ 0 := radNat_ne_zero b
  have hsplit : ∀ e ∈ (radNat b).divisors,
      (μ e : ℝ) * Real.log (((b * g : ℕ) : ℝ) / (e : ℝ))
        = (μ e : ℝ) * Real.log ((b * g : ℕ) : ℝ) - (μ e : ℝ) * Real.log (e : ℝ) := by
    intro e he
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors he)
      (Nat.pos_of_ne_zero hrb0)
    have hbg : ((b * g : ℕ) : ℝ) ≠ 0 := by
      have hpos : 0 < b * g := Nat.mul_pos (Nat.pos_of_ne_zero hb) hg
      have : (0:ℝ) < ((b * g : ℕ) : ℝ) := by exact_mod_cast hpos
      exact ne_of_gt this
    have he' : ((e : ℕ) : ℝ) ≠ 0 := by
      have : (0:ℝ) < (e : ℝ) := by exact_mod_cast he0
      exact ne_of_gt this
    rw [Real.log_div hbg he']
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hmu : ∑ e ∈ (radNat b).divisors, (μ e : ℝ) = if radNat b = 1 then 1 else 0 := by
    by_cases hr : radNat b = 1
    · rw [if_pos hr, hr]; simp
    · rw [if_neg hr]
      have h := sum_moebius_divisors (radNat b)
      rw [if_neg hr] at h
      have hcast : ((∑ e ∈ (radNat b).divisors, (μ e : ℤ)) : ℝ) = ((0 : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h
      push_cast at hcast
      exact hcast
  have hlog : ∑ e ∈ (radNat b).divisors, (μ e : ℝ) * Real.log (e : ℝ) = - Λ (radNat b) := by
    have := ArithmeticFunction.sum_moebius_mul_log_eq (n := radNat b)
    simpa [ArithmeticFunction.log_apply] using this
  rw [hmu, hlog]
  by_cases hb1 : b = 1
  · subst hb1
    have : radNat 1 = 1 := radNat_one
    rw [if_pos this, if_pos rfl, this]
    simp
  · have hrad : radNat b ≠ 1 := fun h => hb1 ((radNat_eq_one_iff hb).1 h)
    rw [if_neg hrad, if_neg hb1]
    ring

/-- Prime-power core: the local `e`-sum is `log p`. -/
theorem local_e_sum_prime_pow {p nu g : ℕ} (hp : p.Prime) (hnu : 0 < nu) (hg : 0 < g) :
    ∑ e ∈ (radNat (p ^ nu)).divisors, (μ e : ℝ) * Real.log (((p ^ nu * g : ℕ) : ℝ) / (e : ℝ))
      = Real.log p := by
  have hb : p ^ nu ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hrad : radNat (p ^ nu) = p := by
    rw [radNat, Nat.primeFactors_prime_pow hnu.ne' hp]
    simp
  rw [local_e_sum hb hg, hrad]
  have hne : p ^ nu ≠ 1 := by
    intro h
    rcases Nat.pow_eq_one.1 h with h1 | h1
    · exact hp.one_lt.ne' h1
    · omega
  rw [if_neg hne, ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Two or more distinct prime factors: the local `e`-sum vanishes. -/
theorem local_e_sum_eq_zero_of_two_primes {b g : ℕ} (hb : b ≠ 0) (hg : 0 < g)
    (hb2 : 2 ≤ b.primeFactors.card) :
    ∑ e ∈ (radNat b).divisors, (μ e : ℝ) * Real.log (((b * g : ℕ) : ℝ) / (e : ℝ)) = 0 := by
  have hb1 : b ≠ 1 := by
    rintro rfl; simp at hb2
  rw [local_e_sum hb hg, if_neg hb1]
  have hnpp : ¬ IsPrimePow (radNat b) := by
    rintro ⟨p, k, hp, hk, hpk⟩
    have hsq : Squarefree (radNat b) := squarefree_radNat b
    have hk1 : k = 1 := by
      by_contra hne
      have h2 : p * p ∣ radNat b := by
        rw [← hpk]
        have : 2 ≤ k := by omega
        calc p * p = p ^ 2 := by ring
          _ ∣ p ^ k := pow_dvd_pow p this
      exact hp.not_unit (hsq p h2)
    subst hk1
    rw [pow_one] at hpk
    -- `rad b` is then a single prime, contradicting two distinct prime factors
    have hcard : (radNat b).primeFactors.card = 1 := by
      rw [← hpk, Nat.Prime.primeFactors (Nat.prime_iff.2 hp)]
      simp
    have hpf : (radNat b).primeFactors = b.primeFactors := by
      rw [radNat, Nat.primeFactors_prod (fun q hq => Nat.prime_of_mem_primeFactors hq)]
    rw [hpf] at hcard
    omega
  have : Λ (radNat b) = 0 := by
    by_contra hne
    exact hnpp (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hne)
  exact this

end Gate1B.R11.Frontier
