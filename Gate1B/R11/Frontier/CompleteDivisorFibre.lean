/-
# Gate1B / R11 / Frontier : the complete sharp divisor fibre `H_z`

Append-only module of the minimal-gap-kernel delta.  Nothing pre-existing is edited.

This module is **purely finite arithmetic**.  It fixes, once and for all, the sharp divisor
functional

```
H_z(M) = ∑_{d | M, d > z} μ(d) log(M/d)
```

(`Hdiv`), its elementary support and linearity identities, the coprime divisor splitting
(`sum_divisors_coprime_mul`), and — the workhorse of the whole delta — the **fibre reindexing**

```
∑_{d | v·m, v | d, d > z} μ(d) log(v·m/d) = μ(v) · H_{z/v}(m)      (v squarefree, gcd(v,m)=1)
```

Finally it fixes the *physical* source wrapper

```
T_C = 252 · ∑_n Ω_C(n) · H_{z_C}(n+2),
```

in which `Ω_C` is a **source parameter**, never an eleven-prime model: no theorem of this layer
inspects it.
-/
import Mathlib

namespace Gate1B.R11.Frontier

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## 1. The radical -/

/-- The radical `rad M = ∏_{p | M} p` of a natural number. -/
def radNat (M : ℕ) : ℕ := ∏ p ∈ M.primeFactors, p

@[simp] theorem radNat_one : radNat 1 = 1 := by simp [radNat]

theorem radNat_dvd (M : ℕ) : radNat M ∣ M := Nat.prod_primeFactors_dvd M

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_of_primes : ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
    Squarefree (∏ p ∈ s, p) := by
  intro s
  induction s using Finset.induction with
  | empty => intro _; simp
  | insert p s hp ih =>
      intro h
      rw [Finset.prod_insert hp]
      have hprime := h p (Finset.mem_insert_self p s)
      have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
        refine Nat.Coprime.prod_right ?_
        intro q hq
        exact (Nat.coprime_primes hprime (h q (Finset.mem_insert_of_mem hq))).2
          (by rintro rfl; exact hp hq)
      exact (Nat.squarefree_mul hcop).2
        ⟨hprime.squarefree, ih fun q hq => h q (Finset.mem_insert_of_mem hq)⟩

theorem squarefree_radNat (M : ℕ) : Squarefree (radNat M) :=
  squarefree_prod_of_primes _ fun _ hp => Nat.prime_of_mem_primeFactors hp

theorem radNat_ne_zero (M : ℕ) : radNat M ≠ 0 := (squarefree_radNat M).ne_zero

/-- The squarefree divisors of `M` are exactly the divisors of `rad M`. -/
theorem dvd_radNat_iff {M d : ℕ} (hM : M ≠ 0) :
    d ∣ radNat M ↔ d ∣ M ∧ Squarefree d := by
  constructor
  · intro h
    exact ⟨h.trans (radNat_dvd M), (squarefree_radNat M).squarefree_of_dvd h⟩
  · rintro ⟨hdvd, hsq⟩
    have : d.primeFactors ⊆ M.primeFactors := Nat.primeFactors_mono hdvd hM
    calc d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ ∣ ∏ p ∈ M.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ this
      _ = radNat M := rfl

/-! ## 2. The sharp divisor functional `H_z` -/

/-- The complete sharp divisor fibre `H_z(M) = ∑_{d|M, d>z} μ(d) log(M/d)`.

The threshold `z` is a *real* parameter (this is what makes the later contraction
`H_{z/v}` legal); the divisor variable is a natural number. -/
noncomputable def Hdiv (z : ℝ) (M : ℕ) : ℝ :=
  ∑ d ∈ M.divisors, (if z < (d : ℝ) then (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) else 0)

@[simp] theorem Hdiv_zero_arg (z : ℝ) : Hdiv z 0 = 0 := by simp [Hdiv]

/-- Non-squarefree divisors never contribute to `H_z`. -/
theorem Hdiv_eq_sum_squarefree (z : ℝ) (M : ℕ) :
    Hdiv z M =
      ∑ d ∈ M.divisors,
        (if Squarefree d then
          (if z < (d : ℝ) then (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) else 0) else 0) := by
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hsq : Squarefree d
  · simp [hsq]
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- `H_z` only sees the divisors of the radical. -/
theorem Hdiv_eq_sum_radNat (z : ℝ) {M : ℕ} (hM : M ≠ 0) :
    Hdiv z M =
      ∑ d ∈ (radNat M).divisors,
        (if z < (d : ℝ) then (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) else 0) := by
  rw [Hdiv_eq_sum_squarefree]
  have hsub : (radNat M).divisors ⊆ M.divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨((dvd_radNat_iff hM).1 hd.1).1, hM⟩
  have hzero : ∀ d ∈ M.divisors, d ∉ (radNat M).divisors →
      (if Squarefree d then
        (if z < (d : ℝ) then (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) else 0) else 0) = 0 := by
    intro d hd hnot
    rw [Nat.mem_divisors] at hd
    have hns : ¬ Squarefree d := by
      intro hsq
      exact hnot (Nat.mem_divisors.2 ⟨(dvd_radNat_iff hM).2 ⟨hd.1, hsq⟩, radNat_ne_zero M⟩)
    simp [hns]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hsq : Squarefree d :=
    (squarefree_radNat M).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  simp [hsq]

/-- Below the trivial threshold, `H_z` is the von Mangoldt function: `H_z(M) = Λ(M)` for `z < 1`. -/
theorem Hdiv_of_lt_one {z : ℝ} (hz : z < 1) (M : ℕ) :
    Hdiv z M = Λ M := by
  have hstep : Hdiv z M = ∑ d ∈ M.divisors, (μ d : ℝ) * Real.log ((M : ℝ) / (d : ℝ)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (Nat.pos_of_mem_divisors hd).ne'
    have : z < (d : ℝ) := lt_of_lt_of_le hz (by exact_mod_cast hd1)
    simp [this]
  have hmul : ((μ : ArithmeticFunction ℝ) * log) M = Λ M := by
    rw [ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
  rw [hstep]
  rw [← hmul, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (f := fun x y => ((μ : ArithmeticFunction ℝ) x) * (log y))]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mem_divisors] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hd.2 (Nat.eq_zero_of_zero_dvd hd.1)
  have : ((M / d : ℕ) : ℝ) = (M : ℝ) / (d : ℝ) := by
    rw [Nat.cast_div hd.1 (by exact_mod_cast hd0)]
  simp [ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply, this]

/-! ## 3. Coprime divisor splitting -/

/-- Divisor sums over a coprime product split as a double sum. -/
theorem sum_divisors_coprime_mul {b a : ℕ} (hb : b ≠ 0) (ha : a ≠ 0) (h : Nat.Coprime b a)
    (f : ℕ → ℝ) :
    ∑ d ∈ (b * a).divisors, f d = ∑ p ∈ b.divisors ×ˢ a.divisors, f (p.1 * p.2) := by
  refine (Finset.sum_nbij' (i := fun p => p.1 * p.2)
    (j := fun d => (Nat.gcd d b, Nat.gcd d a)) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨e, g⟩ hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp ⊢
    exact ⟨Nat.mul_dvd_mul hp.1.1 hp.2.1, by positivity⟩
  · intro d hd
    simp only [Nat.mem_divisors, Finset.mem_product] at hd ⊢
    exact ⟨⟨Nat.gcd_dvd_right d b, hb⟩, ⟨Nat.gcd_dvd_right d a, ha⟩⟩
  · rintro ⟨e, g⟩ hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp
    have hgb : Nat.Coprime g b := Nat.Coprime.coprime_dvd_left hp.2.1 h.symm
    have hea : Nat.Coprime e a := Nat.Coprime.coprime_dvd_left hp.1.1 h
    have h1 : Nat.gcd (e * g) b = e := by
      rw [Nat.Coprime.gcd_mul_right_cancel e hgb]; exact Nat.gcd_eq_left hp.1.1
    have h2 : Nat.gcd (e * g) a = g := by
      rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel g hea]; exact Nat.gcd_eq_left hp.2.1
    simp [h1, h2]
  · intro d hd
    simp only [Nat.mem_divisors] at hd
    have hcop : Nat.Coprime (Nat.gcd d b) (Nat.gcd d a) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right d b)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right d a) h)
    show Nat.gcd d b * Nat.gcd d a = d
    refine Nat.dvd_antisymm
      (hcop.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left d b) (Nat.gcd_dvd_left d a)) ?_
    calc d = Nat.gcd d (b * a) := (Nat.gcd_eq_left hd.1).symm
      _ ∣ Nat.gcd d b * Nat.gcd d a := Nat.gcd_mul_right_dvd_mul_gcd d b a
  · rintro ⟨e, g⟩ _; rfl

/-! ## 4. The fibre reindexing -/

/-- **Fibre reindexing.**  For `v` squarefree and coprime to `m`, the part of the sharp divisor
sum of `v·m` supported on the divisors *divisible by `v`* contracts to `μ(v) · H_{z/v}(m)`. -/
theorem sum_fibre_dvd (z : ℝ) {v m : ℕ} (hv : v ≠ 0) (hm : m ≠ 0) (hsq : Squarefree v)
    (hcop : Nat.Coprime v m) :
    ∑ d ∈ (v * m).divisors,
      (if v ∣ d then
        (if z < (d : ℝ) then (μ d : ℝ) * Real.log (((v * m : ℕ) : ℝ) / (d : ℝ)) else 0)
       else 0)
      = (μ v : ℝ) * Hdiv (z / v) m := by
  classical
  rw [sum_divisors_coprime_mul hv hm hcop, Finset.sum_product]
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hv
  have key : ∀ e ∈ v.divisors, ∀ g ∈ m.divisors,
      (if v ∣ e * g then
        (if z < ((e * g : ℕ) : ℝ) then
          (μ (e * g) : ℝ) * Real.log (((v * m : ℕ) : ℝ) / ((e * g : ℕ) : ℝ)) else 0)
       else 0)
      = (if e = v then
          (if z / v < (g : ℝ) then
            (μ v : ℝ) * ((μ g : ℝ) * Real.log ((m : ℝ) / (g : ℝ))) else 0)
         else 0) := by
    intro e he g hg
    simp only [Nat.mem_divisors] at he hg
    have hgv : Nat.Coprime g v := Nat.Coprime.coprime_dvd_left hg.1 hcop.symm
    by_cases hev : e = v
    · subst hev
      have hdvd : e ∣ e * g := Dvd.intro g rfl
      have hg0 : (0 : ℝ) < (g : ℝ) := by
        have : 0 < g := Nat.pos_of_dvd_of_pos hg.1 (Nat.pos_of_ne_zero hg.2)
        exact_mod_cast this
      have hcast : ((e * g : ℕ) : ℝ) = (e : ℝ) * (g : ℝ) := by push_cast; ring
      have hthr : (z < ((e * g : ℕ) : ℝ)) ↔ (z / e < (g : ℝ)) := by
        rw [hcast, div_lt_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hv), mul_comm]
      have hmu : (μ (e * g) : ℝ) = (μ e : ℝ) * (μ g : ℝ) := by
        have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hgv.symm
        push_cast [this]; ring
      have hlog : Real.log (((e * m : ℕ) : ℝ) / ((e * g : ℕ) : ℝ))
          = Real.log ((m : ℝ) / (g : ℝ)) := by
        congr 1
        push_cast
        field_simp
      simp only [hdvd, if_true, hthr, hmu, hlog]
      by_cases hc : z / (e : ℝ) < (g : ℝ) <;> simp [hc, mul_assoc]
    · have hnd : ¬ v ∣ e * g := by
        intro hdvd
        have : v ∣ e := (Nat.Coprime.dvd_of_dvd_mul_right (hgv.symm) hdvd)
        exact hev (Nat.dvd_antisymm he.1 this)
      simp [hnd, hev]
  rw [Finset.sum_congr rfl (fun e he => Finset.sum_congr rfl (fun g hg => key e he g hg))]
  rw [Finset.sum_eq_single v]
  · simp only [Hdiv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hc : z / (v : ℝ) < (g : ℝ) <;> simp [hc]
  · intro e _ hne; simp [hne]
  · intro hv'
    exact absurd (Nat.mem_divisors_self v hv) hv'

/-- **Forced fibre.**  If every surviving divisor above the threshold is divisible by the
squarefree cofactor `v`, the whole sharp fibre contracts. -/
theorem Hdiv_forced_fibre {z : ℝ} {v m : ℕ} (hv0 : v ≠ 0) (hm0 : m ≠ 0) (hsq : Squarefree v)
    (hcop : Nat.Coprime v m)
    (hforce : ∀ d, d ∣ v * m → z < (d : ℝ) → (μ d : ℝ) ≠ 0 → v ∣ d) :
    Hdiv z (v * m) = (μ v : ℝ) * Hdiv (z / v) m := by
  have hstep : Hdiv z (v * m) =
      ∑ d ∈ (v * m).divisors,
        (if v ∣ d then
          (if z < (d : ℝ) then (μ d : ℝ) * Real.log (((v * m : ℕ) : ℝ) / (d : ℝ)) else 0)
         else 0) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mem_divisors] at hd
    by_cases hvd : v ∣ d
    · rw [if_pos hvd]
    · rw [if_neg hvd]
      by_cases hz : z < (d : ℝ)
      · rw [if_pos hz]
        by_cases hmu : (μ d : ℝ) = 0
        · rw [hmu, zero_mul]
        · exact absurd (hforce d hd.1 hz hmu) hvd
      · rw [if_neg hz]
  rw [hstep]
  exact sum_fibre_dvd z hv0 hm0 hsq hcop

/-- **Prefix / von Mangoldt split.**  `H_z(m) = Λ(m) − (the prefix below the threshold)`. -/
theorem Hdiv_eq_vonMangoldt_sub_prefix (z : ℝ) (m : ℕ) :
    Hdiv z m = Λ m -
      ∑ d ∈ m.divisors, (if z < (d : ℝ) then 0
        else (μ d : ℝ) * Real.log ((m : ℝ) / (d : ℝ))) := by
  have hfull : Hdiv (0 - 1) m = Λ m := Hdiv_of_lt_one (by norm_num) m
  have hsplit : Hdiv (0 - 1) m = Hdiv z m +
      ∑ d ∈ m.divisors, (if z < (d : ℝ) then 0
        else (μ d : ℝ) * Real.log ((m : ℝ) / (d : ℝ))) := by
    rw [Hdiv, Hdiv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (Nat.pos_of_mem_divisors hd).ne'
    have hlow : (0 : ℝ) - 1 < (d : ℝ) := by
      have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      linarith
    rw [if_pos hlow]
    by_cases hz : z < (d : ℝ) <;> simp [hz]
  rw [hfull] at hsplit
  linarith

/-! ## 5. Linearity -/

theorem Hdiv_add_source (z : ℝ) (M : ℕ) (c₁ c₂ : ℝ) :
    c₁ * Hdiv z M + c₂ * Hdiv z M = (c₁ + c₂) * Hdiv z M := by ring

theorem sum_Hdiv_smul {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ℝ) (M : ι → ℕ) (c : ℝ) :
    ∑ i ∈ s, (c * w i) * Hdiv z (M i) = c * ∑ i ∈ s, w i * Hdiv z (M i) := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-! ## 6. The physical source wrapper

`Ω_C` is a **physical source parameter**.  No theorem below inspects it; in particular nothing
in this layer replaces it by an eleven-prime model. -/

variable {ι : Type*}

/-- The abstract physical divisor source `T_C = 252 ∑_n Ω_C(n) H_{z_C}(n+2)`. -/
noncomputable def Tsource (Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) : ℝ :=
  252 * ∑ n ∈ Ns, Ω n * Hdiv z ((n : ℕ) + 2)

/-- The complete divisor source over a finite family of charts. -/
noncomputable def TsourceTotal (Cs : Finset ι) (Ns : Finset ℕ) (Ω : ι → ℕ → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ C ∈ Cs, Tsource Ns (Ω C) (z C)

/-- The total source is `252` times the raw double sum: an exact finite identity. -/
theorem TsourceTotal_eq (Cs : Finset ι) (Ns : Finset ℕ) (Ω : ι → ℕ → ℝ) (z : ι → ℝ) :
    TsourceTotal Cs Ns Ω z = 252 * ∑ C ∈ Cs, ∑ n ∈ Ns, Ω C n * Hdiv (z C) (n + 2) := by
  simp [TsourceTotal, Tsource, Finset.mul_sum]

/-- Additivity of the source in the weight `Ω`: no chart is double-charged. -/
theorem Tsource_add (Ns : Finset ℕ) (Ω₁ Ω₂ : ℕ → ℝ) (z : ℝ) :
    Tsource Ns (fun n => Ω₁ n + Ω₂ n) z = Tsource Ns Ω₁ z + Tsource Ns Ω₂ z := by
  simp only [Tsource, ← Finset.sum_add_distrib, ← mul_add]
  refine congrArg _ (Finset.sum_congr rfl fun n _ => by ring)

end Gate1B.R11.Frontier
