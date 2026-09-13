/-
# Gate1B / R11 / Frontier : the Schinzel–Szekeres gap function `Fgap`

Append-only module of the minimal-gap-kernel delta.

```
Fgap(d) = max_{v | d, v > 1} v · P⁻(v),      Fgap(1) = 1,
```

with `P⁻ = Nat.minFac`.  This module fixes the **finite definition** and the exact lemmas that
the minimal-kernel coordinate uses downstream:

* monotonicity along divisibility;
* the divisor bound `v · P⁻(v) ≤ Fgap d`;
* the **structure theorem** `Fgap d = max_{p | d} p · (the part of d supported on primes ≥ p)`,
  and its squarefree specialisation — the prime-factor formula of the research source.

The classical relation `Fgap(d) = d · G(d)` with `G` the maximal ratio of consecutive divisors is
**not** proved here; it is recorded as an explicit theorem interface in `DenseSupportFirewall`,
never as an axiom.
-/
import Gate1B.R11.Frontier.SquarefullCore

namespace Gate1B.R11.Frontier

open Finset

/-! ## 1. The gap function -/

/-- The Schinzel–Szekeres function `Fgap(d) = max_{v|d, v>1} v·P⁻(v)`, with `Fgap 1 = 1`. -/
def Fgap (d : ℕ) : ℕ := max 1 ({v ∈ d.divisors | 1 < v}.sup fun v => v * v.minFac)

@[simp] theorem Fgap_one : Fgap 1 = 1 := by
  simp [Fgap]

theorem one_le_Fgap (d : ℕ) : 1 ≤ Fgap d := le_max_left _ _

/-- Every divisor `v > 1` contributes to `Fgap`. -/
theorem le_Fgap {d v : ℕ} (hd : d ≠ 0) (hv : v ∣ d) (h1 : 1 < v) :
    v * v.minFac ≤ Fgap d :=
  le_max_of_le_right (Finset.le_sup (f := fun v => v * v.minFac)
    (Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hv, hd⟩, h1⟩))

theorem self_mul_minFac_le_Fgap {d : ℕ} (hd : d ≠ 0) (h1 : 1 < d) :
    d * d.minFac ≤ Fgap d := le_Fgap hd dvd_rfl h1

/-- `Fgap d ≤ x` is exactly the statement that all divisors are `x`-dense. -/
theorem Fgap_le_iff {d x : ℕ} (hd : d ≠ 0) (hx : 1 ≤ x) :
    Fgap d ≤ x ↔ ∀ v, v ∣ d → 1 < v → v * v.minFac ≤ x := by
  constructor
  · intro h v hv h1; exact le_trans (le_Fgap hd hv h1) h
  · intro h
    refine max_le hx (Finset.sup_le fun v hv => ?_)
    rw [Finset.mem_filter, Nat.mem_divisors] at hv
    exact h v hv.1.1 hv.2

/-- `Fgap` is monotone along divisibility. -/
theorem Fgap_mono {v d : ℕ} (hd : d ≠ 0) (hvd : v ∣ d) : Fgap v ≤ Fgap d := by
  have hv : v ≠ 0 := by rintro rfl; exact hd (Nat.eq_zero_of_zero_dvd hvd)
  refine (Fgap_le_iff hv (one_le_Fgap d)).2 fun w hw h1 => le_Fgap hd (hw.trans hvd) h1

/-! ## 2. The structure theorem -/

/-- The part of `d` supported on the primes `≥ p`. -/
def tailPart (d p : ℕ) : ℕ := ∏ q ∈ d.primeFactors with p ≤ q, q ^ d.factorization q

theorem tailPart_ne_zero (d p : ℕ) : tailPart d p ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hq => pow_ne_zero _
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1).ne_zero

theorem factorization_tailPart (d p q : ℕ) :
    (tailPart d p).factorization q =
      if q ∈ d.primeFactors ∧ p ≤ q then d.factorization q else 0 := by
  classical
  rw [tailPart, factorization_prod_prime_pow
    (fun r hr => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hr).1)]
  by_cases h : q ∈ d.primeFactors ∧ p ≤ q
  · rw [if_pos (Finset.mem_filter.2 ⟨h.1, h.2⟩), if_pos h]
  · rw [if_neg (fun hmem => h ⟨(Finset.mem_filter.1 hmem).1, (Finset.mem_filter.1 hmem).2⟩),
      if_neg h]

theorem tailPart_dvd {d p : ℕ} (hd : d ≠ 0) : tailPart d p ∣ d := by
  rw [← Nat.factorization_le_iff_dvd (tailPart_ne_zero d p) hd]
  intro q
  rw [factorization_tailPart]
  by_cases h : q ∈ d.primeFactors ∧ p ≤ q
  · rw [if_pos h]
  · rw [if_neg h]; exact Nat.zero_le _

/-- Any divisor whose prime factors are all `≥ p` divides the `p`-tail. -/
theorem dvd_tailPart {d p v : ℕ} (hd : d ≠ 0) (hvd : v ∣ d) (hv : v ≠ 0)
    (hprimes : ∀ q, q.Prime → q ∣ v → p ≤ q) : v ∣ tailPart d p := by
  rw [← Nat.factorization_le_iff_dvd hv (tailPart_ne_zero d p)]
  intro q
  rw [factorization_tailPart]
  by_cases hq : v.factorization q = 0
  · rw [hq]; positivity
  · have hmem : q ∈ v.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hmem
    have hqv : q ∣ v := Nat.dvd_of_mem_primeFactors hmem
    have hqd : q ∈ d.primeFactors := Nat.mem_primeFactors.2 ⟨hqp, hqv.trans hvd, hd⟩
    rw [if_pos ⟨hqd, hprimes q hqp hqv⟩]
    exact (Nat.factorization_le_iff_dvd hv hd).2 hvd q

theorem one_lt_tailPart {d p : ℕ} (hd : d ≠ 0) (hp : p ∈ d.primeFactors) : 1 < tailPart d p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ tailPart d p := by
    refine dvd_trans (dvd_pow_self p ?_) (Finset.dvd_prod_of_mem _
      (Finset.mem_filter.2 ⟨hp, le_rfl⟩))
    exact (Nat.Prime.factorization_pos_of_dvd hpp hd (Nat.dvd_of_mem_primeFactors hp)).ne'
  exact lt_of_lt_of_le hpp.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero (tailPart_ne_zero d p)) hdvd)

theorem minFac_tailPart {d p : ℕ} (hd : d ≠ 0) (hp : p ∈ d.primeFactors) :
    (tailPart d p).minFac = p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have h1 : 1 < tailPart d p := one_lt_tailPart hd hp
  have hpdvd : p ∣ tailPart d p := by
    refine dvd_trans (dvd_pow_self p ?_) (Finset.dvd_prod_of_mem _
      (Finset.mem_filter.2 ⟨hp, le_rfl⟩))
    exact (Nat.Prime.factorization_pos_of_dvd hpp hd (Nat.dvd_of_mem_primeFactors hp)).ne'
  refine le_antisymm (Nat.minFac_le_of_dvd hpp.two_le hpdvd) ?_
  -- every prime factor of the tail is `≥ p`
  have hmf : (tailPart d p).minFac.Prime := Nat.minFac_prime (by omega)
  have hmfdvd : (tailPart d p).minFac ∣ tailPart d p := Nat.minFac_dvd _
  by_contra hcon
  push_neg at hcon
  have hq : (tailPart d p).minFac.factorization ((tailPart d p).minFac) = 1 := by
    simp [Nat.Prime.factorization_self hmf]
  have hpos : 0 < (tailPart d p).factorization ((tailPart d p).minFac) :=
    (Nat.Prime.factorization_pos_of_dvd hmf (tailPart_ne_zero d p) hmfdvd)
  rw [factorization_tailPart] at hpos
  by_cases h : (tailPart d p).minFac ∈ d.primeFactors ∧ p ≤ (tailPart d p).minFac
  · omega
  · rw [if_neg h] at hpos; omega

/-- **Structure theorem for `Fgap`.**  The maximum is attained on the tails: `Fgap d` is the
maximum over the primes `p | d` of `p` times the part of `d` supported on primes `≥ p`. -/
theorem Fgap_eq_sup_tail {d : ℕ} (hd : d ≠ 0) (hd1 : 1 < d) :
    Fgap d = d.primeFactors.sup fun p => tailPart d p * p := by
  refine le_antisymm ?_ ?_
  · refine max_le ?_ (Finset.sup_le fun v hv => ?_)
    · obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (n := d) (by omega)
      have hmem : p ∈ d.primeFactors := Nat.mem_primeFactors.2 ⟨hp.1, hp.2, hd⟩
      refine le_trans ?_ (Finset.le_sup (f := fun p => tailPart d p * p) hmem)
      have := one_lt_tailPart hd hmem
      nlinarith [hp.1.two_le]
    · rw [Finset.mem_filter, Nat.mem_divisors] at hv
      obtain ⟨⟨hvd, -⟩, hv1⟩ := hv
      have hv0 : v ≠ 0 := by rintro rfl; omega
      set p := v.minFac with hpdef
      have hpp : p.Prime := Nat.minFac_prime (by omega)
      have hpmem : p ∈ d.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hpp, (Nat.minFac_dvd v).trans hvd, hd⟩
      have hvt : v ∣ tailPart d p :=
        dvd_tailPart hd hvd hv0 fun q hq hqv => Nat.minFac_le_of_dvd hq.two_le hqv
      refine le_trans (Nat.mul_le_mul_right p
        (Nat.le_of_dvd (Nat.pos_of_ne_zero (tailPart_ne_zero d p)) hvt)) ?_
      exact Finset.le_sup (f := fun p => tailPart d p * p) hpmem
  · refine Finset.sup_le fun p hp => ?_
    have := le_Fgap hd (tailPart_dvd hd) (one_lt_tailPart hd hp)
    rwa [minFac_tailPart hd hp] at this

/-- **Prime-factor formula (squarefree case).**  For squarefree `d`, the `p`-tail is the product
of the prime factors `≥ p`, so `Fgap d = max_{p | d} p · ∏_{q | d, q ≥ p} q`. -/
theorem Fgap_squarefree {d : ℕ} (hsq : Squarefree d) (hd1 : 1 < d) :
    Fgap d = d.primeFactors.sup fun p => (∏ q ∈ d.primeFactors with p ≤ q, q) * p := by
  have hd : d ≠ 0 := hsq.ne_zero
  rw [Fgap_eq_sup_tail hd hd1]
  refine congrArg _ (funext fun p => ?_)
  congr 1
  refine Finset.prod_congr rfl fun q hq => ?_
  have hqmem : q ∈ d.primeFactors := (Finset.mem_filter.1 hq).1
  have : d.factorization q = 1 := by
    have h1 : d.factorization q ≤ 1 := (Nat.squarefree_iff_factorization_le_one hd).1 hsq q
    have h2 : 0 < d.factorization q := Nat.Prime.factorization_pos_of_dvd
      (Nat.prime_of_mem_primeFactors hqmem) hd (Nat.dvd_of_mem_primeFactors hqmem)
    omega
  rw [this, pow_one]

end Gate1B.R11.Frontier
