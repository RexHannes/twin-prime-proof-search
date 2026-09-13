/-
# Gate1B / R11 / Frontier : the minimal bad-gap kernel

Append-only module of the minimal-gap-kernel delta.  Everything here is finite arithmetic.

```
K_x = { v : v squarefree, Fgap(v) > x, and Fgap(t) ≤ x for every proper divisor t | v }.
```

Kernel-proved here:

* the maximum of `Fgap` on a kernel is attained at the top: `x < v · P⁻(v)`;
* `Fgap(v / P⁻(v)) ≤ x`;
* **existence**: every squarefree `d` with `Fgap(d) > x` is divisible by a minimal kernel;
* **uniqueness** (high priority): distinct kernels have `lcm > x`; hence at most one kernel
  divides any `M ≤ x`;
* the **bad-divisor classification** `d bad ↔ v | d`, i.e. the bad squarefree divisors of
  `M = v·m` are exactly the `v·e` with `e | m` squarefree, together with `m < P⁻(v)` and
  `gcd(m,v) = 1`;
* the **kernel-rank cofactor range** `P⁻(v)^r ≤ v`, `x^r < v^{r+1}` and `m^{r+1} < x`.
-/
import Gate1B.R11.Frontier.SchinzelSzekeresKernel

namespace Gate1B.R11.Frontier

open Finset

/-- The minimal bad-gap kernels at level `x`. -/
def IsMinKernel (x v : ℕ) : Prop :=
  Squarefree v ∧ x < Fgap v ∧ ∀ t, t ∣ v → t ≠ v → Fgap t ≤ x

theorem IsMinKernel.squarefree {x v : ℕ} (h : IsMinKernel x v) : Squarefree v := h.1

theorem IsMinKernel.ne_zero {x v : ℕ} (h : IsMinKernel x v) : v ≠ 0 := h.1.ne_zero

theorem IsMinKernel.ne_one {x v : ℕ} (hx : 1 ≤ x) (h : IsMinKernel x v) : v ≠ 1 := by
  rintro rfl
  have hb := h.2.1
  rw [Fgap_one] at hb
  omega

theorem IsMinKernel.one_lt {x v : ℕ} (hx : 1 ≤ x) (h : IsMinKernel x v) : 1 < v :=
  lt_of_le_of_ne (Nat.one_le_iff_ne_zero.2 h.ne_zero) (Ne.symm (h.ne_one hx))

/-! ## 1. The maximum is attained at the top -/

/-- On a minimal kernel the Schinzel–Szekeres maximum is attained at `v` itself: `x < v·P⁻(v)`. -/
theorem IsMinKernel.lt_mul_minFac {x v : ℕ} (hx : 1 ≤ x) (h : IsMinKernel x v) :
    x < v * v.minFac := by
  by_contra hcon
  push_neg at hcon
  have hle : Fgap v ≤ x := by
    refine (Fgap_le_iff h.ne_zero hx).2 fun w hw hw1 => ?_
    by_cases hwv : w = v
    · subst hwv; exact hcon
    · have hw0 : w ≠ 0 := by rintro rfl; omega
      exact le_trans (le_Fgap hw0 dvd_rfl hw1) (h.2.2 w hw hwv)
  have := h.2.1
  omega

/-- Removing the least prime of a kernel lands in the dense range. -/
theorem IsMinKernel.Fgap_div_minFac_le {x v : ℕ} (hx : 1 ≤ x) (h : IsMinKernel x v) :
    Fgap (v / v.minFac) ≤ x := by
  have h1 : 1 < v := h.one_lt hx
  have hp : v.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : v / v.minFac ∣ v := Nat.div_dvd_of_dvd (Nat.minFac_dvd v)
  refine h.2.2 _ hdvd ?_
  intro hEq
  have hv0 : 0 < v := by omega
  have : v.minFac * (v / v.minFac) = v := Nat.mul_div_cancel' (Nat.minFac_dvd v)
  rw [hEq] at this
  nlinarith [hp.two_le]

/-! ## 2. Existence of a kernel below every bad divisor -/

/-- Every `d` with `Fgap d > x` has a divisor which is a minimal bad-gap kernel. -/
theorem exists_minKernel_dvd (x : ℕ) :
    ∀ d : ℕ, d ≠ 0 → Squarefree d → x < Fgap d → ∃ v, v ∣ d ∧ IsMinKernel x v := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hsq hbad
    by_cases hmin : ∀ t, t ∣ d → t ≠ d → Fgap t ≤ x
    · exact ⟨d, dvd_rfl, ⟨hsq, hbad, hmin⟩⟩
    · push_neg at hmin
      obtain ⟨t, htd, htne, hbt⟩ := hmin
      have ht0 : t ≠ 0 := by rintro rfl; exact hd (Nat.eq_zero_of_zero_dvd htd)
      have htlt : t < d := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) htd) htne
      obtain ⟨v, hvt, hv⟩ := ih t htlt ht0 (hsq.squarefree_of_dvd htd) (by omega)
      exact ⟨v, hvt.trans htd, hv⟩

/-! ## 3. Uniqueness -/

/-- A squarefree number all of whose primes divide `w` divides `w`. -/
theorem dvd_of_squarefree_primes {v w : ℕ} (hv : Squarefree v) (hw : w ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ v → q ∣ w) : v ∣ w := by
  have : v ∣ radNat w := by
    calc v = ∏ p ∈ v.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hv).symm
      _ ∣ ∏ p ∈ w.primeFactors, p := by
          refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
          exact Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp,
            h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), hw⟩
      _ = radNat w := rfl
  exact this.trans (radNat_dvd w)

/-- **Uniqueness of the minimal kernel.**  Two distinct minimal bad-gap kernels have
`lcm(v,w) > x`. -/
theorem lcm_gt_of_minKernel {x v w : ℕ} (hx : 1 ≤ x) (hv : IsMinKernel x v)
    (hw : IsMinKernel x w) (hne : v ≠ w) : x < Nat.lcm v w := by
  by_contra hcon
  push_neg at hcon
  set L := Nat.lcm v w with hL
  have hv0 : v ≠ 0 := hv.ne_zero
  have hw0 : w ≠ 0 := hw.ne_zero
  have hL0 : L ≠ 0 := Nat.lcm_ne_zero hv0 hw0
  have hvL : v ∣ L := Nat.dvd_lcm_left v w
  have hwL : w ∣ L := Nat.dvd_lcm_right v w
  -- `v ∤ w` and `w ∤ v`, else one is a proper divisor of the other
  have hvbad := hv.2.1
  have hwbad := hw.2.1
  have hvw : ¬ v ∣ w := by
    intro hdvd
    have := hw.2.2 v hdvd hne
    omega
  have hwv : ¬ w ∣ v := by
    intro hdvd
    have := hv.2.2 w hdvd (Ne.symm hne)
    omega
  -- the two cofactors
  obtain ⟨k, hk⟩ := id hvL
  obtain ⟨k', hk'⟩ := id hwL
  have hkpos : 0 < k := Nat.pos_of_ne_zero (by
    rintro rfl
    exact hL0 (by rw [hk, mul_zero]))
  have hk'pos : 0 < k' := Nat.pos_of_ne_zero (by
    rintro rfl
    exact hL0 (by rw [hk', mul_zero]))
  -- `k < P⁻(v)` and `k' < P⁻(w)`
  have hklt : k < v.minFac := by
    have h1 : x < v * v.minFac := hv.lt_mul_minFac hx
    have h2 : v * k ≤ x := by rw [← hk]; exact hcon
    have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
    by_contra hcon2
    push_neg at hcon2
    nlinarith
  have hk'lt : k' < w.minFac := by
    have h1 : x < w * w.minFac := hw.lt_mul_minFac hx
    have h2 : w * k' ≤ x := by rw [← hk']; exact hcon
    have hwpos : 0 < w := Nat.pos_of_ne_zero hw0
    by_contra hcon2
    push_neg at hcon2
    nlinarith
  -- a prime of `v` not dividing `w` divides `k'`
  have hq : ∃ q : ℕ, q.Prime ∧ q ∣ v ∧ ¬ q ∣ w := by
    by_contra hcon2
    push_neg at hcon2
    exact hvw (dvd_of_squarefree_primes hv.squarefree hw0 fun q hq hqv => hcon2 q hq hqv)
  obtain ⟨q, hqp, hqv, hqw⟩ := hq
  have hqk' : q ∣ k' := by
    have : q ∣ w * k' := by rw [← hk']; exact hqv.trans hvL
    exact (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqw) this)
  have hq_le : v.minFac ≤ k' :=
    le_trans (Nat.minFac_le_of_dvd hqp.two_le hqv) (Nat.le_of_dvd hk'pos hqk')
  -- symmetrically
  have hr : ∃ r : ℕ, r.Prime ∧ r ∣ w ∧ ¬ r ∣ v := by
    by_contra hcon2
    push_neg at hcon2
    exact hwv (dvd_of_squarefree_primes hw.squarefree hv0 fun r hr hrw => hcon2 r hr hrw)
  obtain ⟨r, hrp, hrw, hrv⟩ := hr
  have hrk : r ∣ k := by
    have : r ∣ v * k := by rw [← hk]; exact hrw.trans hwL
    exact (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hrp).2 hrv) this)
  have hr_le : w.minFac ≤ k :=
    le_trans (Nat.minFac_le_of_dvd hrp.two_le hrw) (Nat.le_of_dvd hkpos hrk)
  omega

/-- **At most one minimal kernel divides any `M ≤ x`.** -/
theorem minKernel_unique_of_dvd {x M v w : ℕ} (hx : 1 ≤ x) (hM : M ≠ 0) (hMx : M ≤ x)
    (hv : IsMinKernel x v) (hw : IsMinKernel x w) (hvM : v ∣ M) (hwM : w ∣ M) : v = w := by
  by_contra hne
  have h1 : x < Nat.lcm v w := lcm_gt_of_minKernel hx hv hw hne
  have h2 : Nat.lcm v w ∣ M := Nat.lcm_dvd hvM hwM
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h2
  omega

/-! ## 4. Bad-divisor classification -/

section Classification

variable {x M v m : ℕ}

/-- The cofactor of the kernel is smaller than the least prime of the kernel. -/
theorem cofactor_lt_minFac (hx : 1 ≤ x) (hv : IsMinKernel x v) (hM : v * m ≤ x) :
    m < v.minFac := by
  have h1 : x < v * v.minFac := hv.lt_mul_minFac hx
  have hvpos : 0 < v := Nat.pos_of_ne_zero hv.ne_zero
  by_contra hcon
  push_neg at hcon
  nlinarith

/-- The cofactor is coprime to the kernel. -/
theorem coprime_cofactor (hx : 1 ≤ x) (hv : IsMinKernel x v) (hM : v * m ≤ x) (hm : m ≠ 0) :
    Nat.Coprime m v := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hne
  have hqm : q ∣ m := hqdvd.trans (Nat.gcd_dvd_left _ _)
  have hqv : q ∣ v := hqdvd.trans (Nat.gcd_dvd_right _ _)
  have h1 : q ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hqm
  have h2 : v.minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le hqv
  have h3 : m < v.minFac := cofactor_lt_minFac hx hv hM
  omega

/-- **Bad-divisor classification.**  If `v` is the (unique) minimal kernel dividing `M ≤ x`, then
a squarefree divisor `d | M` is bad exactly when `v | d`. -/
theorem bad_divisor_iff (hx : 1 ≤ x) (hM0 : M ≠ 0) (hMx : M ≤ x) (hv : IsMinKernel x v)
    (hvM : v ∣ M) {d : ℕ} (hd : d ∣ M) (hdsq : Squarefree d) :
    x < Fgap d ↔ v ∣ d := by
  constructor
  · intro hbad
    obtain ⟨v', hv'd, hv'⟩ := exists_minKernel_dvd x d hdsq.ne_zero hdsq hbad
    have : v' = v := minKernel_unique_of_dvd hx hM0 hMx hv' hv (hv'd.trans hd) hvM
    exact this ▸ hv'd
  · intro hvd
    have hmono : Fgap v ≤ Fgap d := Fgap_mono hdsq.ne_zero hvd
    have := hv.2.1
    omega

/-- The bad squarefree divisors of `M = v·m` are exactly the `v·e` with `e | m` squarefree. -/
theorem bad_divisor_form (hx : 1 ≤ x) (hM0 : M ≠ 0) (hMx : M ≤ x) (hv : IsMinKernel x v)
    (hvm : v * m = M) {d : ℕ} (hd : d ∣ M) (hdsq : Squarefree d) :
    x < Fgap d ↔ ∃ e, e ∣ m ∧ d = v * e := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hvm; exact hM0 hvm.symm
  have hcop : Nat.Coprime m v :=
    coprime_cofactor hx hv (by rw [hvm]; exact hMx) hm0
  rw [bad_divisor_iff hx hM0 hMx hv ⟨m, hvm.symm⟩ hd hdsq]
  constructor
  · intro hvd
    obtain ⟨e, he⟩ := hvd
    refine ⟨e, ?_, he⟩
    have : v * e ∣ v * m := by rw [he] at hd; rwa [hvm]
    exact (mul_dvd_mul_iff_left (a := v) (Nat.pos_of_ne_zero hv.ne_zero).ne').1 this
  · rintro ⟨e, -, rfl⟩
    exact Dvd.intro e rfl

end Classification

/-! ## 5. Kernel-rank cofactor range -/

/-- For squarefree `v`, the least prime raised to the number of prime factors is at most `v`. -/
theorem minFac_pow_card_le {v : ℕ} (hsq : Squarefree v) :
    v.minFac ^ v.primeFactors.card ≤ v := by
  have hv0 : v ≠ 0 := hsq.ne_zero
  calc v.minFac ^ v.primeFactors.card
      = ∏ _p ∈ v.primeFactors, v.minFac := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ v.primeFactors, p := by
        refine Finset.prod_le_prod' fun p hp => ?_
        exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
          (Nat.dvd_of_mem_primeFactors hp)
    _ = v := Nat.prod_primeFactors_of_squarefree hsq

/-- **Kernel-rank bound.**  With `r = ω(v)`, a kernel satisfies `x^r < v^{r+1}`. -/
theorem minKernel_pow_lt {x v : ℕ} (hx : 1 ≤ x) (h : IsMinKernel x v) :
    x ^ v.primeFactors.card < v ^ (v.primeFactors.card + 1) := by
  have h1 : x < v * v.minFac := h.lt_mul_minFac hx
  have hv1 : 1 < v := h.one_lt hx
  have hrpos : v.primeFactors.card ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨v.minFac, Nat.mem_primeFactors.2 ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd v,
      by omega⟩⟩
  set r := v.primeFactors.card with hr
  calc x ^ r < (v * v.minFac) ^ r := Nat.pow_lt_pow_left h1 hrpos
    _ = v ^ r * v.minFac ^ r := by rw [mul_pow]
    _ ≤ v ^ r * v := Nat.mul_le_mul_left _ (minFac_pow_card_le h.squarefree)
    _ = v ^ (r + 1) := by ring

/-- **Cofactor range.**  With `r = ω(v)` and `v·m ≤ x`, the cofactor satisfies `m^{r+1} < x`. -/
theorem cofactor_pow_lt {x v m : ℕ} (hx : 1 ≤ x) (h : IsMinKernel x v) (hm : 0 < m)
    (hM : v * m ≤ x) : m ^ (v.primeFactors.card + 1) < x := by
  set r := v.primeFactors.card with hr
  have key : m ^ (r + 1) * x ^ r < x * x ^ r := by
    calc m ^ (r + 1) * x ^ r < m ^ (r + 1) * v ^ (r + 1) :=
          Nat.mul_lt_mul_of_pos_left (minKernel_pow_lt hx h) (pow_pos hm _)
      _ = (v * m) ^ (r + 1) := by rw [mul_pow]; ring
      _ ≤ x ^ (r + 1) := Nat.pow_le_pow_left hM _
      _ = x * x ^ r := by ring
  exact lt_of_mul_lt_mul_right key (Nat.zero_le _)

/-- Rank two: `m³ < x`. -/
theorem cofactor_rank_two {x v m : ℕ} (hx : 1 ≤ x) (h : IsMinKernel x v) (hm : 0 < m)
    (hM : v * m ≤ x) (hrank : v.primeFactors.card = 2) : m ^ 3 < x := by
  have := cofactor_pow_lt hx h hm hM
  rwa [hrank] at this

/-- Rank three: `m⁴ < x`. -/
theorem cofactor_rank_three {x v m : ℕ} (hx : 1 ≤ x) (h : IsMinKernel x v) (hm : 0 < m)
    (hM : v * m ≤ x) (hrank : v.primeFactors.card = 3) : m ^ 4 < x := by
  have := cofactor_pow_lt hx h hm hM
  rwa [hrank] at this

end Gate1B.R11.Frontier
