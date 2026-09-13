/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the finite Ramanujan
expansion  (T3)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

Exact rational layer.  With the truncated coefficient `λ` of `TruncatedMobius` and the finite
Ramanujan sum `c_q` of `RamanujanFinite`, this module proves the **exact finite expansion**

```
F(N) = ∑_{d ∣ N} λ(d) = ∑_{0 < q ≤ Q_max} a(q) c_q(N),      Q_max = B₁B₂,
a(q) = ∑_{u ∈ I₁, v ∈ I₂, u,v odd, q ∣ uv} μ(u)μ(v) / (uv).
```

No asymptotics are used or claimed: every statement is a finite rational identity.  Two support
facts are proved as well: `a(q) = 0` for even `q`, and `a(q) = 0` whenever `p³ ∣ q` for a prime
`p` (cube-freeness of the surviving Ramanujan moduli).

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TruncatedMobius
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.RamanujanFinite

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset ArithmeticFunction

/-! ## 1. The rational coefficient `a(q)` and its divisor form -/

/-- **The Ramanujan coefficient**
`a(q) = ∑_{u ∈ I₁, v ∈ I₂, u,v odd, q ∣ uv} μ(u)μ(v)/(uv)`, in the exact rational layer. -/
def aCoeff (I : Cutoffs) (q : ℕ) : ℚ :=
  ∑ p ∈ I.box,
    if Odd p.1 ∧ Odd p.2 ∧ q ∣ p.1 * p.2 then
      ((moebius p.1 * moebius p.2 : ℤ) : ℚ) / ((p.1 : ℚ) * (p.2 : ℚ)) else 0

/-- The divisor form of the same coefficient: `a(q) = ∑_{q ∣ d ≤ Q_max} λ(d)/d`. -/
def aDiv (I : Cutoffs) (q : ℕ) : ℚ :=
  ∑ d ∈ Finset.Ioc 0 I.Qmax, if q ∣ d then ((lam I d : ℤ) : ℚ) / (d : ℚ) else 0

/-- The cast of `λ` into the rational layer, termwise. -/
theorem lam_cast (I : Cutoffs) (d : ℕ) :
    ((lam I d : ℤ) : ℚ) =
      ∑ p ∈ I.box, if Odd p.1 ∧ Odd p.2 ∧ p.1 * p.2 = d then
        ((moebius p.1 * moebius p.2 : ℤ) : ℚ) else 0 := by
  rw [lam, Int.cast_sum]
  exact Finset.sum_congr rfl fun p _ => by split <;> simp

/-- **The two forms of `a(q)` agree** — grouping the box by the product `d = uv`. -/
theorem aCoeff_eq_aDiv (I : Cutoffs) (q : ℕ) : aCoeff I q = aDiv I q := by
  have step : ∀ p ∈ I.box,
      (if Odd p.1 ∧ Odd p.2 ∧ q ∣ p.1 * p.2 then
        ((moebius p.1 * moebius p.2 : ℤ) : ℚ) / ((p.1 : ℚ) * (p.2 : ℚ)) else 0)
      = ∑ d ∈ Finset.Ioc 0 I.Qmax,
          (if q ∣ d then
            (if Odd p.1 ∧ Odd p.2 ∧ p.1 * p.2 = d then
              ((moebius p.1 * moebius p.2 : ℤ) : ℚ) else 0) / (d : ℚ) else 0) := by
    intro p hp
    have hmem : p.1 * p.2 ∈ Finset.Ioc 0 I.Qmax := by
      have h1 := I.box_pos hp
      have h2 := I.box_prod_le hp
      exact Finset.mem_Ioc.2 ⟨Nat.mul_pos h1.1 h1.2, h2⟩
    rw [Finset.sum_eq_single (p.1 * p.2)]
    · by_cases hq : q ∣ p.1 * p.2
      · by_cases ho : Odd p.1 ∧ Odd p.2
        · simp [hq, ho.1, ho.2, Nat.cast_mul]
        · simp only [hq, if_true]
          rw [if_neg (by tauto), if_neg (by tauto)]
          simp
      · rw [if_neg (by tauto), if_neg hq]
    · intro d _ hne
      by_cases hq : q ∣ d
      · rw [if_pos hq, if_neg (by tauto)]
        simp
      · rw [if_neg hq]
    · intro hnot; exact absurd hmem hnot
  rw [aCoeff, Finset.sum_congr rfl step, Finset.sum_comm, aDiv]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hq : q ∣ d
  · simp only [hq, if_true]
    rw [lam_cast, Finset.sum_div]
  · simp [hq]

/-! ## 2. The finite Ramanujan expansion -/

/-- `F(N) = ∑_{d ∣ N} λ(d)`, in the exact rational layer. -/
def Fsum (I : Cutoffs) (N : ℕ) : ℚ := ∑ d ∈ N.divisors, ((lam I d : ℤ) : ℚ)

/-- For `0 < d ≤ Q_max`, the divisors of `d` are exactly the elements of `(0, Q_max]` dividing
`d`. -/
theorem filter_dvd_eq_divisors {I : Cutoffs} {d : ℕ} (hd : d ∈ Finset.Ioc 0 I.Qmax) :
    (Finset.Ioc 0 I.Qmax).filter (· ∣ d) = d.divisors := by
  rw [Finset.mem_Ioc] at hd
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
  constructor
  · rintro ⟨-, hqd⟩; exact ⟨hqd, by omega⟩
  · rintro ⟨hqd, -⟩
    have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; omega)
    exact ⟨⟨hq0, le_trans (Nat.le_of_dvd (by omega) hqd) hd.2⟩, hqd⟩

/-- **The finite Ramanujan expansion** (exact, no asymptotics):

`F(N) = ∑_{0 < q ≤ Q_max} a(q) c_q(N)`, with `Q_max = B₁B₂` the sharp cutoff product. -/
theorem Fsum_eq_ramanujan_expansion (I : Cutoffs) {N : ℕ} (hN : 0 < N) :
    Fsum I N = ∑ q ∈ Finset.Ioc 0 I.Qmax, aCoeff I q * ((ram q N : ℤ) : ℚ) := by
  have h1 : ∑ q ∈ Finset.Ioc 0 I.Qmax, aCoeff I q * ((ram q N : ℤ) : ℚ)
      = ∑ q ∈ Finset.Ioc 0 I.Qmax, ∑ d ∈ Finset.Ioc 0 I.Qmax,
          (if q ∣ d then ((lam I d : ℤ) : ℚ) / (d : ℚ) * ((ram q N : ℤ) : ℚ) else 0) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [aCoeff_eq_aDiv, aDiv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by split <;> simp
  rw [h1, Finset.sum_comm]
  have h2 : ∀ d ∈ Finset.Ioc 0 I.Qmax,
      (∑ q ∈ Finset.Ioc 0 I.Qmax,
        (if q ∣ d then ((lam I d : ℤ) : ℚ) / (d : ℚ) * ((ram q N : ℤ) : ℚ) else 0))
      = if d ∣ N then ((lam I d : ℤ) : ℚ) else 0 := by
    intro d hd
    have hd' := Finset.mem_Ioc.1 hd
    rw [← Finset.sum_filter, filter_dvd_eq_divisors hd, ← Finset.mul_sum]
    have : ∑ q ∈ d.divisors, ((ram q N : ℤ) : ℚ)
        = ((if d ∣ N then (d : ℤ) else 0 : ℤ) : ℚ) := by
      rw [← Int.cast_sum, sum_ram_divisors N hd'.1]
    rw [this]
    have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    by_cases hdN : d ∣ N
    · simp only [hdN, if_true, Int.cast_natCast]
      field_simp
    · simp [hdN]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter, Fsum]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors] at hd ⊢
    exact ⟨hd.2, hN.ne'⟩
  · intro d hd hnot
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors] at hd hnot
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.2 hd)
    have : I.Qmax < d := by
      by_contra hle
      exact hnot ⟨⟨hd0, by omega⟩, hd.1⟩
    rw [lam_eq_zero_of_Qmax_lt I this]
    simp

/-! ## 3. Support of the coefficient -/

/-- Even moduli carry no Ramanujan coefficient: the two oddness cutoffs are load-bearing. -/
theorem aCoeff_eq_zero_of_even (I : Cutoffs) {q : ℕ} (hq : Even q) : aCoeff I q = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [if_neg]
  rintro ⟨h1, h2, h3⟩
  have hodd : Odd (p.1 * p.2) := h1.mul h2
  have : (2 : ℕ) ∣ p.1 * p.2 := dvd_trans hq.two_dvd h3
  rw [Nat.odd_iff] at hodd
  omega

/-- Cube-full moduli carry no Ramanujan coefficient: if `p³ ∣ q` then `a(q) = 0`.  (Only
squarefree `u, v` survive `μ`, so `p³` cannot divide `uv`.) -/
theorem aCoeff_eq_zero_of_cube_dvd (I : Cutoffs) {q p : ℕ} (hp : p.Prime) (hpq : p ^ 3 ∣ q) :
    aCoeff I q = 0 := by
  refine Finset.sum_eq_zero fun x hx => ?_
  have hpos := I.box_pos hx
  by_cases hu : Squarefree x.1
  · by_cases hv : Squarefree x.2
    · rw [if_neg]
      rintro ⟨-, -, hdvd⟩
      have huv : x.1 * x.2 ≠ 0 := Nat.mul_ne_zero hpos.1.ne' hpos.2.ne'
      have h3 : 3 ≤ (x.1 * x.2).factorization p :=
        (hp.pow_dvd_iff_le_factorization huv).1 (dvd_trans hpq hdvd)
      rw [Nat.factorization_mul hpos.1.ne' hpos.2.ne'] at h3
      simp only [Finsupp.add_apply] at h3
      have h4 := (Nat.squarefree_iff_factorization_le_one hpos.1.ne').1 hu p
      have h5 := (Nat.squarefree_iff_factorization_le_one hpos.2.ne').1 hv p
      omega
    · have : moebius x.2 = 0 := moebius_eq_zero_of_not_squarefree hv
      split <;> simp [this]
  · have : moebius x.1 = 0 := moebius_eq_zero_of_not_squarefree hu
    split <;> simp [this]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
