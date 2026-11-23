import RequestProject.REAL1B_20261122.FMClosing

/-! Gold 4.66. Complete the Möbius sum before regrouping prime owners. -/
namespace REAL1B.FM.Owners
open ArithmeticFunction Vaughan Closing
noncomputable section
open Classical

theorem total_mu (r : ℕ) : ∑ m ∈ r.divisors, mu m = if r = 1 then 1 else 0 := by
  calc
    _ = (mob * zetaR) r := (coe_mul_zeta_apply (f := mob) (x := r)).symm
    _ = _ := by rw [show mob * zetaR = 1 from coe_moebius_mul_coe_zeta, one_apply]

def truncated (E : ℝ) (r : ℕ) := ∑ m ∈ r.divisors, if (m:ℝ) ≤ E then mu m else 0

theorem divisor_complement (r : ℕ) (E : ℝ) :
    (∑ m ∈ r.divisors, if E < (m:ℝ) then mu m else 0) =
      (if r = 1 then 1 else 0) - truncated E r := by
  rw [eq_sub_iff_add_eq, ← total_mu, truncated, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by
    by_cases h : E < (m:ℝ) <;> simp [h, le_of_not_gt, not_le.mpr])

def edge (u d : ℝ) (l : ℕ) := max u (d/l)
def boundary (u : ℝ) (k : ℕ) : ℝ := if k.Prime ∧ u < (k:ℝ) then Real.log k else 0
def debt (u d : ℝ) (k : ℕ) := ∑ l ∈ k.primeFactors,
  if u < (l:ℝ) then Real.log l * truncated (edge u d l) (k/l) else 0

theorem owner_row {u d : ℝ} {k l : ℕ} (hl : l.Prime) :
    primeRow u d k l = Real.log l *
      ((if k/l = 1 then 1 else 0) - truncated (edge u d l) (k/l)) := by
  rw [← divisor_complement]
  unfold primeRow
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have hpos : (0:ℝ) < l := by exact_mod_cast hl.pos
  simp [edge, div_lt_iff₀ hpos, Nat.cast_mul]

private theorem coeff_over_factors (u d : ℝ) (k : ℕ) :
    coeff u d k = ∑ l ∈ k.primeFactors, if u < (l:ℝ) then primeRow u d k l else 0 := by
  have hf : k.divisors.filter Nat.Prime = k.primeFactors := by
    ext l
    simp [Nat.mem_divisors, and_comm, and_left_comm]
  rw [← hf, Finset.sum_filter]
  unfold coeff
  exact Finset.sum_congr rfl (fun l _ => by by_cases h : l.Prime <;> simp [h])

/-- The all-owner boundary occurs exactly at a genuine prime input. Strict
cutoffs are dual to the weak cutoff in each omitted truncated. -/
theorem coeff_complement (u d : ℝ) (k : ℕ) : coeff u d k = boundary u k - debt u d k := by
  have rowBoundary : (∑ l ∈ k.primeFactors, if l = k then boundary u k else 0) =
      boundary u k := by
    by_cases h : k.Prime
    · simp [h.mem_primeFactors (dvd_refl k) h.ne_zero]
    · simp [boundary, h]
  rw [eq_sub_iff_add_eq, coeff_over_factors, debt, ← Finset.sum_add_distrib, ← rowBoundary]
  apply Finset.sum_congr rfl
  intro l hl
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hl
  have he : k/l = 1 ↔ l = k := by
    constructor
    · intro h
      simpa [h] using Nat.div_mul_cancel hd
    · rintro rfl
      exact Nat.div_self hp.pos
  rw [owner_row hp]
  by_cases hk : l = k
  · subst k
    by_cases h : u < (l:ℝ) <;> simp [he, h, boundary, hp]
    ring
  · by_cases h : u < (l:ℝ) <;> simp [he, h, hk]

/-- Large extra factors cannot occur in a divisor at or below E. -/
private theorem truncated_large_factor {N r : ℕ} {E : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hlarge : ∀ p ∈ N.primeFactors, E < (p:ℝ)) :
    truncated E (N*r) = truncated E r := by
  have hsets : (N*r).divisors.filter (fun m : ℕ => (m:ℝ) ≤ E) =
      r.divisors.filter (fun m : ℕ => (m:ℝ) ≤ E) := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,_⟩, hcut⟩
      have hm := Nat.pos_of_dvd_of_pos hd (Nat.mul_pos hN hr)
      have hc : m.Coprime N := by
        by_contra hn
        obtain ⟨p,hp,hm',hN'⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
        have hpm : (p:ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd hm hm'
        exact (not_lt_of_ge (hpm.trans hcut)) (hlarge p (hp.mem_primeFactors hN' hN.ne'))
      exact ⟨⟨hc.dvd_of_dvd_mul_left hd, hr.ne'⟩, hcut⟩
    · rintro ⟨⟨hd,_⟩, hcut⟩
      exact ⟨⟨dvd_mul_of_dvd_right hd N, (Nat.mul_pos hN hr).ne'⟩, hcut⟩
  simpa only [truncated, ← Finset.sum_filter] using congrArg
    (fun s : Finset ℕ => ∑ m ∈ s, mu m) hsets

/-- Gold 4.66 Part V (2.2). M has at least one owner; M=P gives (2.1).
The quotient r need not be squarefree for this finite identity. -/
theorem large_owners {M r : ℕ} {u d : ℝ} (hu : 0 < u)
    (hM : 1 < M) (hr : 1 < r) (hs : Squarefree M) (hc : M.Coprime r)
    (hlarge : ∀ p ∈ M.primeFactors, max u (d/u) < (p:ℝ)) :
    coeff u d (M*r) = -Real.log M * truncated u r + coeff u d r - boundary u r := by
  have hMp : 0 < M := by omega
  have hrp : 0 < r := by omega
  have cuts (p : ℕ) (hp : p ∈ M.primeFactors) :
      u < (p:ℝ) ∧ d < (p:ℝ)*u := by
    obtain ⟨h₁,h₂⟩ := max_lt_iff.mp (hlarge p hp)
    exact ⟨h₁, (div_lt_iff₀ hu).mp h₂⟩
  let cost (k l : ℕ) : ℝ := if u < (l:ℝ) then Real.log l * truncated (edge u d l) (k/l) else 0
  have owner (l : ℕ) (hl : l ∈ M.primeFactors) :
      cost (M*r) l = Real.log l * truncated u r := by
    obtain ⟨hlp,hld,_⟩ := Nat.mem_primeFactors.mp hl
    obtain ⟨hlu,hldu⟩ := cuts l hl
    have hpos : (0:ℝ) < l := hu.trans hlu
    have he : edge u d l = u := max_eq_left ((div_le_iff₀ hpos).mpr (by linarith))
    have hq : (M*r)/l = (M/l)*r := by rw [Nat.mul_comm M r, Nat.mul_div_assoc _ hld, Nat.mul_comm]
    have hdiv : M/l ∣ M := Nat.div_dvd_of_dvd hld
    have hqpos := Nat.div_pos (Nat.le_of_dvd hMp hld) hlp.pos
    simp only [cost, if_pos hlu, he, hq]
    rw [truncated_large_factor hqpos hrp (fun p hp =>
      (cuts p (Nat.primeFactors_mono hdiv hMp.ne' hp)).1)]
  have cofactor (l : ℕ) (hl : l ∈ r.primeFactors) : cost (M*r) l = cost r l := by
    obtain ⟨hlp,hld,_⟩ := Nat.mem_primeFactors.mp hl
    by_cases h : u < (l:ℝ)
    · simp only [cost, if_pos h, Nat.mul_div_assoc M hld]
      congr 1
      apply truncated_large_factor hMp (Nat.div_pos (Nat.le_of_dvd hrp hld) hlp.pos)
      intro p hp
      obtain ⟨hpu,hpd⟩ := cuts p hp
      exact max_lt_iff.mpr ⟨hpu, (div_lt_iff₀ (hu.trans h)).mpr
        (hpd.trans (mul_lt_mul_of_pos_left h (hu.trans hpu)))⟩
    · simp [cost, h]
  have hlog : ∑ p ∈ M.primeFactors, Real.log p = Real.log M := by
    rw [← Real.log_prod (s := M.primeFactors) (f := fun p : ℕ => (p:ℝ)) (fun p hp => (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero :
      (p : ℝ) ≠ 0)), ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hs]
  have debt_eq : debt u d (M*r) = Real.log M * truncated u r + debt u d r := by
    change ∑ l ∈ (M*r).primeFactors, cost (M*r) l = _ + ∑ l ∈ r.primeFactors, cost r l
    rw [hc.primeFactors_mul, Finset.sum_union hc.disjoint_primeFactors,
      Finset.sum_congr rfl owner, Finset.sum_congr rfl cofactor, ← Finset.sum_mul, hlog]
  have hb : boundary u (M*r) = 0 := by simp [boundary, Nat.not_prime_mul hM.ne' hr.ne']
  rw [coeff_complement u d (M*r), hb, debt_eq, coeff_complement u d r]
  ring

end
end REAL1B.FM.Owners

#print axioms REAL1B.FM.Owners.total_mu
#print axioms REAL1B.FM.Owners.divisor_complement
#print axioms REAL1B.FM.Owners.owner_row
#print axioms REAL1B.FM.Owners.coeff_complement
#print axioms REAL1B.FM.Owners.large_owners
