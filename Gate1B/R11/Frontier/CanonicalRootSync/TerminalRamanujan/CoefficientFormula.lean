/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the exact coefficient
formula  (T8)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

The exact cofactor decomposition of the Ramanujan coefficient at an odd cube-free modulus
`q = a b²` (`a, b` squarefree, coprime, both odd):

```
a(q) = (μ(a)/q) ∑_{r s t = a} (1/t) H_{2D₁}(I₁/D₁) H_{2D₂}(I₂/D₂),
D₁ = b r t,   D₂ = b s t.
```

`t` is the designated inclusion–exclusion variable — *not* a gcd of the residual cofactors: the
residual harmonic sums are only required to be coprime to `2Dᵢ`, so `r` and `s` may still share
primes with the opposite variable.  This is exactly the shape proved here.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.PrimeAllocation

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset ArithmeticFunction

/-! ## 1. Elementary auxiliaries -/

/-- A divisor of an odd number is odd. -/
theorem odd_of_dvd_odd {m n : ℕ} (hmn : m ∣ n) (hn : Odd n) : Odd m := by
  rcases Nat.even_or_odd m with he | ho
  · exfalso
    have h2 : 2 ∣ n := dvd_trans he.two_dvd hmn
    rw [Nat.odd_iff] at hn
    omega
  · exact ho

/-! ## 2. The pointwise allocation expansion of a box term -/

/-- **Pointwise allocation expansion.**  For `u, v > 0` the truncated box term at modulus
`q = a b²` expands over the allocation triples `r s t = a`. -/
theorem term_alloc_expansion {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hab : Nat.Coprime a b) {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (if Odd u ∧ Odd v ∧ a * b ^ 2 ∣ u * v then
        ((moebius u * moebius v : ℤ) : ℚ) / ((u : ℚ) * (v : ℚ)) else 0)
      = ∑ x ∈ a.divisorsAntidiagonal, ∑ y ∈ x.1.divisorsAntidiagonal,
          ((moebius x.2 : ℤ) : ℚ)
            * (if Odd u ∧ D1 b y.1 x.2 ∣ u then ((moebius u : ℤ) : ℚ) / (u : ℚ) else 0)
            * (if Odd v ∧ D2 b y.2 x.2 ∣ v then ((moebius v : ℤ) : ℚ) / (v : ℚ) else 0) := by
  by_cases hou : Odd u
  · by_cases hov : Odd v
    · by_cases hsu : Squarefree u
      · by_cases hsv : Squarefree v
        · -- the genuine case
          have hstep : ∀ x ∈ a.divisorsAntidiagonal, ∀ y ∈ x.1.divisorsAntidiagonal,
              ((moebius x.2 : ℤ) : ℚ)
                  * (if Odd u ∧ D1 b y.1 x.2 ∣ u then ((moebius u : ℤ) : ℚ) / (u : ℚ) else 0)
                  * (if Odd v ∧ D2 b y.2 x.2 ∣ v then ((moebius v : ℤ) : ℚ) / (v : ℚ) else 0)
                = (((moebius x.2) * (if D1 b y.1 x.2 ∣ u then (1 : ℤ) else 0)
                    * (if D2 b y.2 x.2 ∣ v then (1 : ℤ) else 0) : ℤ) : ℚ)
                  * (((moebius u * moebius v : ℤ) : ℚ) / ((u : ℚ) * (v : ℚ))) := by
            intro x _ y _
            by_cases hD1 : D1 b y.1 x.2 ∣ u
            · by_cases hD2 : D2 b y.2 x.2 ∣ v
              · simp only [hou, hov, hD1, hD2, and_self, if_true, Int.cast_mul, mul_one]
                field_simp
              · simp [hD2]
            · simp [hD1]
          rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl (hstep x hx)]
          have hcast : ∀ x ∈ a.divisorsAntidiagonal,
              (∑ y ∈ x.1.divisorsAntidiagonal,
                (((moebius x.2) * (if D1 b y.1 x.2 ∣ u then (1 : ℤ) else 0)
                  * (if D2 b y.2 x.2 ∣ v then (1 : ℤ) else 0) : ℤ) : ℚ)
                * (((moebius u * moebius v : ℤ) : ℚ) / ((u : ℚ) * (v : ℚ))))
              = ((∑ y ∈ x.1.divisorsAntidiagonal,
                    (moebius x.2) * (if D1 b y.1 x.2 ∣ u then (1 : ℤ) else 0)
                      * (if D2 b y.2 x.2 ∣ v then (1 : ℤ) else 0) : ℤ) : ℚ)
                * (((moebius u * moebius v : ℤ) : ℚ) / ((u : ℚ) * (v : ℚ))) := by
            intro x _
            rw [← Finset.sum_mul, Int.cast_sum]
          rw [Finset.sum_congr rfl hcast, ← Finset.sum_mul, ← Int.cast_sum,
            alloc_indicator_with_b ha hb hab hsu hsv]
          by_cases hq : a * b ^ 2 ∣ u * v
          · rw [if_pos hq, if_pos ⟨hou, hov, hq⟩]
            simp
          · rw [if_neg hq, if_neg (by tauto)]
            simp
        · -- `v` not squarefree: both sides vanish
          have hmv : moebius v = 0 := moebius_eq_zero_of_not_squarefree hsv
          rw [show (if Odd u ∧ Odd v ∧ a * b ^ 2 ∣ u * v then
              ((moebius u * moebius v : ℤ) : ℚ) / ((u : ℚ) * (v : ℚ)) else 0) = 0 by
            split <;> simp [hmv]]
          refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
          split <;> simp [hmv]
      · -- `u` not squarefree: both sides vanish
        have hmu : moebius u = 0 := moebius_eq_zero_of_not_squarefree hsu
        rw [show (if Odd u ∧ Odd v ∧ a * b ^ 2 ∣ u * v then
            ((moebius u * moebius v : ℤ) : ℚ) / ((u : ℚ) * (v : ℚ)) else 0) = 0 by
          split <;> simp [hmu]]
        refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
        by_cases hD1 : Odd u ∧ D1 b y.1 x.2 ∣ u
        · rw [if_pos hD1]; simp [hmu]
        · rw [if_neg hD1]; simp
    · rw [if_neg (by tauto)]
      refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
      rw [if_neg (show ¬(Odd v ∧ D2 b y.2 x.2 ∣ v) by tauto)]
      simp
  · rw [if_neg (by tauto)]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
    rw [if_neg (by tauto)]
    simp

/-! ## 3. The exact coefficient formula -/

/-- **The exact cofactor decomposition of the Ramanujan coefficient.**  For an odd cube-free
modulus `q = a b²` with `a, b` squarefree, coprime and odd,

`a(q) = (μ(a)/q) ∑_{r s t = a} (1/t) H_{2D₁}(I₁/D₁) H_{2D₂}(I₂/D₂)`,

with `D₁ = b r t`, `D₂ = b s t`.  Both interval cutoffs remain explicit in every harmonic
factor. -/
theorem aCoeff_cofactor_allocation (I : Cutoffs) {a b : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hab : Nat.Coprime a b)
    (haodd : Odd a) (hbodd : Odd b) :
    aCoeff I (a * b ^ 2)
      = ((moebius a : ℤ) : ℚ) / ((a * b ^ 2 : ℕ) : ℚ) *
        ∑ x ∈ a.divisorsAntidiagonal, ∑ y ∈ x.1.divisorsAntidiagonal,
          (1 / (x.2 : ℚ)) *
            (harm I.a1 I.b1 (D1 b y.1 x.2) (2 * D1 b y.1 x.2) *
              harm I.a2 I.b2 (D2 b y.2 x.2) (2 * D2 b y.2 x.2)) := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  -- Step 1: expand every box term over the allocation triples.
  have h1 : aCoeff I (a * b ^ 2)
      = ∑ p ∈ I.box, ∑ x ∈ a.divisorsAntidiagonal, ∑ y ∈ x.1.divisorsAntidiagonal,
          ((moebius x.2 : ℤ) : ℚ)
            * (if Odd p.1 ∧ D1 b y.1 x.2 ∣ p.1 then ((moebius p.1 : ℤ) : ℚ) / (p.1 : ℚ) else 0)
            * (if Odd p.2 ∧ D2 b y.2 x.2 ∣ p.2 then
                ((moebius p.2 : ℤ) : ℚ) / (p.2 : ℚ) else 0) := by
    rw [aCoeff]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpos := I.box_pos hp
    exact term_alloc_expansion ha hb hab hpos.1 hpos.2
  -- Step 2: exchange the box sum with the allocation sums and factor the box.
  rw [h1, Finset.sum_comm]
  have h2 : ∀ x ∈ a.divisorsAntidiagonal,
      (∑ p ∈ I.box, ∑ y ∈ x.1.divisorsAntidiagonal,
        ((moebius x.2 : ℤ) : ℚ)
          * (if Odd p.1 ∧ D1 b y.1 x.2 ∣ p.1 then ((moebius p.1 : ℤ) : ℚ) / (p.1 : ℚ) else 0)
          * (if Odd p.2 ∧ D2 b y.2 x.2 ∣ p.2 then ((moebius p.2 : ℤ) : ℚ) / (p.2 : ℚ) else 0))
      = ∑ y ∈ x.1.divisorsAntidiagonal,
          (1 / (x.2 : ℚ)) *
            (harm I.a1 I.b1 (D1 b y.1 x.2) (2 * D1 b y.1 x.2) *
              harm I.a2 I.b2 (D2 b y.2 x.2) (2 * D2 b y.2 x.2))
            * (((moebius a : ℤ) : ℚ) / ((a * b ^ 2 : ℕ) : ℚ)) := by
    intro x hx
    obtain ⟨hxa, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨hyx, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
    -- names for the allocation variables
    set r := y.1 with hr
    set s := y.2 with hs
    set t := x.2 with ht
    have hrst : r * s * t = a := by rw [hr, hs, ht, hyx, hxa]
    have hsq : Squarefree (r * s * t) := by rw [hrst]; exact ha
    have hsq' : Squarefree (r * s) := (Nat.squarefree_mul_iff.1 hsq).2.1
    have hct : Nat.Coprime (r * s) t := (Nat.squarefree_mul_iff.1 hsq).1
    have hst : Squarefree t := (Nat.squarefree_mul_iff.1 hsq).2.2
    have hcrs : Nat.Coprime r s := (Nat.squarefree_mul_iff.1 hsq').1
    have hcrt : Nat.Coprime r t := Nat.Coprime.coprime_dvd_left (dvd_mul_right r s) hct
    have hcst : Nat.Coprime s t := Nat.Coprime.coprime_dvd_left (dvd_mul_left s r) hct
    have hdr : r ∣ a := ⟨s * t, by rw [← hrst]; ring⟩
    have hds : s ∣ a := ⟨r * t, by rw [← hrst]; ring⟩
    have hdt : t ∣ a := ⟨r * s, by rw [← hrst]; ring⟩
    have hcbr : Nat.Coprime b r := (Nat.Coprime.coprime_dvd_left hdr hab).symm
    have hcbs : Nat.Coprime b s := (Nat.Coprime.coprime_dvd_left hds hab).symm
    have hcbt : Nat.Coprime b t := (Nat.Coprime.coprime_dvd_left hdt hab).symm
    have hrodd : Odd r := odd_of_dvd_odd hdr haodd
    have hsodd : Odd s := odd_of_dvd_odd hds haodd
    have htodd : Odd t := odd_of_dvd_odd hdt haodd
    have hr0 : r ≠ 0 := by rintro h; rw [h, zero_mul, zero_mul] at hrst; exact ha0 hrst.symm
    have hs0 : s ≠ 0 := by rintro h; rw [h, mul_zero, zero_mul] at hrst; exact ha0 hrst.symm
    have ht0 : t ≠ 0 := by rintro h; rw [h, mul_zero] at hrst; exact ha0 hrst.symm
    have hD1odd : Odd (D1 b r t) := by
      unfold D1; exact (hbodd.mul hrodd).mul htodd
    have hD2odd : Odd (D2 b s t) := by
      unfold D2; exact (hbodd.mul hsodd).mul htodd
    have hD1pos : 0 < D1 b r t := by
      unfold D1; positivity
    have hD2pos : 0 < D2 b s t := by
      unfold D2; positivity
    -- factor the box sum into the two interval sums
    rw [Cutoffs.box, Finset.sum_product]
    have hfactor :
        (∑ u ∈ I.I1, ∑ v ∈ I.I2,
          ((moebius t : ℤ) : ℚ)
            * (if Odd u ∧ D1 b r t ∣ u then ((moebius u : ℤ) : ℚ) / (u : ℚ) else 0)
            * (if Odd v ∧ D2 b s t ∣ v then ((moebius v : ℤ) : ℚ) / (v : ℚ) else 0))
        = ((moebius t : ℤ) : ℚ)
            * (∑ u ∈ I.I1, if Odd u ∧ D1 b r t ∣ u then ((moebius u : ℤ) : ℚ) / (u : ℚ) else 0)
            * (∑ v ∈ I.I2, if Odd v ∧ D2 b s t ∣ v then
                ((moebius v : ℤ) : ℚ) / (v : ℚ) else 0) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hfactor, Cutoffs.I1, Cutoffs.I2, moebius_interval_extraction hD1pos hD1odd,
      moebius_interval_extraction hD2pos hD2odd]
    -- allocation algebra: μ(t) μ(D₁) μ(D₂) = μ(a) and D₁ D₂ = q t
    have hmu : moebius (D1 b r t) * moebius (D2 b s t) * moebius t = moebius a := by
      rw [moebius_D1_mul_D2 hb hst hcbr hcbs hcbt hcrs hcrt hcst, hrst]
    have hDD : (D1 b r t : ℚ) * (D2 b s t : ℚ) = ((a * b ^ 2 : ℕ) : ℚ) * (t : ℚ) := by
      have := D1_mul_D2 b r s t
      have hq : (D1 b r t * D2 b s t : ℕ) = (a * b ^ 2) * t := by rw [this, hrst]
      exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hq
    have hD1Q : ((D1 b r t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hD1pos.ne'
    have hD2Q : ((D2 b s t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hD2pos.ne'
    have htQ : ((t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ht0
    have haQ : ((a * b ^ 2 : ℕ) : ℚ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact Nat.mul_ne_zero ha0 (pow_ne_zero 2 hb0)
    have hmuQ : ((moebius (D1 b r t) : ℤ) : ℚ) * ((moebius (D2 b s t) : ℤ) : ℚ)
        * ((moebius t : ℤ) : ℚ) = ((moebius a : ℤ) : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hmu
    field_simp
    linear_combination (harm I.a1 I.b1 (D1 b r t) (2 * D1 b r t) *
        harm I.a2 I.b2 (D2 b s t) (2 * D2 b s t) * (t : ℚ) * ((a * b ^ 2 : ℕ) : ℚ)) * hmuQ
      - (harm I.a1 I.b1 (D1 b r t) (2 * D1 b r t) *
        harm I.a2 I.b2 (D2 b s t) (2 * D2 b s t) * ((moebius a : ℤ) : ℚ)) * hDD
  rw [Finset.sum_congr rfl h2]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
