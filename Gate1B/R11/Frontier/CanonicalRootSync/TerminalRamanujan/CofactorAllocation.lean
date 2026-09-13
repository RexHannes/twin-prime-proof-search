/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : cofactor allocation  (T6)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

For an odd cube-free modulus `q = a b²` with `a, b` squarefree and `(a,b) = 1`, the allocation
variables `r s t = a` (pairwise coprime) produce the two cofactors

```
D₁ = b r t,    D₂ = b s t.
```

This module proves the exact allocation algebra

* `D₁ D₂ = q t`   (the boxed identity),
* `μ(D₁) μ(D₂) μ(t) = μ(a)`   (the exact Möbius bookkeeping of the allocation),

defines the finite harmonic Möbius interval sum

```
H_D(I/d) = ∑_{A/d < n ≤ B/d, (n,D)=1} μ(n)/n
```

in a division-free integer formulation (`A < d n ≤ B`), and proves the **extraction lemma**

```
∑_{u ∈ (A,B], u odd, D ∣ u} μ(u)/u = (μ(D)/D) · H_{2D}(I/D)        (D odd, D > 0),
```

which is the step that produces the `H_{2D₁}(I₁/D₁) H_{2D₂}(I₂/D₂)` factors of the coefficient
formula.  `t` is *not* defined as a gcd of the residual cofactors: it is the designated
allocation variable, and the residual cofactors are only required to be coprime to `2Dᵢ`.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TruncatedMobius

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset ArithmeticFunction

/-! ## 1. The allocation variables and the exact allocation algebra -/

/-- The first cofactor `D₁ = b r t`. -/
def D1 (b r t : ℕ) : ℕ := b * r * t

/-- The second cofactor `D₂ = b s t`. -/
def D2 (b s t : ℕ) : ℕ := b * s * t

/-- **The boxed allocation identity** `D₁ D₂ = q t`, for `q = a b²` and `a = r s t`. -/
theorem D1_mul_D2 (b r s t : ℕ) : D1 b r t * D2 b s t = ((r * s * t) * b ^ 2) * t := by
  unfold D1 D2; ring

/-- **The Möbius bookkeeping of the allocation**: `μ(D₁) μ(D₂) μ(t) = μ(a)` with `a = r s t`.
(The square factors `μ(b)²` and `μ(t)²` are `1` because `b` and `t` are squarefree.) -/
theorem moebius_D1_mul_D2 {b r s t : ℕ} (hb : Squarefree b) (ht : Squarefree t)
    (hbr : Nat.Coprime b r) (hbs : Nat.Coprime b s) (hbt : Nat.Coprime b t)
    (hrs : Nat.Coprime r s) (hrt : Nat.Coprime r t) (hst : Nat.Coprime s t) :
    moebius (D1 b r t) * moebius (D2 b s t) * moebius t = moebius (r * s * t) := by
  have hbrt : Nat.Coprime (b * r) t := Nat.Coprime.mul_left hbt hrt
  have hbst : Nat.Coprime (b * s) t := Nat.Coprime.mul_left hbt hst
  have hrst : Nat.Coprime (r * s) t := Nat.Coprime.mul_left hrt hst
  have e1 : moebius (D1 b r t) = moebius b * moebius r * moebius t := by
    unfold D1
    rw [isMultiplicative_moebius.map_mul_of_coprime hbrt,
      isMultiplicative_moebius.map_mul_of_coprime hbr]
  have e2 : moebius (D2 b s t) = moebius b * moebius s * moebius t := by
    unfold D2
    rw [isMultiplicative_moebius.map_mul_of_coprime hbst,
      isMultiplicative_moebius.map_mul_of_coprime hbs]
  have e3 : moebius (r * s * t) = moebius r * moebius s * moebius t := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hrst,
      isMultiplicative_moebius.map_mul_of_coprime hrs]
  have hb2 : moebius b ^ 2 = 1 := moebius_sq_eq_one_of_squarefree hb
  have ht2 : moebius t ^ 2 = 1 := moebius_sq_eq_one_of_squarefree ht
  calc moebius (D1 b r t) * moebius (D2 b s t) * moebius t
      = (moebius b ^ 2) * (moebius t ^ 2) * (moebius r * moebius s * moebius t) := by
        rw [e1, e2]; ring
    _ = moebius r * moebius s * moebius t := by rw [hb2, ht2]; ring
    _ = moebius (r * s * t) := e3.symm

/-! ## 2. The finite harmonic Möbius interval sum -/

/-- **The finite harmonic Möbius interval sum** `H_D(I/d) = ∑_{A/d < n ≤ B/d, (n,D)=1} μ(n)/n`,
written without division: the range condition is `A < d n ≤ B`. -/
def harm (A B d D : ℕ) : ℚ :=
  ∑ n ∈ Finset.Ioc 0 B,
    if A < d * n ∧ d * n ≤ B ∧ Nat.Coprime n D then ((moebius n : ℤ) : ℚ) / (n : ℚ) else 0

/-- If `D ∣ u` with `u` odd, `D` odd and the cofactor `u / D` not coprime to `2D`, then `u` is
not squarefree, so `μ(u) = 0`: such terms are invisible to the extraction lemma. -/
theorem moebius_eq_zero_of_not_coprime_cofactor {D u : ℕ} (hD : 0 < D)
    (hu : 0 < u) (hodd : Odd u) (hdvd : D ∣ u) (hnc : ¬ Nat.Coprime (u / D) (2 * D)) :
    moebius u = 0 := by
  obtain ⟨n, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left n hD] at hnc
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hu)
  have hnodd : Odd n := by
    rcases Nat.even_or_odd n with he | ho
    · exact absurd (he.mul_left D) (by simpa [Nat.even_iff, Nat.odd_iff] using hodd)
    · exact ho
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd n (2 * D)) (by
    intro h
    exact hnc h)
  have hpn : p ∣ n := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hp2D : p ∣ 2 * D := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hpD : p ∣ D := by
    rcases (Nat.Prime.dvd_mul hp).1 hp2D with h2 | hD'
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
      subst hp2
      rw [Nat.odd_iff] at hnodd
      omega
    · exact hD'
  refine moebius_eq_zero_of_not_squarefree ?_
  intro hsq
  have : p * p ∣ D * n := mul_dvd_mul hpD hpn
  exact hp.not_isUnit (hsq p this)

/-- **The extraction lemma.**  For odd `D > 0`,
`∑_{u ∈ (A,B], u odd, D ∣ u} μ(u)/u = (μ(D)/D) · H_{2D}(I/D)`. -/
theorem moebius_interval_extraction {A B D : ℕ} (hD : 0 < D) (hDodd : Odd D) :
    (∑ u ∈ Finset.Ioc A B, if Odd u ∧ D ∣ u then ((moebius u : ℤ) : ℚ) / (u : ℚ) else 0)
      = ((moebius D : ℤ) : ℚ) / (D : ℚ) * harm A B D (2 * D) := by
  -- Step 1: discard the terms whose cofactor is not coprime to `2D` (their `μ` vanishes).
  have step1 :
      (∑ u ∈ Finset.Ioc A B, if Odd u ∧ D ∣ u then ((moebius u : ℤ) : ℚ) / (u : ℚ) else 0)
        = ∑ u ∈ Finset.Ioc A B,
            if Odd u ∧ D ∣ u ∧ Nat.Coprime (u / D) (2 * D) then
              ((moebius u : ℤ) : ℚ) / (u : ℚ) else 0 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : 0 < u := by
      have := Finset.mem_Ioc.1 hu
      omega
    by_cases h1 : Odd u ∧ D ∣ u
    · by_cases h2 : Nat.Coprime (u / D) (2 * D)
      · rw [if_pos h1, if_pos ⟨h1.1, h1.2, h2⟩]
      · rw [if_pos h1, if_neg (by tauto),
          moebius_eq_zero_of_not_coprime_cofactor hD hu0 h1.1 h1.2 h2]
        simp
    · rw [if_neg h1, if_neg (by tauto)]
  -- Step 2: reindex `u = D n`.
  rw [step1, ← Finset.sum_filter, harm, Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun u => u / D) (fun n => D * n) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hu ⊢
    obtain ⟨⟨hA, hB⟩, hodd, hdvd, hcop⟩ := hu
    have hu0 : 0 < u := by omega
    have hn0 : 0 < u / D := Nat.div_pos (Nat.le_of_dvd hu0 hdvd) hD
    have hmul : D * (u / D) = u := Nat.mul_div_cancel' hdvd
    have hle : u / D ≤ u := Nat.div_le_self u D
    refine ⟨⟨hn0, ?_⟩, ?_, ?_, hcop⟩ <;> omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hn0, hnB⟩, hA, hB, hcop⟩ := hn
    have hnodd : Odd n := by
      rcases Nat.even_or_odd n with he | ho
      · exfalso
        obtain ⟨k, hk⟩ := he
        have : (2 : ℕ) ∣ Nat.gcd n (2 * D) := Nat.dvd_gcd ⟨k, by omega⟩ ⟨D, rfl⟩
        rw [Nat.Coprime] at hcop
        omega
      · exact ho
    refine ⟨⟨hA, hB⟩, hDodd.mul hnodd, Dvd.intro n rfl, ?_⟩
    rwa [Nat.mul_div_cancel_left n hD]
  · intro u hu
    simp only [Finset.mem_filter] at hu
    exact Nat.mul_div_cancel' hu.2.2.1
  · intro n _
    exact Nat.mul_div_cancel_left n hD
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hu
    obtain ⟨⟨hA, hB⟩, hodd, hdvd, hcop⟩ := hu
    have hu0 : 0 < u := by omega
    have hmul : D * (u / D) = u := Nat.mul_div_cancel' hdvd
    have hcopDn : Nat.Coprime D (u / D) :=
      (Nat.Coprime.coprime_dvd_right ⟨2, by ring⟩ hcop).symm
    have hmu : moebius u = moebius D * moebius (u / D) := by
      conv_lhs => rw [← hmul]
      exact isMultiplicative_moebius.map_mul_of_coprime hcopDn
    have hDQ : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
    have hnQ : ((u / D : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.div_pos (Nat.le_of_dvd hu0 hdvd) hD).ne'
    rw [hmu]
    have : (u : ℚ) = (D : ℚ) * ((u / D : ℕ) : ℚ) := by
      rw [← Nat.cast_mul, hmul]
    rw [this]
    push_cast
    field_simp

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
