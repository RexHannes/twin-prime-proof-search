/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
exact Möbius provenance of the complement allocation  (B4)

Append-only module.  Exact finite identities only, kernel-proved; nothing pre-existing is
edited.  The truncated Möbius coefficient `lam` of `TruncatedMobius.lean` is reused verbatim,
**with both sharp cutoffs `I₁`, `I₂` and both oddness conditions retained in every statement**.

Contents.

* §1  elementary Möbius/divisor algebra: `μ(d)μ(a/d) = μ(a)` for squarefree `a`, and the
  canonical coprime splitting `X = (X,a)(X,u)` of a divisor of `a u` with `(a,u) = 1`;
* §2  the coprime splitting of a divisor sum;
* §3  `lam` as a sum over divisors;
* §4  the **exact provenance identity** for the complement allocation `J = a₀`,

  ```
  λ(a₀ u) = μ(a₀) ∑_{d ∣ a₀} ∑_{xy = u} μ(x) μ(y) 1[d x ∈ I₁] 1[(a₀/d) y ∈ I₂] · (oddness),
  ```

* §5  the same identity with the square part `J = a₀ b₀²` present, `κ₁ = b₀ d`,
  `κ₂ = b₀ a₀/d`:

  ```
  λ(a₀ b₀² u) = μ(a₀) ∑_{d ∣ a₀} ∑_{xy = u} μ(x) μ(y) 1[κ₁ x ∈ I₁] 1[κ₂ y ∈ I₂] · (oddness);
  ```

* §6  the firewall: the sharp intervals may not be replaced by unrestricted support.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.PrimeAllocation

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Finset ArithmeticFunction
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. Möbius and divisor algebra -/

/-- A divisor of a squarefree number is coprime to its cofactor. -/
theorem coprime_div_of_squarefree {a d : ℕ} (h : Squarefree a) (hd : d ∣ a) :
    Nat.Coprime d (a / d) := by
  obtain ⟨c, rfl⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; simp at h
  rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hd0)]
  exact (Nat.squarefree_mul_iff.mp h).1

/-- **Exact Möbius allocation over a divisor**: `μ(d) μ(a/d) = μ(a)` for squarefree `a`. -/
theorem moebius_mul_div {a d : ℕ} (h : Squarefree a) (hd : d ∣ a) :
    moebius d * moebius (a / d) = moebius a := by
  have hmul : d * (a / d) = a := Nat.mul_div_cancel' hd
  calc moebius d * moebius (a / d)
      = moebius (d * (a / d)) :=
        (isMultiplicative_moebius.map_mul_of_coprime (coprime_div_of_squarefree h hd)).symm
    _ = moebius a := by rw [hmul]

/-- **Canonical coprime splitting of a divisor**: if `(a,u) = 1` and `X ∣ a u` then
`X = (X,a) · (X,u)`. -/
theorem dvd_eq_gcd_mul_gcd {a u X : ℕ} (hco : Nat.Coprime a u) (h : X ∣ a * u) :
    X = Nat.gcd X a * Nat.gcd X u := by
  obtain ⟨m, n, hm, hn, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
  have hna : Nat.Coprime n a := (Nat.Coprime.coprime_dvd_left hn hco.symm)
  have hmu : Nat.Coprime m u := (Nat.Coprime.coprime_dvd_left hm hco)
  have h1 : Nat.gcd (m * n) a = m := by
    rw [Nat.Coprime.gcd_mul_right_cancel m hna, Nat.gcd_eq_left hm]
  have h2 : Nat.gcd (m * n) u = n := by
    rw [Nat.Coprime.gcd_mul_left_cancel n hmu, Nat.gcd_eq_left hn]
  rw [h1, h2]

/-! ## 2. The coprime splitting of a divisor sum -/

/-- **Coprime splitting of a divisor sum.**  For `(a,u) = 1`, summing a function of the pair
`(X, au/X)` over the divisors of `a u` is the same as summing over pairs `(d, x)` of divisors of
`a` and of `u`, with `X = d x` and `au/X = (a/d)(u/x)`. -/
theorem sum_divisors_coprime_split {a u : ℕ} (hco : Nat.Coprime a u) (ha : a ≠ 0) (hu : u ≠ 0)
    (F : ℕ → ℕ → ℤ) :
    ∑ X ∈ (a * u).divisors, F X ((a * u) / X)
      = ∑ q ∈ a.divisors ×ˢ u.divisors, F (q.1 * q.2) ((a / q.1) * (u / q.2)) := by
  refine Finset.sum_nbij' (fun X => (Nat.gcd X a, Nat.gcd X u)) (fun q => q.1 * q.2) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    simp only [Nat.mem_divisors, Finset.mem_product] at hX ⊢
    exact ⟨⟨Nat.gcd_dvd_right X a, ha⟩, ⟨Nat.gcd_dvd_right X u, hu⟩⟩
  · intro q hq
    simp only [Nat.mem_divisors, Finset.mem_product] at hq ⊢
    exact ⟨mul_dvd_mul hq.1.1 hq.2.1, mul_ne_zero ha hu⟩
  · intro X hX
    simp only [Nat.mem_divisors] at hX
    exact (dvd_eq_gcd_mul_gcd hco hX.1).symm
  · intro q hq
    simp only [Nat.mem_divisors, Finset.mem_product] at hq
    have hna : Nat.Coprime q.2 a := Nat.Coprime.coprime_dvd_left hq.2.1 hco.symm
    have hmu : Nat.Coprime q.1 u := Nat.Coprime.coprime_dvd_left hq.1.1 hco
    have h1 : Nat.gcd (q.1 * q.2) a = q.1 := by
      rw [Nat.Coprime.gcd_mul_right_cancel q.1 hna, Nat.gcd_eq_left hq.1.1]
    have h2 : Nat.gcd (q.1 * q.2) u = q.2 := by
      rw [Nat.Coprime.gcd_mul_left_cancel q.2 hmu, Nat.gcd_eq_left hq.2.1]
    show (Nat.gcd (q.1 * q.2) a, Nat.gcd (q.1 * q.2) u) = q
    rw [h1, h2]
  · intro X hX
    simp only [Nat.mem_divisors] at hX
    have hsplit : X = Nat.gcd X a * Nat.gcd X u := dvd_eq_gcd_mul_gcd hco hX.1
    have hdiv : (a * u) / X = (a / Nat.gcd X a) * (u / Nat.gcd X u) := by
      rw [Nat.div_mul_div_comm (Nat.gcd_dvd_right X a) (Nat.gcd_dvd_right X u), ← hsplit]
    show F X ((a * u) / X)
      = F (Nat.gcd X a * Nat.gcd X u) ((a / Nat.gcd X a) * (u / Nat.gcd X u))
    rw [← hsplit, hdiv]

/-! ## 3. `lam` as a divisor sum -/

/-- **The truncated Möbius coefficient as a divisor sum**, both cutoffs and both oddness
conditions retained. -/
theorem lam_eq_divisors (I : Cutoffs) {N : ℕ} (hN : N ≠ 0) :
    lam I N = ∑ X ∈ N.divisors,
      (if X ∈ I.I1 ∧ N / X ∈ I.I2 ∧ Odd X ∧ Odd (N / X) then moebius X * moebius (N / X)
        else 0) := by
  rw [lam_eq_sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun p => p.1) (fun X => (X, N / X)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Nat.mem_divisors, Cutoffs.mem_box] at hp ⊢
    obtain ⟨hbox, hodd1, hodd2, hprod⟩ := hp
    have hdvd : p.1 ∣ N := ⟨p.2, hprod.symm⟩
    have hp1 : 0 < p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · exact absurd hprod (by rw [h]; simpa using hN.symm)
      · exact h
    have hq : N / p.1 = p.2 := by
      rw [← hprod, Nat.mul_div_cancel_left p.2 hp1]
    refine ⟨⟨hdvd, hN⟩, ?_, ?_, hodd1, ?_⟩
    · exact Cutoffs.mem_I1.mpr hbox.1
    · rw [hq]; exact Cutoffs.mem_I2.mpr hbox.2
    · rw [hq]; exact hodd2
  · intro X hX
    simp only [Finset.mem_filter, Nat.mem_divisors, Cutoffs.mem_box] at hX ⊢
    obtain ⟨⟨hdvd, -⟩, hI1, hI2, hodd1, hodd2⟩ := hX
    refine ⟨⟨Cutoffs.mem_I1.mp hI1, Cutoffs.mem_I2.mp hI2⟩, hodd1, hodd2, ?_⟩
    exact Nat.mul_div_cancel' hdvd
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨-, -, -, hprod⟩ := hp
    have hp1 : 0 < p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · exact absurd hprod (by rw [h]; simpa using hN.symm)
      · exact h
    have hq : N / p.1 = p.2 := by rw [← hprod, Nat.mul_div_cancel_left p.2 hp1]
    show (p.1, N / p.1) = p
    rw [hq]
  · intro X _
    rfl
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨-, -, -, hprod⟩ := hp
    have hp1 : 0 < p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · exact absurd hprod (by rw [h]; simpa using hN.symm)
      · exact h
    have hq : N / p.1 = p.2 := by rw [← hprod, Nat.mul_div_cancel_left p.2 hp1]
    show moebius p.1 * moebius p.2 = moebius p.1 * moebius (N / p.1)
    rw [hq]

/-! ## 4. The exact provenance identity (square-free complement `J = a₀`) -/

/-- **The allocation sum** with the two prefactors `κ₁ = b₀ d`, `κ₂ = b₀ (a₀/d)`:

`∑_{d ∣ a₀} ∑_{xy = u} μ(x) μ(y) 1[κ₁ x ∈ I₁] 1[κ₂ y ∈ I₂] 1[κ₁x, κ₂y odd]`. -/
def allocSum (I : Cutoffs) (b0 a0 u : ℕ) : ℤ :=
  ∑ q ∈ a0.divisors ×ˢ u.divisors,
    (if b0 * q.1 * q.2 ∈ I.I1 ∧ b0 * (a0 / q.1) * (u / q.2) ∈ I.I2
        ∧ Odd (b0 * q.1 * q.2) ∧ Odd (b0 * (a0 / q.1) * (u / q.2))
      then moebius q.2 * moebius (u / q.2) else 0)

/-- **Exact Möbius provenance, squarefree complement.**  For `(a₀,u) = 1` with `a₀` squarefree,

`λ(a₀ u) = μ(a₀) ∑_{d ∣ a₀} ∑_{xy = u} μ(x)μ(y) 1[d x ∈ I₁] 1[(a₀/d) y ∈ I₂] · (oddness)`.

All cutoffs, all oddness conditions and all coprimality conditions are retained. -/
theorem lam_mobius_provenance (I : Cutoffs) {a0 u : ℕ} (hco : Nat.Coprime a0 u)
    (ha0sq : Squarefree a0) (ha0 : a0 ≠ 0) (hu : u ≠ 0) :
    lam I (a0 * u) = moebius a0 * allocSum I 1 a0 u := by
  rw [lam_eq_divisors I (mul_ne_zero ha0 hu),
    sum_divisors_coprime_split hco ha0 hu
      (fun X Y => if X ∈ I.I1 ∧ Y ∈ I.I2 ∧ Odd X ∧ Odd Y then moebius X * moebius Y else 0),
    allocSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  simp only [Nat.mem_divisors, Finset.mem_product] at hq
  obtain ⟨⟨hd, -⟩, ⟨hx, -⟩⟩ := hq
  have hcop1 : Nat.Coprime q.1 q.2 :=
    Nat.Coprime.coprime_dvd_right hx (Nat.Coprime.coprime_dvd_left hd hco)
  have hcop2 : Nat.Coprime (a0 / q.1) (u / q.2) :=
    Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hx)
      (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hd) hco)
  have hmu1 : moebius (q.1 * q.2) = moebius q.1 * moebius q.2 :=
    isMultiplicative_moebius.map_mul_of_coprime hcop1
  have hmu2 : moebius ((a0 / q.1) * (u / q.2)) = moebius (a0 / q.1) * moebius (u / q.2) :=
    isMultiplicative_moebius.map_mul_of_coprime hcop2
  have hall : moebius q.1 * moebius (a0 / q.1) = moebius a0 := moebius_mul_div ha0sq hd
  by_cases hcond : q.1 * q.2 ∈ I.I1 ∧ (a0 / q.1) * (u / q.2) ∈ I.I2 ∧ Odd (q.1 * q.2)
      ∧ Odd ((a0 / q.1) * (u / q.2))
  · rw [if_pos hcond, if_pos (by simpa using hcond)]
    rw [hmu1, hmu2, ← hall]
    ring
  · rw [if_neg hcond, if_neg (by simpa using hcond), mul_zero]

/-! ## 5. The exact provenance identity with the square part `J = a₀ b₀²` -/

/-- If `p²` divides a product of two squarefree numbers, then `p` divides the first. -/
theorem prime_dvd_of_sq_dvd_mul {p X Y : ℕ} (hp : p.Prime) (hY : Squarefree Y)
    (h : p ^ 2 ∣ X * Y) : p ∣ X := by
  by_contra hpX
  have hcop : Nat.Coprime (p ^ 2) X :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpX)
  have hY2 : p ^ 2 ∣ Y := Nat.Coprime.dvd_of_dvd_mul_left hcop h
  rw [pow_two] at hY2
  have hu := hY p hY2
  rw [Nat.isUnit_iff] at hu
  exact hp.one_lt.ne' hu

/-- **The square part is forced into both factors.**  If `b₀` is squarefree and `b₀² ∣ X Y` with
`X`, `Y` squarefree, then `b₀ ∣ X`. -/
theorem sq_part_dvd {b0 X Y : ℕ} (hb0 : Squarefree b0) (hY : Squarefree Y)
    (h : b0 ^ 2 ∣ X * Y) : b0 ∣ X := by
  refine squarefree_dvd_of_primes_dvd hb0 fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpb : p ∣ b0 := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ^ 2 ∣ b0 ^ 2 := pow_dvd_pow_of_dvd hpb 2
  exact prime_dvd_of_sq_dvd_mul hpp hY (hp2.trans h)

/-- Division of the square-completed modulus by a `b₀`-multiple divisor. -/
theorem div_sq_mul {b0 X' W : ℕ} (hb0 : 0 < b0) (hX'0 : 0 < X') (hX' : X' ∣ W) :
    (b0 ^ 2 * W) / (b0 * X') = b0 * (W / X') := by
  obtain ⟨m, rfl⟩ := hX'
  rw [Nat.mul_div_cancel_left m hX'0]
  have hrw : b0 ^ 2 * (X' * m) = (b0 * X') * (b0 * m) := by ring
  rw [hrw, Nat.mul_div_cancel_left _ (Nat.mul_pos hb0 hX'0)]

/-- **Exact Möbius provenance with the square part.**  For `J = a₀ b₀²` with `a₀ b₀` squarefree,
`(a₀,u) = 1` and `(b₀, a₀u) = 1`,

`λ(a₀ b₀² u) = μ(a₀) ∑_{d ∣ a₀} ∑_{xy = u} μ(x)μ(y) 1[κ₁x ∈ I₁] 1[κ₂y ∈ I₂] · (oddness)`,

with `κ₁ = b₀ d`, `κ₂ = b₀ (a₀/d)`.  All cutoffs, oddness and coprimality conditions are
retained; no support is enlarged. -/
theorem lam_mobius_provenance_sq (I : Cutoffs) {a0 b0 u : ℕ} (hco : Nat.Coprime a0 u)
    (hb0sq : Squarefree b0) (hb0co : Nat.Coprime b0 (a0 * u)) (ha0sq : Squarefree a0)
    (ha0 : a0 ≠ 0) (hu : u ≠ 0) (hb0 : b0 ≠ 0) :
    lam I (a0 * b0 ^ 2 * u) = moebius a0 * allocSum I b0 a0 u := by
  have hb0pos : 0 < b0 := Nat.pos_of_ne_zero hb0
  have hW : a0 * u ≠ 0 := mul_ne_zero ha0 hu
  have hNW : a0 * b0 ^ 2 * u = b0 ^ 2 * (a0 * u) := by ring
  have hN : a0 * b0 ^ 2 * u ≠ 0 := by
    rw [hNW]; exact mul_ne_zero (pow_ne_zero 2 hb0) hW
  -- Step 1: the square part is forced into both factors, so only `b₀`-multiples contribute.
  have step1 : lam I (a0 * b0 ^ 2 * u)
      = ∑ X ∈ (a0 * b0 ^ 2 * u).divisors with (b0 ∣ X ∧ b0 ∣ (a0 * b0 ^ 2 * u) / X),
          (if X ∈ I.I1 ∧ (a0 * b0 ^ 2 * u) / X ∈ I.I2 ∧ Odd X ∧ Odd ((a0 * b0 ^ 2 * u) / X)
            then moebius X * moebius ((a0 * b0 ^ 2 * u) / X) else 0) := by
    rw [lam_eq_divisors I hN]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro X hX hne
    simp only [Nat.mem_divisors] at hX
    have hXY : X * ((a0 * b0 ^ 2 * u) / X) = a0 * b0 ^ 2 * u := Nat.mul_div_cancel' hX.1
    have hmu : moebius X * moebius ((a0 * b0 ^ 2 * u) / X) ≠ 0 := by
      intro h0
      apply hne
      by_cases hc : X ∈ I.I1 ∧ (a0 * b0 ^ 2 * u) / X ∈ I.I2 ∧ Odd X
          ∧ Odd ((a0 * b0 ^ 2 * u) / X)
      · rw [if_pos hc, h0]
      · rw [if_neg hc]
    have hsqX : Squarefree X := by
      by_contra h
      exact hmu (by rw [moebius_eq_zero_of_not_squarefree h, zero_mul])
    have hsqY : Squarefree ((a0 * b0 ^ 2 * u) / X) := by
      by_contra h
      exact hmu (by rw [moebius_eq_zero_of_not_squarefree h, mul_zero])
    have hdvdXY : b0 ^ 2 ∣ X * ((a0 * b0 ^ 2 * u) / X) := by
      rw [hXY, hNW]; exact Dvd.intro _ rfl
    have hdvdYX : b0 ^ 2 ∣ ((a0 * b0 ^ 2 * u) / X) * X := by
      rw [mul_comm]; exact hdvdXY
    exact ⟨sq_part_dvd hb0sq hsqY hdvdXY, sq_part_dvd hb0sq hsqX hdvdYX⟩
  -- Step 2: reindex `X = b₀ X'` and cancel `μ(b₀)² = 1`.
  have step2 : (∑ X ∈ (a0 * b0 ^ 2 * u).divisors with (b0 ∣ X ∧ b0 ∣ (a0 * b0 ^ 2 * u) / X),
          (if X ∈ I.I1 ∧ (a0 * b0 ^ 2 * u) / X ∈ I.I2 ∧ Odd X ∧ Odd ((a0 * b0 ^ 2 * u) / X)
            then moebius X * moebius ((a0 * b0 ^ 2 * u) / X) else 0))
      = ∑ X' ∈ (a0 * u).divisors,
          (if b0 * X' ∈ I.I1 ∧ b0 * ((a0 * u) / X') ∈ I.I2 ∧ Odd (b0 * X')
              ∧ Odd (b0 * ((a0 * u) / X'))
            then moebius X' * moebius ((a0 * u) / X') else 0) := by
    refine Finset.sum_nbij' (fun X => X / b0) (fun X' => b0 * X') ?_ ?_ ?_ ?_ ?_
    · intro X hX
      simp only [Finset.mem_filter, Nat.mem_divisors] at hX
      obtain ⟨⟨hdvd, -⟩, hb1, hb2⟩ := hX
      obtain ⟨X', rfl⟩ := hb1
      obtain ⟨m, hm⟩ := hb2
      have hmul : (b0 * X') * (b0 * m) = a0 * b0 ^ 2 * u := by
        rw [← hm, Nat.mul_div_cancel' hdvd]
      have hWm : X' * m = a0 * u := by
        have h2 : b0 ^ 2 * (X' * m) = b0 ^ 2 * (a0 * u) := by
          rw [← hNW, ← hmul]; ring
        exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
      simp only [Nat.mem_divisors, Nat.mul_div_cancel_left X' hb0pos]
      exact ⟨⟨m, hWm.symm⟩, hW⟩
    · intro X' hX'
      simp only [Nat.mem_divisors] at hX'
      obtain ⟨⟨m, hm⟩, -⟩ := hX'
      have hX'0 : 0 < X' := by
        rcases Nat.eq_zero_or_pos X' with h | h
        · exact absurd hm (by rw [h]; simpa using hW)
        · exact h
      have hdvd : b0 * X' ∣ a0 * b0 ^ 2 * u := by
        rw [hNW, hm]
        exact ⟨b0 * m, by ring⟩
      have hdiv : (a0 * b0 ^ 2 * u) / (b0 * X') = b0 * ((a0 * u) / X') := by
        rw [hNW]
        exact div_sq_mul hb0pos hX'0 ⟨m, hm⟩
      simp only [Finset.mem_filter, Nat.mem_divisors, hdiv]
      exact ⟨⟨hdvd, hN⟩, Dvd.intro X' rfl, Dvd.intro _ rfl⟩
    · intro X hX
      simp only [Finset.mem_filter] at hX
      show b0 * (X / b0) = X
      exact Nat.mul_div_cancel' hX.2.1
    · intro X' _
      show b0 * X' / b0 = X'
      exact Nat.mul_div_cancel_left X' hb0pos
    · intro X hX
      simp only [Finset.mem_filter, Nat.mem_divisors] at hX
      obtain ⟨⟨hdvd, -⟩, hb1, hb2⟩ := hX
      obtain ⟨X', rfl⟩ := hb1
      have hX'0 : 0 < X' := by
        rcases Nat.eq_zero_or_pos X' with h | h
        · exfalso
          apply hN
          rw [h, mul_zero] at hdvd
          exact zero_dvd_iff.mp hdvd
        · exact h
      obtain ⟨m, hm⟩ := hb2
      have hmul : (b0 * X') * (b0 * m) = a0 * b0 ^ 2 * u := by
        rw [← hm, Nat.mul_div_cancel' hdvd]
      have hWm : X' * m = a0 * u := by
        have h2 : b0 ^ 2 * (X' * m) = b0 ^ 2 * (a0 * u) := by
          rw [← hNW, ← hmul]; ring
        exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
      have hdiv : (a0 * b0 ^ 2 * u) / (b0 * X') = b0 * ((a0 * u) / X') := by
        rw [hNW]
        exact div_sq_mul hb0pos hX'0 ⟨m, hWm.symm⟩
      have hX'div : X' ∣ a0 * u := ⟨m, hWm.symm⟩
      have hcop1 : Nat.Coprime b0 X' :=
        Nat.Coprime.coprime_dvd_right hX'div hb0co
      have hcop2 : Nat.Coprime b0 ((a0 * u) / X') :=
        Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hX'div) hb0co
      have hmu1 : moebius (b0 * X') = moebius b0 * moebius X' :=
        isMultiplicative_moebius.map_mul_of_coprime hcop1
      have hmu2 : moebius (b0 * ((a0 * u) / X')) = moebius b0 * moebius ((a0 * u) / X') :=
        isMultiplicative_moebius.map_mul_of_coprime hcop2
      have hb2sq : moebius b0 * moebius b0 = 1 := by
        have := moebius_sq_eq_one_of_squarefree hb0sq
        rw [pow_two] at this
        exact this
      show (if b0 * X' ∈ I.I1 ∧ (a0 * b0 ^ 2 * u) / (b0 * X') ∈ I.I2 ∧ Odd (b0 * X')
            ∧ Odd ((a0 * b0 ^ 2 * u) / (b0 * X'))
          then moebius (b0 * X') * moebius ((a0 * b0 ^ 2 * u) / (b0 * X')) else 0)
        = (if b0 * (b0 * X' / b0) ∈ I.I1 ∧ b0 * ((a0 * u) / (b0 * X' / b0)) ∈ I.I2
              ∧ Odd (b0 * (b0 * X' / b0)) ∧ Odd (b0 * ((a0 * u) / (b0 * X' / b0)))
            then moebius (b0 * X' / b0) * moebius ((a0 * u) / (b0 * X' / b0)) else 0)
      rw [Nat.mul_div_cancel_left X' hb0pos, hdiv]
      by_cases hc : b0 * X' ∈ I.I1 ∧ b0 * ((a0 * u) / X') ∈ I.I2 ∧ Odd (b0 * X')
          ∧ Odd (b0 * ((a0 * u) / X'))
      · rw [if_pos hc, if_pos hc, hmu1, hmu2]
        calc moebius b0 * moebius X' * (moebius b0 * moebius ((a0 * u) / X'))
            = (moebius b0 * moebius b0) * (moebius X' * moebius ((a0 * u) / X')) := by ring
          _ = moebius X' * moebius ((a0 * u) / X') := by rw [hb2sq, one_mul]
      · rw [if_neg hc, if_neg hc]
  -- Step 3: split the remaining divisor sum along `(a₀, u) = 1`.
  rw [step1, step2,
    sum_divisors_coprime_split hco ha0 hu
      (fun X Y => if b0 * X ∈ I.I1 ∧ b0 * Y ∈ I.I2 ∧ Odd (b0 * X) ∧ Odd (b0 * Y)
        then moebius X * moebius Y else 0),
    allocSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  simp only [Nat.mem_divisors, Finset.mem_product] at hq
  obtain ⟨⟨hd, -⟩, ⟨hx, -⟩⟩ := hq
  have hcop1 : Nat.Coprime q.1 q.2 :=
    Nat.Coprime.coprime_dvd_right hx (Nat.Coprime.coprime_dvd_left hd hco)
  have hcop2 : Nat.Coprime (a0 / q.1) (u / q.2) :=
    Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hx)
      (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hd) hco)
  have hmu1 : moebius (q.1 * q.2) = moebius q.1 * moebius q.2 :=
    isMultiplicative_moebius.map_mul_of_coprime hcop1
  have hmu2 : moebius ((a0 / q.1) * (u / q.2)) = moebius (a0 / q.1) * moebius (u / q.2) :=
    isMultiplicative_moebius.map_mul_of_coprime hcop2
  have hall : moebius q.1 * moebius (a0 / q.1) = moebius a0 := moebius_mul_div ha0sq hd
  have hassoc1 : b0 * (q.1 * q.2) = b0 * q.1 * q.2 := by ring
  have hassoc2 : b0 * ((a0 / q.1) * (u / q.2)) = b0 * (a0 / q.1) * (u / q.2) := by ring
  rw [hassoc1, hassoc2]
  by_cases hcond : b0 * q.1 * q.2 ∈ I.I1 ∧ b0 * (a0 / q.1) * (u / q.2) ∈ I.I2
      ∧ Odd (b0 * q.1 * q.2) ∧ Odd (b0 * (a0 / q.1) * (u / q.2))
  · rw [if_pos hcond, if_pos hcond, hmu1, hmu2, ← hall]
    ring
  · rw [if_neg hcond, if_neg hcond, mul_zero]

/-! ## 6. Firewall: the sharp intervals are not removable -/

/-- **The sharp cutoffs may not be dropped.**  With `I₁ = I₂ = (0,1]`, `a₀ = 3`, `u = 1` the
allocation sum is `0`, whereas the unrestricted allocation (all `d ∣ a₀`) would contribute `2`
terms: the interval indicators are load-bearing in the provenance identity. -/
theorem allocSum_respects_cutoffs :
    allocSum ⟨0, 1, 0, 1⟩ 1 3 1 = 0 ∧ lam ⟨0, 1, 0, 1⟩ (3 * 1) = 0 := by
  constructor
  · simp [allocSum, Cutoffs.I1, Cutoffs.I2, Nat.divisors]
    decide
  · simpa using lam_ne_muConv.1

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
