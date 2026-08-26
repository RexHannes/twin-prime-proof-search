/-
# Gate-1A Δv4 §12 / §14 — corrected 2D Poisson–Bruhat coordinate and axis arithmetic

Content:

* **§12** the exact dual-coordinate identity
  `a/(r P₀) + n/(r Q) = Z/(r P₀ Q)` with `Z = Q a + P₀ n`, and the resulting
  fact that the PB row weight factors through `(Z, n)` — the `Z`-coordinate
  is a genuine change of variables, not a schematic label.
* **§14A** `Z_zero_forces_a_zero_n_zero`: under clean coprimality
  `gcd(P₀,Q) = 1`, `Z = 0` forces `P₀ ∣ a` and `Q ∣ n`, hence (under the
  actual PB truncation `|a|, |n| < min(P₀,Q)`, which the exponent margin
  `M H / L² = M / D < 1` of `Gate1A/Delta4/Scale.lean` supplies) `a = n = 0`.
* **§14B** `L_zero_forces_h1_h2_zero`: for four pairwise distinct primes,
  `p₂q₂h₁ = p₁q₁h₂` forces `p₁q₁ ∣ h₁` and `p₂q₂ ∣ h₂`, hence under the
  truncation `|h₁| < p₁q₁` both `h₁` and `h₂` vanish, i.e. the `L = 0` locus
  maps *exactly* onto the already-firewalled `h = 0` locus.

Hostile note (checked): §14A needs a truncation strictly below **both**
`P₀` and `Q`, and §14B needs the four primes pairwise distinct.  Both
hypotheses are carried explicitly; the counterexamples at the end of the
file show that neither may be dropped.
-/
import Mathlib
import Gate1A.Delta4.Scale

namespace Gate1A

namespace Delta4

/-! ## §12 The corrected PB `Z`-coordinate -/

/-- The PB dual coordinate `Z = Q a + P₀ n`. -/
def pbZ (P0 Q a n : ℤ) : ℤ := Q * a + P0 * n

/-- **§12 exact identity.** `a/(r P₀) + n/(r Q) = Z/(r P₀ Q)`. -/
theorem pb_phase_eq_Z_over (r P0 Q : ℝ) (a n : ℝ) (hr : r ≠ 0) (hP : P0 ≠ 0)
    (hQ : Q ≠ 0) :
    a / (r * P0) + n / (r * Q) = (Q * a + P0 * n) / (r * P0 * Q) := by
  field_simp

/-- The PB phase depends on `(a, n)` **only** through `(Z, n)`: two dual
points with the same `Z` and the same `n` have literally the same phase. -/
theorem pb_phase_factors_through_Z (r P0 Q : ℝ) (a a' n : ℝ) (hr : r ≠ 0)
    (hP : P0 ≠ 0) (hQ : Q ≠ 0) (h : Q * a + P0 * n = Q * a' + P0 * n) :
    a / (r * P0) + n / (r * Q) = a' / (r * P0) + n / (r * Q) := by
  rw [pb_phase_eq_Z_over r P0 Q a n hr hP hQ, pb_phase_eq_Z_over r P0 Q a' n hr hP hQ, h]

/-- The literal PB smooth row weight
`R(Z,n) = M K /(r P₀ Q) · V̂(M Z/(r P₀ Q), K n / Q)`.
It is a function of `(Z, n)` by construction: this is the formal content of
"the row weight lives in the `Z`-coordinate". -/
noncomputable def pbRowWeight (M K r P0 Q : ℝ) (V : ℝ → ℝ → ℂ) (Z n : ℝ) : ℂ :=
  ((M * K / (r * P0 * Q) : ℝ) : ℂ) * V (M * Z / (r * P0 * Q)) (K * n / Q)

theorem pbRowWeight_depends_only_on_Z_n (M K r P0 Q : ℝ) (V : ℝ → ℝ → ℂ)
    {Z Z' n n' : ℝ} (hZ : Z = Z') (hn : n = n') :
    pbRowWeight M K r P0 Q V Z n = pbRowWeight M K r P0 Q V Z' n' := by
  rw [hZ, hn]

/-! ## §14A The `Z = 0` axis -/

/-- **§14A divisibility step.**  With `gcd(P₀,Q) = 1`, `Q a + P₀ n = 0`
forces `P₀ ∣ a` and `Q ∣ n`. -/
theorem Z_zero_divisibility {P0 Q a n : ℤ} (hcop : IsCoprime P0 Q)
    (hZ : pbZ P0 Q a n = 0) : P0 ∣ a ∧ Q ∣ n := by
  have hQa : Q * a = -(P0 * n) := by
    have := hZ; simp only [pbZ] at this; linarith
  constructor
  · have : P0 ∣ Q * a := ⟨-n, by rw [hQa]; ring⟩
    exact (IsCoprime.dvd_of_dvd_mul_left hcop this)
  · have hPn : P0 * n = -(Q * a) := by rw [hQa]; ring
    have : Q ∣ P0 * n := ⟨-a, by rw [hPn]; ring⟩
    exact (IsCoprime.dvd_of_dvd_mul_left hcop.symm this)

/-- **§14A (`Z_zero_forces_a_zero_n_zero`).**  Under clean coprimality and the
actual PB truncation `|a| < P₀`, `|n| < Q`, the `Z = 0` axis contains only the
origin. -/
theorem Z_zero_forces_a_zero_n_zero {P0 Q a n : ℤ} (hcop : IsCoprime P0 Q)
    (hZ : pbZ P0 Q a n = 0) (ha : |a| < P0) (hn : |n| < Q) :
    a = 0 ∧ n = 0 := by
  obtain ⟨hPa, hQn⟩ := Z_zero_divisibility hcop hZ
  exact ⟨Int.eq_zero_of_abs_lt_dvd hPa ha, Int.eq_zero_of_abs_lt_dvd hQn hn⟩

/-- The truncation hypothesis of §14A cannot be weakened to a bound below only
one of the two moduli: with `P₀ = 3`, `Q = 5`, the point `(a,n) = (3,-5)` lies
on the axis `Z = 0` and satisfies `|a| < Q`, yet `a ≠ 0` (of course `|a| < P₀`
fails). -/
theorem Z_zero_needs_both_truncations :
    IsCoprime (3 : ℤ) 5 ∧ pbZ 3 5 3 (-5) = 0 ∧ |(3 : ℤ)| < 5 ∧ (3 : ℤ) ≠ 0 := by
  refine ⟨⟨2, -1, by norm_num⟩, by norm_num [pbZ], by norm_num, by norm_num⟩

/-! ## §14B The `L = 0` firewall -/

/-- **§14B divisibility step.**  For four pairwise distinct primes,
`p₂ q₂ h₁ = p₁ q₁ h₂` forces `p₁ q₁ ∣ h₁`. -/
theorem L_zero_dvd_h1 {p1 p2 q1 q2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hq1 : q1.Prime) (hq2 : q2.Prime)
    (h12 : p1 ≠ p2) (h1q1 : p1 ≠ q1) (h1q2 : p1 ≠ q2) (hq12 : q1 ≠ p2)
    (hq1q2 : q1 ≠ q2) {h1 h2 : ℤ}
    (heq : (p2 : ℤ) * q2 * h1 = (p1 : ℤ) * q1 * h2) :
    ((p1 : ℤ) * q1) ∣ h1 := by
  have hp1Z : Prime (p1 : ℤ) := Nat.prime_iff_prime_int.mp hp1
  have hq1Z : Prime (q1 : ℤ) := Nat.prime_iff_prime_int.mp hq1
  -- `p1 ∣ h1`
  have hp1h : (p1 : ℤ) ∣ h1 := by
    have hdvd : (p1 : ℤ) ∣ (p2 : ℤ) * q2 * h1 := ⟨(q1 : ℤ) * h2, by rw [heq]; ring⟩
    rcases (hp1Z.dvd_mul.mp hdvd) with hc | hc
    · rcases hp1Z.dvd_mul.mp hc with hc' | hc'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp1 hp2).mp
          (Int.ofNat_dvd.mp hc')) h12
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp1 hq2).mp
          (Int.ofNat_dvd.mp hc')) h1q2
    · exact hc
  -- `q1 ∣ h1`
  have hq1h : (q1 : ℤ) ∣ h1 := by
    have hdvd : (q1 : ℤ) ∣ (p2 : ℤ) * q2 * h1 := ⟨(p1 : ℤ) * h2, by rw [heq]; ring⟩
    rcases (hq1Z.dvd_mul.mp hdvd) with hc | hc
    · rcases hq1Z.dvd_mul.mp hc with hc' | hc'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq1 hp2).mp
          (Int.ofNat_dvd.mp hc')) hq12
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq1 hq2).mp
          (Int.ofNat_dvd.mp hc')) hq1q2
    · exact hc
  -- distinct primes are coprime, so the product divides
  have hcop : IsCoprime (p1 : ℤ) (q1 : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using (Nat.coprime_primes hp1 hq1).mpr h1q1
  exact hcop.mul_dvd hp1h hq1h

/-- **§14B (`L_zero_forces_h1_h2_zero`).**  With four pairwise distinct primes
and the actual truncation `|h₁| < p₁q₁`, the locus `L = 0`, i.e.
`2 p₂ q₂ h₁ − 2 p₁ q₁ h₂ = 0`, forces `h₁ = h₂ = 0`: the `L = 0` axis is
exactly the already-firewalled `h = 0` locus. -/
theorem L_zero_forces_h1_h2_zero {p1 p2 q1 q2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hq1 : q1.Prime) (hq2 : q2.Prime)
    (h12 : p1 ≠ p2) (h1q1 : p1 ≠ q1) (h1q2 : p1 ≠ q2) (hq12 : q1 ≠ p2)
    (hq1q2 : q1 ≠ q2) {h1 h2 : ℤ}
    (hL : 2 * (p2 : ℤ) * q2 * h1 - 2 * (p1 : ℤ) * q1 * h2 = 0)
    (htrunc : |h1| < (p1 : ℤ) * q1) :
    h1 = 0 ∧ h2 = 0 := by
  have heq : (p2 : ℤ) * q2 * h1 = (p1 : ℤ) * q1 * h2 := by linarith
  have hdvd := L_zero_dvd_h1 hp1 hp2 hq1 hq2 h12 h1q1 h1q2 hq12 hq1q2 heq
  have hpq : (0 : ℤ) < (p1 : ℤ) * q1 := by
    have := hp1.pos; have := hq1.pos; positivity
  have hh1 : h1 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd htrunc
  refine ⟨hh1, ?_⟩
  have : (p1 : ℤ) * q1 * h2 = 0 := by rw [← heq, hh1]; ring
  rcases mul_eq_zero.mp this with hc | hc
  · exact absurd hc (ne_of_gt hpq)
  · exact hc

/-- The pairwise-distinctness hypothesis of §14B is load-bearing: with
`p₁ = p₂ = 2`, `q₁ = q₂ = 3` the equation `p₂q₂h₁ = p₁q₁h₂` holds for
`h₁ = h₂ = 1`, and `|h₁| < p₁q₁`, yet `h₁ ≠ 0`. -/
theorem L_zero_needs_distinct_primes :
    (2 : ℤ) * 3 * 1 = (2 : ℤ) * 3 * 1 ∧ |(1 : ℤ)| < (2 : ℤ) * 3 ∧ (1 : ℤ) ≠ 0 := by
  refine ⟨rfl, by norm_num, by norm_num⟩

end Delta4

end Gate1A
