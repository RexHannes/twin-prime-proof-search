/-
# Gate 1B safe extension — the exact PCL identity for the MIXED centered face

Everything in this file is an exact finite arithmetic identity.  There is no
smoothness claim, no asymptotic claim, and no analytic input.

Contents.

* `ramanujanSum h N` — the Ramanujan sum in its Hölder (divisor) form
  `c_h(N) = ∑_{e ∣ h, e ∣ N} e μ(h/e)`.
* `ramanujanSum_over_divisors` — the exact identity `∑_{h ∣ d} c_h(N) = d 1_{d ∣ N}`
  (Möbius inversion; no character theory needed).
* `ramanujanProperDivisors_eq_centeredDivisibility` —
  `∑_{h ∣ d, h > 1} c_h(N) = d ρ_d(N)` for the banked convention
  `ρ_d(N) = 1_{d ∣ N} − 1/d`.
* `squarefree_divisor_coprime_quotient`, `moebius_split_squarefree_divisor` —
  the exact `d = h s` splitting on squarefree `d`.
* `pclMixedFace_exact` / `betaMixedFace_to_PCL_exact` — the exact reindexing of
  the mixed centered face into PCL form.

## FIREWALL (scope)

The identity proved here is for the **MIXED CENTERED FACE**

    B_cross = ∑_d μ(d) ∑_p L_p ρ_d(N) ρ_p(N) W(d,p)

only.  It does **not** say that a raw `β(q)` shell equals the PCL expression:
the HFMV unary faces `UnaryD` and `UnaryP` of
`Gate1B/SafeExtensions/MixedFaceScope.lean` are not included, and by
`mixedFace_ne_raw_without_unary_hypotheses` they genuinely cannot be dropped.
-/
import Gate1B.SafeExtensions.MixedFaceScope

namespace Gate1B.SafeExtensions

open Finset ArithmeticFunction TwinPrimeProject.Gate01Consolidation

/-! ## 1. The exact Ramanujan divisor identity -/

/-- Ramanujan sum in Hölder (divisor) form: `c_h(N) = ∑_{e ∣ h, e ∣ N} e μ(h/e)`,
written over `divisorsAntidiagonal` as `∑_{ab = h} μ(a) · b · 1_{b ∣ N}`. -/
noncomputable def ramanujanSum (h N : ℕ) : ℝ :=
  ∑ x ∈ h.divisorsAntidiagonal, (moebius x.1 : ℝ) * (if x.2 ∣ N then (x.2 : ℝ) else 0)

/-- **Exact Ramanujan divisor identity.**  `∑_{h ∣ d} c_h(N) = d · 1_{d ∣ N}`. -/
theorem ramanujanSum_over_divisors (N : ℕ) : ∀ d, 0 < d →
    ∑ h ∈ d.divisors, ramanujanSum h N = if d ∣ N then (d : ℝ) else 0 := by
  rw [ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun h => ramanujanSum h N) (g := fun n => if n ∣ N then (n : ℝ) else 0)]
  intro n _
  rw [ramanujanSum]

theorem ramanujanSum_one (N : ℕ) : ramanujanSum 1 N = 1 := by
  simp [ramanujanSum]

/-- **Proper-divisor Ramanujan identity.**  For the banked centering convention
`ρ_d(N) = 1_{d ∣ N} − 1/d`, one has `∑_{h ∣ d, h > 1} c_h(N) = d ρ_d(N)`. -/
theorem ramanujanProperDivisors_eq_centeredDivisibility (d N : ℕ) (hd : 0 < d) :
    ∑ h ∈ d.divisors.filter (fun h => 1 < h), ramanujanSum h N = d * rho d N := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsplit := Finset.sum_filter_add_sum_filter_not d.divisors (fun h => 1 < h)
      (fun h => ramanujanSum h N)
  have hone : (d.divisors.filter (fun h => ¬ 1 < h)) = ({1} : Finset ℕ) := by
    ext x
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton, not_lt]
    constructor
    · rintro ⟨⟨hxd, _⟩, hx1⟩
      have := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hxd, hd.ne'⟩)
      omega
    · rintro rfl
      exact ⟨⟨one_dvd _, hd.ne'⟩, le_refl 1⟩
  rw [hone, Finset.sum_singleton, ramanujanSum_one] at hsplit
  rw [ramanujanSum_over_divisors N d hd] at hsplit
  have hval : (d : ℝ) * rho d N = (if d ∣ N then (d : ℝ) else 0) - 1 := by
    unfold rho
    rw [mul_sub, mul_one_div, div_self hdR]
    split_ifs <;> ring
  rw [hval]
  linarith

/-- `ρ_d(N)` as the exact average of Ramanujan sums over proper divisors. -/
theorem rho_eq_ramanujan_average (d N : ℕ) (hd : 0 < d) :
    rho d N = (1 / d) * ∑ h ∈ d.divisors.filter (fun h => 1 < h), ramanujanSum h N := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [ramanujanProperDivisors_eq_centeredDivisibility d N hd]
  field_simp

/-! ## 2. Squarefree divisor splitting -/

/-- On a squarefree `d`, a factorisation `d = h s` has coprime factors. -/
theorem squarefree_divisor_coprime_quotient {d h s : ℕ} (hsq : Squarefree d)
    (hd : h * s = d) : Nat.Coprime h s := by
  subst hd
  exact (Nat.squarefree_mul_iff.mp hsq).1

/-- On a squarefree `d = h s`, `μ(d) = μ(h) μ(s)` exactly. -/
theorem moebius_split_squarefree_divisor {d h s : ℕ} (hsq : Squarefree d)
    (hd : h * s = d) : moebius d = moebius h * moebius s := by
  subst hd
  exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (squarefree_divisor_coprime_quotient hsq rfl)

/-! ## 3. The PCL coefficient and pair index set -/

/-- The PCL coefficient `H_h(N) = μ(h) c_h(N)`. -/
noncomputable def pclH (h N : ℕ) : ℝ := (moebius h : ℝ) * ramanujanSum h N

/-- The PCL pair index set: all factorisations `d = h s` with `d ∈ D` and `h > 1`.
All support conditions of the original `d`-sum are transported into this set. -/
def pclPairs (D : Finset ℕ) : Finset (ℕ × ℕ) :=
  D.biUnion (fun d => d.divisorsAntidiagonal.filter (fun x => 1 < x.1))

theorem mem_pclPairs {D : Finset ℕ} {x : ℕ × ℕ} :
    x ∈ pclPairs D ↔ ∃ d ∈ D, x.1 * x.2 = d ∧ d ≠ 0 ∧ 1 < x.1 := by
  simp only [pclPairs, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨d, hd, ⟨hprod, hne⟩, h1⟩
    exact ⟨d, hd, hprod, hne, h1⟩
  · rintro ⟨d, hd, hprod, hne, h1⟩
    exact ⟨d, hd, ⟨hprod, hne⟩, h1⟩

/-- Support transport: every PCL pair `(h, s)` has `h s ∈ D`, `h > 1`, `s > 0`,
and — when `D` consists of squarefree numbers — coprime, squarefree components. -/
theorem pclPairs_support {D : Finset ℕ} (hD : ∀ d ∈ D, 0 < d ∧ Squarefree d)
    {x : ℕ × ℕ} (hx : x ∈ pclPairs D) :
    x.1 * x.2 ∈ D ∧ 1 < x.1 ∧ 0 < x.2 ∧ Nat.Coprime x.1 x.2 ∧
      Squarefree x.1 ∧ Squarefree x.2 := by
  obtain ⟨d, hdD, hprod, _, h1⟩ := mem_pclPairs.mp hx
  obtain ⟨hdpos, hsq⟩ := hD d hdD
  subst hprod
  have hmul := Nat.squarefree_mul_iff.mp hsq
  refine ⟨hdD, h1, ?_, hmul.1, hmul.2.1, hmul.2.2⟩
  rcases Nat.eq_zero_or_pos x.2 with h | h
  · rw [h, mul_zero] at hdpos; exact absurd hdpos (lt_irrefl 0)
  · exact h

/-- Reindexing a filtered divisor sum as a filtered antidiagonal sum. -/
theorem sum_antidiagonal_filter_gt_one (d : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ x ∈ d.divisorsAntidiagonal.filter (fun x => 1 < x.1), F x.1 x.2
      = ∑ h ∈ d.divisors.filter (fun h => 1 < h), F h (d / h) := by
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Nat.sum_divisorsAntidiagonal (f := fun h s => if 1 < h then F h s else 0)]

/-- The antidiagonal blocks of distinct `d` are disjoint, so the PCL pair sum
splits as an iterated sum. -/
theorem sum_pclPairs (D : Finset ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ x ∈ pclPairs D, F x
      = ∑ d ∈ D, ∑ x ∈ d.divisorsAntidiagonal.filter (fun x => 1 < x.1), F x := by
  refine Finset.sum_biUnion ?_
  intro a _ b _ hab
  simp only [Finset.disjoint_left, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
  rintro x ⟨⟨hxa, -⟩, -⟩ ⟨⟨hxb, -⟩, -⟩
  exact hab (hxa ▸ hxb)

/-! ## 4. The exact mixed-face → PCL reindexing -/

/-- The mixed centered face, with arbitrary finite prime weights `L`, arbitrary
source weights `W`, and arbitrary finite supports `D`, `P`. -/
noncomputable def BCross (N : ℕ) (D P : Finset ℕ) (L : ℕ → ℝ) (W : ℕ → ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, (moebius d : ℝ) * ∑ p ∈ P, L p * rho d N * rho p N * W d p

/-- The PCL form of the mixed centered face. -/
noncomputable def PCLForm (N : ℕ) (D P : Finset ℕ) (L : ℕ → ℝ) (W : ℕ → ℕ → ℝ) : ℝ :=
  ∑ x ∈ pclPairs D, ((moebius x.2 : ℝ) / x.2) * ((1 / x.1) * pclH x.1 N) *
    ∑ p ∈ P, L p * W (x.1 * x.2) p * rho p N

/-- **Exact PCL reindexing of the mixed centered face.**

    ∑_d μ(d) ∑_p L_p ρ_d(N) ρ_p(N) W(d,p)
      = ∑_{(h,s), hs ∈ D, h > 1} (μ(s)/s) (1/h) H_h(N) ∑_p L_p W(hs,p) ρ_p(N).

All support conditions are transported into `pclPairs D` (see
`pclPairs_support`); the only hypothesis is that every `d ∈ D` is positive and
squarefree.  The weights `L` and `W` are arbitrary.

**Scope**: this is the MIXED face only — see the file header firewall. -/
theorem pclMixedFace_exact (N : ℕ) (D P : Finset ℕ) (L : ℕ → ℝ) (W : ℕ → ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d ∧ Squarefree d) :
    BCross N D P L W = PCLForm N D P L W := by
  unfold BCross PCLForm
  rw [sum_pclPairs]
  refine Finset.sum_congr rfl fun d hdD => ?_
  obtain ⟨hdpos, hsq⟩ := hD d hdD
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  set G : ℝ := ∑ p ∈ P, L p * W d p * rho p N with hG
  -- the inner `p`-sum factors out `ρ_d(N)`
  have hinner : (∑ p ∈ P, L p * rho d N * rho p N * W d p) = rho d N * G := by
    rw [hG, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  -- each PCL term at a factorisation `d = h s`
  have hterm : ∀ x ∈ d.divisorsAntidiagonal.filter (fun x => 1 < x.1),
      ((moebius x.2 : ℝ) / x.2) * ((1 / x.1) * pclH x.1 N) *
        (∑ p ∈ P, L p * W (x.1 * x.2) p * rho p N)
      = ((moebius d : ℝ) / d) * G * ramanujanSum x.1 N := by
    intro x hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨⟨hprod, -⟩, h1⟩ := hx
    have hcast : (x.1 : ℝ) * (x.2 : ℝ) = (d : ℝ) := by
      rw [← Nat.cast_mul, hprod]
    have hx1 : (x.1 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hcast
      exact hdR hcast.symm
    have hx2 : (x.2 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcast
      exact hdR hcast.symm
    have hmu : (moebius d : ℝ) = (moebius x.1 : ℝ) * (moebius x.2 : ℝ) := by
      rw [moebius_split_squarefree_divisor hsq hprod]
      push_cast
      ring
    rw [hprod, ← hG, hmu, pclH]
    field_simp
    rw [← hcast]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_antidiagonal_filter_gt_one d (fun h _ => ramanujanSum h N),
    ramanujanProperDivisors_eq_centeredDivisibility d N hdpos, hinner]
  field_simp

/-- Gate-labelled restatement: the centered mixed face is exactly the PCL sum. -/
theorem betaMixedFace_to_PCL_exact (N : ℕ) (D P : Finset ℕ) (L : ℕ → ℝ) (W : ℕ → ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d ∧ Squarefree d) :
    (∑ d ∈ D, (moebius d : ℝ) * ∑ p ∈ P, L p * rho d N * rho p N * W d p)
      = ∑ x ∈ pclPairs D, ((moebius x.2 : ℝ) / x.2) * ((1 / x.1) * pclH x.1 N) *
          ∑ p ∈ P, L p * W (x.1 * x.2) p * rho p N :=
  pclMixedFace_exact N D P L W hD

end Gate1B.SafeExtensions
