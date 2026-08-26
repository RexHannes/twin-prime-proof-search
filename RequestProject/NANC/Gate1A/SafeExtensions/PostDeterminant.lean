/-
# NANC Gate 1A v9 — the true post-Cauchy determinant `Omega`

With the primed copy `ell1', ell2', delta', h1'` and

    Delta  = ell1*h1  − ell2*h2,
    Delta' = ell1'*h1' − ell2'*h2,

the post-Cauchy determinant is

    Omega = delta' * ell1 * ell2 * Delta' − delta * ell1' * ell2' * Delta.

Banked: the definition, its fully expanded (BC-style) form, and the *generic
rigidity* of the branch `Omega = 0` under explicit prime/size hypotheses.

**FIREWALL.**  Closing the zero branch is not the same as controlling the
nonzero post-determinant; nothing analytic follows.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

/-- `Delta = ell1*h1 − ell2*h2` (post-determinant convention). -/
def postDelta (ell1 ell2 h1 h2 : ℤ) : ℤ := ell1 * h1 - ell2 * h2

/-- The post-Cauchy determinant `Omega`. -/
def postDetOmega (delta delta' ell1 ell2 ell1' ell2' h1 h1' h2 : ℤ) : ℤ :=
  delta' * (ell1 * ell2) * postDelta ell1' ell2' h1' h2
    - delta * (ell1' * ell2') * postDelta ell1 ell2 h1 h2

/-- **Expanded BC-style form of `Omega`.** -/
theorem postDetOmega_factorization (delta delta' ell1 ell2 ell1' ell2' h1 h1' h2 : ℤ) :
    postDetOmega delta delta' ell1 ell2 ell1' ell2' h1 h1' h2
      = delta' * ell1 * ell2 * ell1' * h1' - delta' * ell1 * ell2 * ell2' * h2
        - delta * ell1' * ell2' * ell1 * h1 + delta * ell1' * ell2' * ell2 * h2 := by
  unfold postDetOmega postDelta; ring

/-- Two positive integer primes dividing one another are equal. -/
theorem int_eq_of_prime_dvd_prime {a b : ℤ} (ha : Prime a) (hb : Prime b)
    (hapos : 0 < a) (hbpos : 0 < b) (h : a ∣ b) : a = b := by
  obtain ⟨k, hk⟩ := h
  rcases hb.irreducible.isUnit_or_isUnit hk with hu | hu
  · exact absurd hu ha.not_unit
  · rcases Int.isUnit_iff.mp hu with rfl | rfl
    · omega
    · omega

/-- A positive prime `ell` cannot divide a nonzero integer of strictly smaller
absolute value. -/
theorem not_dvd_of_abs_lt {ell x : ℤ} (hx0 : x ≠ 0) (hlt : |x| < ell) : ¬ ell ∣ x := by
  intro hdvd
  have := Int.le_of_dvd (abs_pos.mpr hx0) ((dvd_abs _ _).mpr hdvd)
  omega

/-- **Amplifier matching from `Omega = 0`.**  Reducing modulo `ell1` and modulo
`ell1'` and using that `h2` and the `delta`'s are nonzero and smaller than every
amplifier prime, the two amplifier pairs must meet. -/
theorem postDet_zero_amplifier_match
    {delta delta' ell1 ell2 ell1' ell2' h1 h1' h2 : ℤ}
    (hp1 : Prime ell1) (hp2 : Prime ell2) (hp1' : Prime ell1') (hp2' : Prime ell2')
    (hpos1 : 0 < ell1) (hpos2 : 0 < ell2) (hpos1' : 0 < ell1') (hpos2' : 0 < ell2')
    (hne12 : ell1 ≠ ell2) (hne12' : ell1' ≠ ell2')
    (hh2 : h2 ≠ 0) (hh2lt : |h2| < ell1) (hh2lt' : |h2| < ell1')
    (hd : delta ≠ 0) (hdlt : |delta| < ell1)
    (hd' : delta' ≠ 0) (hd'lt : |delta'| < ell1')
    (hOmega : postDetOmega delta delta' ell1 ell2 ell1' ell2' h1 h1' h2 = 0) :
    (ell1 = ell1' ∨ ell1 = ell2') ∧ (ell1' = ell1 ∨ ell1' = ell2) := by
  have hexp : delta' * ell1 * ell2 * ell1' * h1' - delta' * ell1 * ell2 * ell2' * h2
      - delta * ell1' * ell2' * ell1 * h1 + delta * ell1' * ell2' * ell2 * h2 = 0 :=
    (postDetOmega_factorization delta delta' ell1 ell2 ell1' ell2' h1 h1' h2).symm.trans hOmega
  constructor
  · -- reduce modulo `ell1`
    have key : ell1 ∣ delta * ((ell1' * ell2') * (ell2 * h2)) := by
      refine ⟨-(delta' * ell2 * ell1' * h1') + delta' * ell2 * ell2' * h2
        + delta * ell1' * ell2' * h1, ?_⟩
      linear_combination hexp
    have h1dvd : ell1 ∣ ell1' * ell2' := by
      rcases hp1.dvd_mul.mp key with h | h
      · exact absurd h (not_dvd_of_abs_lt hd hdlt)
      · rcases hp1.dvd_mul.mp h with h' | h'
        · exact h'
        · rcases hp1.dvd_mul.mp h' with h'' | h''
          · exact absurd (int_eq_of_prime_dvd_prime hp1 hp2 hpos1 hpos2 h'') hne12
          · exact absurd h'' (not_dvd_of_abs_lt hh2 hh2lt)
    rcases hp1.dvd_mul.mp h1dvd with h | h
    · exact Or.inl (int_eq_of_prime_dvd_prime hp1 hp1' hpos1 hpos1' h)
    · exact Or.inr (int_eq_of_prime_dvd_prime hp1 hp2' hpos1 hpos2' h)
  · -- reduce modulo `ell1'`
    have key : ell1' ∣ delta' * ((ell1 * ell2) * (ell2' * h2)) := by
      refine ⟨delta' * ell1 * ell2 * h1' - delta * ell2' * ell1 * h1
        + delta * ell2' * ell2 * h2, ?_⟩
      linear_combination -hexp
    have h1dvd : ell1' ∣ ell1 * ell2 := by
      rcases hp1'.dvd_mul.mp key with h | h
      · exact absurd h (not_dvd_of_abs_lt hd' hd'lt)
      · rcases hp1'.dvd_mul.mp h with h' | h'
        · exact h'
        · rcases hp1'.dvd_mul.mp h' with h'' | h''
          · exact absurd (int_eq_of_prime_dvd_prime hp1' hp2' hpos1' hpos2' h'') hne12'
          · exact absurd h'' (not_dvd_of_abs_lt hh2 hh2lt')
    rcases hp1'.dvd_mul.mp h1dvd with h | h
    · exact Or.inl (int_eq_of_prime_dvd_prime hp1' hp1 hpos1' hpos1 h)
    · exact Or.inr (int_eq_of_prime_dvd_prime hp1' hp2 hpos1' hpos2 h)

/-- **Generic post-determinant zero rigidity (long diagonal).**

Hypotheses, all explicit:

* `ell1, ell2, ell1', ell2'` are positive primes with `ell1 ≠ ell2`,
  `ell1' ≠ ell2'`, and the *no-swap* hypothesis `ell1 ≠ ell2'`;
* `h1, h2 ≠ 0` with `|h2| < ell1, ell1'` and `|h1| < ell2`;
* `delta, delta' ≠ 0` with `|delta| < ell1, ell2`, `|delta'| < ell1'` and the
  separation `|delta| + |delta'| < ell1`;
* `Omega = 0`.

Conclusion: the two data sets coincide,
`ell1 = ell1'`, `ell2 = ell2'`, `delta = delta'`, `h1 = h1'`.

The hypotheses `|h1| < ell2` (needed for the `ell2`-reduction), `ell1 ≠ ell2'`
(the genuine swapped solution branch is otherwise possible) and
`|delta| + |delta'| < ell1` (instead of `|delta|, |delta'| < ell1`) are the
explicit repairs required to make the stated conclusion true. -/
theorem postDet_zero_generic_longDiagonal
    {delta delta' ell1 ell2 ell1' ell2' h1 h1' h2 : ℤ}
    (hp1 : Prime ell1) (hp2 : Prime ell2) (hp1' : Prime ell1') (hp2' : Prime ell2')
    (hpos1 : 0 < ell1) (hpos2 : 0 < ell2) (hpos1' : 0 < ell1') (hpos2' : 0 < ell2')
    (hne12 : ell1 ≠ ell2) (hne12' : ell1' ≠ ell2') (hnoswap : ell1 ≠ ell2')
    (hh1 : h1 ≠ 0) (hh1lt : |h1| < ell2)
    (hh2 : h2 ≠ 0) (hh2lt : |h2| < ell1) (hh2lt' : |h2| < ell1')
    (hd : delta ≠ 0) (hdlt : |delta| < ell1) (hdlt2 : |delta| < ell2)
    (hd' : delta' ≠ 0) (hd'lt : |delta'| < ell1')
    (hsep : |delta| + |delta'| < ell1)
    (hOmega : postDetOmega delta delta' ell1 ell2 ell1' ell2' h1 h1' h2 = 0) :
    ell1 = ell1' ∧ ell2 = ell2' ∧ delta = delta' ∧ h1 = h1' := by
  have hexp : delta' * ell1 * ell2 * ell1' * h1' - delta' * ell1 * ell2 * ell2' * h2
      - delta * ell1' * ell2' * ell1 * h1 + delta * ell1' * ell2' * ell2 * h2 = 0 :=
    (postDetOmega_factorization delta delta' ell1 ell2 ell1' ell2' h1 h1' h2).symm.trans hOmega
  -- Step 1: `ell1 = ell1'`.
  have hmatch := postDet_zero_amplifier_match hp1 hp2 hp1' hp2' hpos1 hpos2 hpos1' hpos2'
    hne12 hne12' hh2 hh2lt hh2lt' hd hdlt hd' hd'lt hOmega
  have hE1 : ell1 = ell1' := by
    rcases hmatch.1 with h | h
    · exact h
    · exact absurd h hnoswap
  -- Step 2: `ell2 = ell2'`, by reduction modulo `ell2`.
  have key2 : ell2 ∣ delta * ((ell1' * ell2') * (ell1 * h1)) := by
    refine ⟨delta' * ell1 * ell1' * h1' - delta' * ell1 * ell2' * h2
      + delta * ell1' * ell2' * h2, ?_⟩
    linear_combination -hexp
  have hdvd2 : ell2 ∣ ell1' * ell2' := by
    rcases hp2.dvd_mul.mp key2 with h | h
    · exact absurd h (not_dvd_of_abs_lt hd hdlt2)
    · rcases hp2.dvd_mul.mp h with h' | h'
      · exact h'
      · rcases hp2.dvd_mul.mp h' with h'' | h''
        · exact absurd (int_eq_of_prime_dvd_prime hp2 hp1 hpos2 hpos1 h'').symm hne12
        · exact absurd h'' (not_dvd_of_abs_lt hh1 hh1lt)
  have hE2 : ell2 = ell2' := by
    rcases hp2.dvd_mul.mp hdvd2 with h | h
    · have : ell2 = ell1' := int_eq_of_prime_dvd_prime hp2 hp1' hpos2 hpos1' h
      exact absurd (hE1.trans this.symm) hne12
    · exact int_eq_of_prime_dvd_prime hp2 hp2' hpos2 hpos2' h
  subst hE1; subst hE2
  -- Step 3: cancel `ell1 * ell2`.
  have hcancel : ell1 * ell2 * (ell1 * (delta' * h1' - delta * h1)
      - ell2 * h2 * (delta' - delta)) = 0 := by linear_combination hexp
  have hne : (ell1 : ℤ) * ell2 ≠ 0 := by positivity
  have hred : ell1 * (delta' * h1' - delta * h1) = ell2 * h2 * (delta' - delta) := by
    have := (mul_eq_zero.mp hcancel).resolve_left hne
    linarith
  -- Step 4: `delta = delta'`.
  have hdvdD : ell1 ∣ ell2 * (h2 * (delta' - delta)) := by
    refine ⟨delta' * h1' - delta * h1, ?_⟩
    linear_combination -hred
  have hdvdD' : ell1 ∣ delta' - delta := by
    rcases hp1.dvd_mul.mp hdvdD with h | h
    · exact absurd (int_eq_of_prime_dvd_prime hp1 hp2 hpos1 hpos2 h) hne12
    · rcases hp1.dvd_mul.mp h with h' | h'
      · exact absurd h' (not_dvd_of_abs_lt hh2 hh2lt)
      · exact h'
  have hdd : delta' - delta = 0 := by
    by_contra hzero
    have := Int.le_of_dvd (abs_pos.mpr hzero) ((dvd_abs _ _).mpr hdvdD')
    have habs : |delta' - delta| ≤ |delta'| + |delta| := abs_sub _ _
    linarith
  have hdeq : delta = delta' := by linarith
  -- Step 5: `h1 = h1'`.
  subst hdeq
  have h5 : ell1 * (delta * (h1' - h1)) = 0 := by linear_combination hred
  have : delta * (h1' - h1) = 0 := by
    rcases mul_eq_zero.mp h5 with h | h
    · omega
    · exact h
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hd
  · exact ⟨rfl, rfl, rfl, by linarith⟩

end TwinPrimeProject.NANC.Gate1A.V9
