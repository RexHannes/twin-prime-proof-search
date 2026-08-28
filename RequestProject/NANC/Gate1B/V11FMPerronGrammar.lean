import Mathlib

/-!
# V11 · Gate 1B — the Ford/Perron **generated coefficient grammar** (atoms)

This module is strictly append-only v11 work.  Nothing in the V10 bank is
modified, imported-for-modification, or re-proved.

## What this file is

A *finite syntax* for the coefficient atoms that a Perron-style decomposition
is allowed to generate, together with an **explicit semantic realisation**
`semAtom : GenAtom → ℕ → ℂ`.  No atom carries an arbitrary function: every
constructor carries finitely many explicit numerical parameters, so that
"generated" is a genuine restriction and not a synonym for "arbitrary".

## What this file is NOT

* It is **not** a claim that the coefficients of Ford–Maynard Proposition 7.22
  (or of any other paper) belong to this class.  No provenance statement is
  made here; see `V11FMProvenance.lean`.
* The least/greatest-prime twists are **not** realised.  The repository
  contains no definition of `P⁻(n)` or `P⁺(n)` (searched: `Pminus`, `Pplus`,
  `leastPrime`, `greatestPrime` — all absent).  They are therefore carried by a
  *separate abstract atom type* `PrimeExtremaAtom` whose semantic realisation
  requires a `PrimeExtremaRealisation`, a structure that this project **does
  not inhabit**.

No `sorry`, no user axiom, no `native_decide`.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-! ## 1. Semantic tags -/

/-- The ten semantic tags of the proposed generated grammar.  The last two tags
(`boundedConvolution`, `finiteLinearCombination`) are *expression-level*
constructors, realised in `V11GeneratedExpression.lean`; the first eight are
atom-level. -/
inductive AtomTag
  | mobius
  | constant
  | boxCutoff
  | smoothWeight
  | mellinTwist
  | leastPrimeTwist
  | greatestPrimeTwist
  | perfectPowerPullback
  | boundedConvolution
  | finiteLinearCombination
  deriving DecidableEq, Repr, Fintype

/-! ## 2. Realisable atoms -/

/-- **Realisable generated atoms.**  Each constructor carries only explicit
numerical parameters. -/
inductive GenAtom
  /-- The Möbius function. -/
  | mobius
  /-- A constant coefficient. -/
  | constant (c : ℂ)
  /-- The sharp box cut-off of the interval `[lo, hi]`. -/
  | boxCutoff (lo hi : ℕ)
  /-- The normalised linear window: `1` on `[0,a]`, `0` on `[b,∞)`, linear in
  between.  A finitely parameterised smooth-type weight, *not* an arbitrary
  function. -/
  | smoothWeight (a b : ℕ)
  /-- The Mellin twist `n ↦ n^{it}`. -/
  | mellinTwist (t : ℝ)
  /-- The pullback of the indicator of the perfect `k`-th powers. -/
  | perfectPowerPullback (k : ℕ)

/-- The semantic tag of a realisable atom. -/
def GenAtom.tag : GenAtom → AtomTag
  | .mobius => .mobius
  | .constant _ => .constant
  | .boxCutoff _ _ => .boxCutoff
  | .smoothWeight _ _ => .smoothWeight
  | .mellinTwist _ => .mellinTwist
  | .perfectPowerPullback _ => .perfectPowerPullback

/-- The linear window, as a real function. -/
noncomputable def rampR (a b : ℕ) (n : ℕ) : ℝ :=
  if n ≤ a then 1 else if b ≤ n then 0 else ((b : ℝ) - n) / ((b : ℝ) - a)

/-- **Semantics of the realisable atoms.** -/
noncomputable def semAtom : GenAtom → ℕ → ℂ
  | .mobius, n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  | .constant c, _ => c
  | .boxCutoff lo hi, n => if lo ≤ n ∧ n ≤ hi then 1 else 0
  | .smoothWeight a b, n => ((rampR a b n : ℝ) : ℂ)
  | .mellinTwist t, n => ((n : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
  | .perfectPowerPullback k, n =>
      if ((Finset.range (n + 1)).filter (fun m => m ^ k = n)).Nonempty then 1 else 0

/-- **Admissibility** of an atom: the finitely many parameters are in range.
Only `constant` and `smoothWeight` carry a genuine condition. -/
def GenAtom.Admissible : GenAtom → Prop
  | .mobius => True
  | .constant c => ‖c‖ ≤ 1
  | .boxCutoff _ _ => True
  | .smoothWeight a b => a < b
  | .mellinTwist _ => True
  | .perfectPowerPullback _ => True

/-! ## 3. Unit bound for admissible atoms -/

/-- A unimodular power of a nonnegative real base has norm at most one. -/
theorem norm_cpow_I_mul_le_one (x : ℝ) (hx : 0 ≤ x) (t : ℝ) :
    ‖(x : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤ 1 := by
  rcases hx.lt_or_eq with h | h
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos h]; simp
  · rcases eq_or_ne t 0 with rfl | ht
    · simp
    · have hx0 : x = 0 := h.symm
      have hexp : Complex.I * (t : ℂ) ≠ 0 := by
        simp [Complex.ext_iff, ht]
      rw [hx0]
      simp [Complex.zero_cpow hexp]

/-- The linear window takes values in `[0,1]`. -/
theorem rampR_mem_unitInterval (a b n : ℕ) (hab : a < b) :
    0 ≤ rampR a b n ∧ rampR a b n ≤ 1 := by
  unfold rampR
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  split_ifs with h1 h2
  · exact ⟨by norm_num, le_refl 1⟩
  · exact ⟨le_refl 0, by norm_num⟩
  · have hn1 : (a : ℝ) < (n : ℝ) := by
      have : a < n := lt_of_not_ge h1
      exact_mod_cast this
    have hn2 : (n : ℝ) < (b : ℝ) := by
      have : n < b := lt_of_not_ge h2
      exact_mod_cast this
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by linarith)]
      linarith

/-- **Every admissible atom is 1-bounded.** -/
theorem norm_semAtom_le_one (a : GenAtom) (ha : a.Admissible) (n : ℕ) :
    ‖semAtom a n‖ ≤ 1 := by
  cases a with
  | mobius =>
      by_cases h : Squarefree n
      · simp [semAtom, ArithmeticFunction.moebius_apply_of_squarefree h]
      · simp [semAtom, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  | constant c => exact ha
  | boxCutoff lo hi =>
      simp only [semAtom]
      split_ifs <;> simp
  | smoothWeight a b =>
      have := rampR_mem_unitInterval a b n ha
      simp only [semAtom, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg this.1]
      exact this.2
  | mellinTwist t =>
      exact norm_cpow_I_mul_le_one _ (Nat.cast_nonneg n) t
  | perfectPowerPullback k =>
      simp only [semAtom]
      split_ifs <;> simp

/-! ## 4. The abstract prime-extrema atoms — realisation interface UNINHABITED -/

/-- **Abstract generated atoms for the two-parameter `P±` twists.**  These are
data only.  `n ↦ (P⁻(n) + 1/2)^{it}` and `n ↦ P⁺(n)^{it}` cannot be realised in
this repository because `P⁻` and `P⁺` do not exist in it. -/
inductive PrimeExtremaAtom
  /-- `n ↦ (P⁻(n) + 1/2)^{it}`. -/
  | leastPrimeTwist (t : ℝ)
  /-- `n ↦ P⁺(n)^{it}`. -/
  | greatestPrimeTwist (t : ℝ)

/-- The semantic tag of an abstract prime-extrema atom. -/
def PrimeExtremaAtom.tag : PrimeExtremaAtom → AtomTag
  | .leastPrimeTwist _ => .leastPrimeTwist
  | .greatestPrimeTwist _ => .greatestPrimeTwist

/-- **The semantic realisation interface for `P±`.**

This structure is *not inhabited anywhere in this project*: the repository
contains no least/greatest prime-factor function, and v11 deliberately does not
invent one.  Every statement that needs a semantic value for a
`PrimeExtremaAtom` therefore carries an explicit `PrimeExtremaRealisation`
parameter and is unusable until such a parameter is supplied.

(No claim is made that the structure is *empty*; the claim is only that this
project supplies no inhabitant.) -/
structure PrimeExtremaRealisation where
  /-- The least prime factor. -/
  Pminus : ℕ → ℕ
  /-- The greatest prime factor. -/
  Pplus : ℕ → ℕ
  /-- `P⁻(n)` is prime for `n ≥ 2`. -/
  Pminus_prime : ∀ n, 2 ≤ n → (Pminus n).Prime
  /-- `P⁻(n)` divides `n`. -/
  Pminus_dvd : ∀ n, 2 ≤ n → Pminus n ∣ n
  /-- `P⁻(n)` is least among prime divisors. -/
  Pminus_least : ∀ n p, 2 ≤ n → p.Prime → p ∣ n → Pminus n ≤ p
  /-- `P⁺(n)` is prime for `n ≥ 2`. -/
  Pplus_prime : ∀ n, 2 ≤ n → (Pplus n).Prime
  /-- `P⁺(n)` divides `n`. -/
  Pplus_dvd : ∀ n, 2 ≤ n → Pplus n ∣ n
  /-- `P⁺(n)` is greatest among prime divisors. -/
  Pplus_greatest : ∀ n p, 2 ≤ n → p.Prime → p ∣ n → p ≤ Pplus n

/-- The semantics of the abstract prime-extrema atoms, **relative to a supplied
realisation**. -/
noncomputable def semPrimeExtremaAtom (E : PrimeExtremaRealisation) :
    PrimeExtremaAtom → ℕ → ℂ
  | .leastPrimeTwist t, n =>
      (((E.Pminus n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
  | .greatestPrimeTwist t, n => ((E.Pplus n : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))

/-- Relative to any supplied realisation the prime-extrema atoms are also
1-bounded.  (Conditional on the realisation, which this project never
supplies.) -/
theorem norm_semPrimeExtremaAtom_le_one (E : PrimeExtremaRealisation)
    (a : PrimeExtremaAtom) (n : ℕ) : ‖semPrimeExtremaAtom E a n‖ ≤ 1 := by
  cases a with
  | leastPrimeTwist t =>
      exact norm_cpow_I_mul_le_one _ (by positivity) t
  | greatestPrimeTwist t =>
      exact norm_cpow_I_mul_le_one _ (Nat.cast_nonneg _) t

/-! ## 5. Non-triviality guards -/

/-- The grammar is not degenerate: the Möbius atom is admissible and takes the
value `-1` at `2`. -/
theorem semAtom_mobius_two : semAtom .mobius 2 = -1 := by
  have h : Squarefree 2 := Nat.squarefree_two
  simp [semAtom, ArithmeticFunction.moebius_apply_of_squarefree h,
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]

/-- Two admissible atoms with different semantics exist, so the semantic map is
not constant. -/
theorem semAtom_not_constant :
    ∃ a b : GenAtom, a.Admissible ∧ b.Admissible ∧ semAtom a 2 ≠ semAtom b 2 :=
  ⟨.mobius, .constant 0, trivial, by simp [GenAtom.Admissible], by
    rw [semAtom_mobius_two]; simp [semAtom]⟩

end Gate1BV11
end TwinPrimeProject
