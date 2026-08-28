import Mathlib
import Gate1B.SafeAlgebra.RamanujanUnitBaseline

/-!
# V10 · Gate 1B — the canonical zero mode, reproved from Mathlib orthogonality

This module **reproves** (it does not assume) the finite Fourier facts behind the
canonical unit main term.

* `stdCharSystem` inhabits the project's existing hypothesis-carrying interface
  `Gate1B.SafeAlgebra.AdditiveCharacterSystem q` using Mathlib's
  `ZMod.stdAddChar`.  Additivity, unimodularity, conjugation and **orthogonality**
  are all *derived* from Mathlib (`AddChar.sum_mulShift`,
  `ZMod.isPrimitive_stdAddChar`); nothing is postulated.
* `unit_indicator_baseline_std` is therefore the unconditional form of the
  required identity

      1_{(n,q)=1}/φ(q) = 1/q + 1/(q φ(q)) ∑_{a ≠ 0} c_q(-a) e_q(a n).

* `canonical_discrepancy_has_zero_additive_mean` : for a weight supported on the
  units, the discrepancy against the canonical unit main term

      M_q(n) = 1_{unit}(n) · (1/φ(q)) ∑_{u unit} c(u)

  has vanishing `a = 0` additive Fourier coefficient.
* `canonical_discrepancy_eq_nonzero_frequencies` : consequently the discrepancy is
  a combination of **purely nonzero** additive frequencies.
* `zero_mean_fails_for_arbitrary_expected_term` : the test theorem.  Replacing the
  canonical unit main term by an arbitrary `E` destroys the conclusion.

Nothing here is analytic and nothing here is an axiom.
-/

namespace TwinPrimeProject
namespace Gate1BV10

open Finset Gate1B.SafeAlgebra

/-! ## 1. The standard additive character system, orthogonality proved -/

/-- The additive character `e_q(x)` supplied by Mathlib. -/
noncomputable def echar (q : ℕ) [NeZero q] (x : ZMod q) : ℂ := ZMod.stdAddChar x

/-- **Orthogonality, proved** (not assumed): `∑_{a mod q} e_q(a x) = q · 1_{x = 0}`. -/
theorem sum_echar (q : ℕ) [NeZero q] (x : ZMod q) :
    ∑ a : ZMod q, echar q (a * x) = if x = 0 then (q : ℂ) else 0 := by
  classical
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar (N := q))) x
    (ZMod.isPrimitive_stdAddChar q)
  simp only [echar]
  rw [h]
  by_cases hx : x = 0 <;> simp [hx, ZMod.card]

/-- **The project's `AdditiveCharacterSystem` interface, inhabited from Mathlib.**
Every field — in particular orthogonality — is proved. -/
noncomputable def stdCharSystem (q : ℕ) [NeZero q] : AdditiveCharacterSystem q where
  chi := echar q
  add := by intro x y; simp [echar, AddChar.map_add_eq_mul]
  norm_one := by intro x; exact AddChar.norm_apply _ x
  conj_eq := by
    intro x
    have h1 : ‖ZMod.stdAddChar x‖ = 1 := AddChar.norm_apply _ x
    simp only [echar]
    rw [← Complex.inv_eq_conj h1, ← AddChar.map_neg_eq_inv]
  orthogonality := sum_echar q

@[simp] theorem stdCharSystem_chi (q : ℕ) [NeZero q] (x : ZMod q) :
    (stdCharSystem q).chi x = echar q x := rfl

@[simp] theorem echar_zero (q : ℕ) [NeZero q] : echar q 0 = 1 :=
  (stdCharSystem q).chi_zero

/-- The number of units, `φ(q)`, is nonzero. -/
theorem card_units_ne_zero (q : ℕ) [NeZero q] : ((Fintype.card (ZMod q)ˣ : ℂ)) ≠ 0 := by
  have : Fintype.card (ZMod q)ˣ ≠ 0 := Fintype.card_ne_zero
  exact_mod_cast this

/-- **The required Ramanujan / unit-baseline identity, unconditional.**

`1_{unit}(n)/φ(q) = 1/q + 1/(q φ(q)) ∑_{a ≠ 0} c_q(-a) e_q(a n)`. -/
theorem unit_indicator_baseline_std (q : ℕ) [NeZero q] (n : ZMod q) :
    (if IsUnit n then (1 : ℂ) else 0) / (Fintype.card (ZMod q)ˣ)
      = 1 / q + (1 / ((q : ℂ) * (Fintype.card (ZMod q)ˣ))) *
          ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0,
            (stdCharSystem q).ramanujan (-a) * (stdCharSystem q).chi (a * n) :=
  (stdCharSystem q).unit_indicator_baseline n (card_units_ne_zero q)

/-! ## 2. Additive Fourier coefficients -/

variable {q : ℕ} [NeZero q]

/-- The additive Fourier coefficient `ĝ(a) = ∑_n g(n) e_q(-a n)`. -/
noncomputable def fourierCoeff (g : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  ∑ n : ZMod q, g n * echar q (-(a * n))

/-- The `a = 0` coefficient is the plain sum. -/
theorem fourierCoeff_zero (g : ZMod q → ℂ) : fourierCoeff g 0 = ∑ n : ZMod q, g n := by
  simp [fourierCoeff]

/-- **Fourier inversion** over `ZMod q`, from orthogonality. -/
theorem fourier_inversion (g : ZMod q → ℂ) (n : ZMod q) :
    g n = (1 / (q : ℂ)) * ∑ a : ZMod q, fourierCoeff g a * echar q (a * n) := by
  classical
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hstep : ∀ a : ZMod q, fourierCoeff g a * echar q (a * n)
      = ∑ m : ZMod q, g m * echar q (a * (n - m)) := by
    intro a
    rw [fourierCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have := (stdCharSystem q).add (-(a * m)) (a * n)
    simp only [stdCharSystem_chi] at this
    calc g m * echar q (-(a * m)) * echar q (a * n)
        = g m * (echar q (-(a * m)) * echar q (a * n)) := by ring
      _ = g m * echar q (-(a * m) + a * n) := by rw [this]
      _ = g m * echar q (a * (n - m)) := by ring_nf
  symm
  calc (1 / (q : ℂ)) * ∑ a : ZMod q, fourierCoeff g a * echar q (a * n)
      = (1 / (q : ℂ)) * ∑ a : ZMod q, ∑ m : ZMod q, g m * echar q (a * (n - m)) := by
        rw [Finset.sum_congr rfl fun a _ => hstep a]
    _ = (1 / (q : ℂ)) * ∑ m : ZMod q, g m * ∑ a : ZMod q, echar q (a * (n - m)) := by
        rw [Finset.sum_comm]
        exact congrArg _ (Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum])
    _ = (1 / (q : ℂ)) * ∑ m : ZMod q, g m * (if n - m = 0 then (q : ℂ) else 0) := by
        exact congrArg _ (Finset.sum_congr rfl fun m _ => by rw [sum_echar q (n - m)])
    _ = g n := by
        rw [Finset.sum_eq_single n]
        · simp; field_simp
        · intro m _ hm
          rw [if_neg (by intro h; exact hm (by linear_combination -h)), mul_zero]
        · intro h; exact absurd (Finset.mem_univ n) h

/-! ## 3. The canonical unit main term and its discrepancy -/

/-- Summing a unit-supported weight over `ZMod q` is summing over the units. -/
theorem sum_ite_isUnit (h : ZMod q → ℂ) :
    ∑ n : ZMod q, (if IsUnit n then h n else 0) = ∑ u : (ZMod q)ˣ, h (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter]
  refine (Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q)) ?_ ?_ ?_ ?_).symm
  · intro u _; simp [Finset.mem_filter]
  · intro u _ v _ huv; exact Units.ext huv
  · intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨u, rfl⟩ := hn.2
    exact ⟨u, Finset.mem_univ u, rfl⟩
  · intro u _; rfl

/-- The canonical unit main term
`M_q(n) = 1_{unit}(n) · (1/φ(q)) ∑_{u unit} c(u)`. -/
noncomputable def canonicalMain (c : ZMod q → ℂ) (n : ZMod q) : ℂ :=
  (if IsUnit n then (1 : ℂ) else 0) *
    ((∑ u : (ZMod q)ˣ, c (u : ZMod q)) / (Fintype.card (ZMod q)ˣ))

/-- The canonical discrepancy `C_q − M_q`. -/
noncomputable def canonicalDiscrepancy (c : ZMod q → ℂ) (n : ZMod q) : ℂ :=
  c n - canonicalMain c n

/-- **CANONICAL ZERO MODE.**  For a weight supported on the units, the `a = 0`
additive Fourier coefficient of the canonical discrepancy vanishes. -/
theorem canonical_discrepancy_has_zero_additive_mean (c : ZMod q → ℂ)
    (hsupp : ∀ n : ZMod q, ¬ IsUnit n → c n = 0) :
    fourierCoeff (canonicalDiscrepancy c) 0 = 0 := by
  classical
  have hphi : ((Fintype.card (ZMod q)ˣ : ℂ)) ≠ 0 := card_units_ne_zero q
  have hc : ∀ n : ZMod q, c n = (if IsUnit n then c n else 0) := by
    intro n; by_cases h : IsUnit n
    · simp [h]
    · simp [h, hsupp n h]
  have h1 : ∑ n : ZMod q, c n = ∑ u : (ZMod q)ˣ, c (u : ZMod q) := by
    rw [Finset.sum_congr rfl fun n _ => hc n]
    exact sum_ite_isUnit c
  have h2 : ∑ n : ZMod q, canonicalMain c n = ∑ u : (ZMod q)ˣ, c (u : ZMod q) := by
    have := sum_ite_isUnit (q := q)
      (fun _ => (∑ u : (ZMod q)ˣ, c (u : ZMod q)) / (Fintype.card (ZMod q)ˣ))
    simp only [canonicalMain]
    rw [Finset.sum_congr rfl fun n _ => (by by_cases h : IsUnit n <;> simp [h] :
      (if IsUnit n then (1 : ℂ) else 0) *
          ((∑ u : (ZMod q)ˣ, c (u : ZMod q)) / (Fintype.card (ZMod q)ˣ))
        = if IsUnit n then (∑ u : (ZMod q)ˣ, c (u : ZMod q)) / (Fintype.card (ZMod q)ˣ)
          else 0)]
    rw [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [fourierCoeff_zero]
  simp only [canonicalDiscrepancy, Finset.sum_sub_distrib, h1, h2, sub_self]

/-- **Pure nonzero frequencies.**  The canonical discrepancy is a combination of
additive frequencies `a ≠ 0` only. -/
theorem canonical_discrepancy_eq_nonzero_frequencies (c : ZMod q → ℂ)
    (hsupp : ∀ n : ZMod q, ¬ IsUnit n → c n = 0) (n : ZMod q) :
    canonicalDiscrepancy c n
      = (1 / (q : ℂ)) * ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          fourierCoeff (canonicalDiscrepancy c) a * echar q (a * n) := by
  classical
  have hz := canonical_discrepancy_has_zero_additive_mean c hsupp
  have hsplit : ∑ a : ZMod q, fourierCoeff (canonicalDiscrepancy c) a * echar q (a * n)
      = ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          fourierCoeff (canonicalDiscrepancy c) a * echar q (a * n) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), hz]
    ring
  rw [fourier_inversion (canonicalDiscrepancy c) n, hsplit]

/-! ## 4. Test theorem: the canonical main term is load bearing -/

/-- **TEST / COUNTERGUARD.**  If the canonical unit main term is replaced by an
arbitrary expected function `E`, the zero additive mode does **not** vanish in
general: here `c = 0`, `E = 1`, and the `a = 0` coefficient equals `−q ≠ 0`. -/
theorem zero_mean_fails_for_arbitrary_expected_term (q : ℕ) [NeZero q] :
    fourierCoeff (fun _ : ZMod q => (0 : ℂ) - 1) 0 = -(q : ℂ) ∧ (-(q : ℂ)) ≠ 0 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  constructor
  · rw [fourierCoeff_zero]
    simp [Finset.sum_const, ZMod.card]
  · simpa using hq

end Gate1BV10
end TwinPrimeProject
