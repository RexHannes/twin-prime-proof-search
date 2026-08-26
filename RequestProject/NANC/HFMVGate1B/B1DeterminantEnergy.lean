import Mathlib

/-!
# HFMV Gate 1B, Module 5: the B1 determinant multiplicity and energy lemma

Abstract finite model.  `P` is a finite box of primes and `Hh` a finite box of
short nonzero integer shifts with `|h| ≤ H` and `2H < p` for every `p ∈ P`.

The determinant relation is

  `h₁ p₂ - h₂ p₁ = n p'`   (over `ℤ`).

Proved here:

* `b1_multiplicity_one`: for fixed distinct primes `p₁ ≠ p₂` and fixed `n p'`
  there is **at most one** pair `(h₁, h₂)` in the short box;
* `b1_key_injOn`: consequently the "determinant key" `(p₁, p₂, h₁p₂ - h₂p₁)`
  is injective on the admissible quadruples;
* `b1_energy`: the abstract finite energy inequality
  `Σ_key ‖α(key)‖² ≤ C · Σ_(p,h) ‖c(p,h)‖⁴` with the **explicit** finite
  constant `C = |P ×ˢ Hh|` coming from Cauchy–Schwarz.  The multiplicity factor
  is visible in the statement; nothing is hidden inside automation.
-/

namespace TwinPrimeProject
namespace HFMVGate1B

open Finset

/-! ## 1. The determinant relation and multiplicity one -/

/-- The B1 determinant relation `h₁ p₂ - h₂ p₁ = n p'`. -/
def B1Det (p₁ h₁ p₂ h₂ n p' : ℤ) : Prop := h₁ * p₂ - h₂ * p₁ = n * p'

/-- **Multiplicity one.**  For distinct primes `p₁, p₂`, short shifts
`|hᵢ| ≤ H` and the separation `2H < p₁`, the determinant value `n p'`
determines the pair `(h₁, h₂)`.  Only the bounds on the `h₁`-coordinates are
needed: the `h₂`-coordinates are then forced. -/
theorem b1_multiplicity_one {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂)
    {H h₁ h₂ h₁' h₂' n p' : ℤ}
    (hb₁ : |h₁| ≤ H) (hb₁' : |h₁'| ≤ H)
    (hsep : 2 * H < (p₁ : ℤ))
    (e : B1Det p₁ h₁ p₂ h₂ n p') (e' : B1Det p₁ h₁' p₂ h₂' n p') :
    h₁ = h₁' ∧ h₂ = h₂' := by
  unfold B1Det at e e'
  have hcop : IsCoprime (p₁ : ℤ) (p₂ : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp₁ hp₂).mpr hne)
  have hp₁pos : (0 : ℤ) < (p₁ : ℤ) := by exact_mod_cast hp₁.pos
  have key : (h₁ - h₁') * (p₂ : ℤ) = (h₂ - h₂') * (p₁ : ℤ) := by linear_combination e - e'
  have hdvd : (p₁ : ℤ) ∣ (h₁ - h₁') * (p₂ : ℤ) := by
    rw [key]; exact dvd_mul_left _ _
  have hdvd' : (p₁ : ℤ) ∣ (h₁ - h₁') := hcop.dvd_of_dvd_mul_right hdvd
  have habs : |h₁ - h₁'| < (p₁ : ℤ) := by
    obtain ⟨u₁, u₂⟩ := abs_le.mp hb₁
    obtain ⟨u₃, u₄⟩ := abs_le.mp hb₁'
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have h1 : h₁ = h₁' := by
    have := Int.eq_zero_of_abs_lt_dvd hdvd' habs
    linarith
  refine ⟨h1, ?_⟩
  have : (h₂ - h₂') * (p₁ : ℤ) = 0 := by rw [← key, h1]; ring
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hp₁pos.ne'

/-! ## 2. The determinant key and its injectivity -/

/-- The admissible box of `(prime, shift)` pairs. -/
def b1Box (P : Finset ℕ) (Hh : Finset ℤ) : Finset (ℕ × ℤ) := P ×ˢ Hh

/-- Admissible quadruples: two box elements with distinct primes. -/
def b1Quads (P : Finset ℕ) (Hh : Finset ℤ) : Finset ((ℕ × ℤ) × (ℕ × ℤ)) :=
  ((b1Box P Hh) ×ˢ (b1Box P Hh)).filter (fun x => x.1.1 ≠ x.2.1)

/-- The determinant key `(p₁, p₂, h₁ p₂ - h₂ p₁)`. -/
def b1Key (x : (ℕ × ℤ) × (ℕ × ℤ)) : ℕ × ℕ × ℤ :=
  (x.1.1, x.2.1, x.1.2 * (x.2.1 : ℤ) - x.2.2 * (x.1.1 : ℤ))

/-- **Injectivity of the determinant key** on the admissible quadruples, under
the box hypotheses: every prime in `P` is prime and exceeds `2H`, and every
shift in `Hh` is nonzero of absolute value at most `H`. -/
theorem b1_key_injOn {P : Finset ℕ} {Hh : Finset ℤ} {H : ℤ}
    (hP : ∀ p ∈ P, p.Prime ∧ 2 * H < (p : ℤ))
    (hHh : ∀ h ∈ Hh, h ≠ 0 ∧ |h| ≤ H) :
    ∀ x ∈ b1Quads P Hh, ∀ y ∈ b1Quads P Hh, b1Key x = b1Key y → x = y := by
  intro x hx y hy hkey
  simp only [b1Quads, b1Box, mem_filter, mem_product] at hx hy
  obtain ⟨⟨⟨hxp₁, hxh₁⟩, hxp₂, hxh₂⟩, hxne⟩ := hx
  obtain ⟨⟨⟨hyp₁, hyh₁⟩, hyp₂, hyh₂⟩, _⟩ := hy
  simp only [b1Key, Prod.mk.injEq] at hkey
  obtain ⟨hp₁, hp₂, hdet⟩ := hkey
  obtain ⟨hprime₁, hsep₁⟩ := hP _ hxp₁
  obtain ⟨hprime₂, _⟩ := hP _ hxp₂
  have hb₁ := (hHh _ hxh₁).2
  have hb₁' := (hHh _ hyh₁).2
  have e : B1Det x.1.1 x.1.2 x.2.1 x.2.2
      (x.1.2 * (x.2.1 : ℤ) - x.2.2 * (x.1.1 : ℤ)) 1 := by
    unfold B1Det; ring
  have e' : B1Det x.1.1 y.1.2 x.2.1 y.2.2
      (x.1.2 * (x.2.1 : ℤ) - x.2.2 * (x.1.1 : ℤ)) 1 := by
    unfold B1Det
    rw [mul_one, hdet, hp₁, hp₂]
  obtain ⟨e₁, e₂⟩ :=
    b1_multiplicity_one hprime₁ hprime₂ hxne hb₁ hb₁' hsep₁ e e'
  exact Prod.ext (Prod.ext hp₁ e₁) (Prod.ext hp₂ e₂)

/-! ## 3. The abstract finite energy inequality -/

/-- The fibre sum of the coefficient product over a fixed determinant key. -/
noncomputable def b1Alpha (P : Finset ℕ) (Hh : Finset ℤ) (c : ℕ × ℤ → ℂ)
    (k : ℕ × ℕ × ℤ) : ℂ :=
  ∑ x ∈ (b1Quads P Hh).filter (fun x => b1Key x = k), c x.1 * c x.2

/-- Each key fibre is a single quadruple, so `α` is a single product. -/
theorem b1Alpha_single {P : Finset ℕ} {Hh : Finset ℤ} {H : ℤ} {c : ℕ × ℤ → ℂ}
    (hP : ∀ p ∈ P, p.Prime ∧ 2 * H < (p : ℤ))
    (hHh : ∀ h ∈ Hh, h ≠ 0 ∧ |h| ≤ H)
    {x : (ℕ × ℤ) × (ℕ × ℤ)} (hx : x ∈ b1Quads P Hh) :
    b1Alpha P Hh c (b1Key x) = c x.1 * c x.2 := by
  unfold b1Alpha
  refine Finset.sum_eq_single_of_mem x (by simp [mem_filter, hx]) ?_
  intro y hy hyx
  exact absurd (b1_key_injOn hP hHh y (mem_filter.mp hy).1 x hx (mem_filter.mp hy).2) hyx

/-- **B1 determinant energy inequality.**  With `C = |P ×ˢ Hh|` (an explicit
finite constant depending only on the size of the box),

  `Σ_k ‖α(k)‖² ≤ C · Σ_(p,h) ‖c(p,h)‖⁴`.

The multiplicity-one lemma is what identifies the key fibres; the constant `C`
is the Cauchy–Schwarz factor and is displayed, not hidden. -/
theorem b1_energy {P : Finset ℕ} {Hh : Finset ℤ} {H : ℤ} (c : ℕ × ℤ → ℂ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 * H < (p : ℤ))
    (hHh : ∀ h ∈ Hh, h ≠ 0 ∧ |h| ≤ H) :
    ∑ k ∈ (b1Quads P Hh).image b1Key, ‖b1Alpha P Hh c k‖ ^ 2
      ≤ (b1Box P Hh).card * ∑ y ∈ b1Box P Hh, ‖c y‖ ^ 4 := by
  classical
  -- Step 1: reindex the key sum by the quadruples (the key is injective).
  have hstep1 : ∑ k ∈ (b1Quads P Hh).image b1Key, ‖b1Alpha P Hh c k‖ ^ 2
      = ∑ x ∈ b1Quads P Hh, ‖c x.1‖ ^ 2 * ‖c x.2‖ ^ 2 := by
    rw [Finset.sum_image (b1_key_injOn hP hHh)]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [b1Alpha_single hP hHh hx, norm_mul, mul_pow]
  -- Step 2: extend to the full product box.
  have hsub : b1Quads P Hh ⊆ (b1Box P Hh) ×ˢ (b1Box P Hh) := filter_subset _ _
  have hstep2 : ∑ x ∈ b1Quads P Hh, ‖c x.1‖ ^ 2 * ‖c x.2‖ ^ 2
      ≤ ∑ x ∈ (b1Box P Hh) ×ˢ (b1Box P Hh), ‖c x.1‖ ^ 2 * ‖c x.2‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
  -- Step 3: the full product sum factors.
  have hstep3 : ∑ x ∈ (b1Box P Hh) ×ˢ (b1Box P Hh), ‖c x.1‖ ^ 2 * ‖c x.2‖ ^ 2
      = (∑ y ∈ b1Box P Hh, ‖c y‖ ^ 2) ^ 2 := by
    rw [Finset.sum_product, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  -- Step 4: Cauchy–Schwarz / Chebyshev.
  have hstep4 : (∑ y ∈ b1Box P Hh, ‖c y‖ ^ 2) ^ 2
      ≤ (b1Box P Hh).card * ∑ y ∈ b1Box P Hh, (‖c y‖ ^ 2) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hpow : ∀ y : ℕ × ℤ, (‖c y‖ ^ 2) ^ 2 = ‖c y‖ ^ 4 := by
    intro y; ring
  calc ∑ k ∈ (b1Quads P Hh).image b1Key, ‖b1Alpha P Hh c k‖ ^ 2
      = ∑ x ∈ b1Quads P Hh, ‖c x.1‖ ^ 2 * ‖c x.2‖ ^ 2 := hstep1
    _ ≤ ∑ x ∈ (b1Box P Hh) ×ˢ (b1Box P Hh), ‖c x.1‖ ^ 2 * ‖c x.2‖ ^ 2 := hstep2
    _ = (∑ y ∈ b1Box P Hh, ‖c y‖ ^ 2) ^ 2 := hstep3
    _ ≤ (b1Box P Hh).card * ∑ y ∈ b1Box P Hh, (‖c y‖ ^ 2) ^ 2 := hstep4
    _ = (b1Box P Hh).card * ∑ y ∈ b1Box P Hh, ‖c y‖ ^ 4 := by
        simp only [hpow]

end HFMVGate1B
end TwinPrimeProject
