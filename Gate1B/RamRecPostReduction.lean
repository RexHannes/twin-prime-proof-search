import Mathlib
import RequestProject.CurrentProgramme.StatusTypes
import RequestProject.CurrentProgramme.AddMinRamanujanReciprocity

/-!
# Gate 1B · Post-Ramanujan exact algebra bank (append-only)

**Phase A of the C4Shift consolidation.**  This module is *append-only*: it adds
new exact finite algebra on top of the banked Ramanujan-reciprocal layer
(`AddMinRamanujanReciprocity`) and modifies nothing historical.

Everything below is **Class A** in the sense of the consolidation policy: exact
finite algebra, modular arithmetic, additive characters, finite Cauchy–Schwarz
with every hypothesis printed.  There is **no analytic estimate**, no
`sorry`/`axiom`/`native_decide`, and no negative-log saving is encoded anywhere.

## Contents

1. **Divisor–cofactor split.**  `N = r n`, `gcd(N,M) = 1` implies
   `gcd(r,M) = gcd(n,M) = 1` and, in `ZMod M`, `N⁻¹ = r⁻¹ n⁻¹`
   (`inverse_N_eq_inverse_r_mul_inverse_n_mod_M`).  **No `gcd(r,n) = 1` is
   assumed.**
2. **Reciprocal phase.**  `Phi m r n x` is built from the repository's additive
   character `ezExp`, together with its rational phase `phaseQ` and the exact
   dictionary `phaseChar_eq_exp` / `phaseChar_eq_iff`.
3. **Phase collision classification.**  A collision of two reciprocal phases
   forces `r₁ = r₂`, `x₁ ≡ x₂ (mod r₁)` and `m₁ n₂ ≡ m₂ n₁ (mod M)`; the ratio
   coordinate `lambda = m n⁻¹ mod M` is therefore a collision invariant.  **No
   analytic spacing estimate is imported.**
4. **Fixed-`M` ratio-fibre Cauchy** at natural scale: `∑_λ |∑_{fibre} b|² ≤
   T ∑ |b|²`, from explicit finite-support hypotheses.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace RamRecPostReduction

open Finset FiniteLiftLocalTwist AddMinRamanujan

/-! ## 1. The divisor–cofactor split -/

/-- If `N = r n` is coprime to `M`, so is the divisor `r`. -/
theorem coprime_divisor_of_coprime_mul {r n M : ℕ} (h : Nat.Coprime (r * n) M) :
    Nat.Coprime r M :=
  Nat.Coprime.coprime_dvd_left (Dvd.intro n rfl) h

/-- If `N = r n` is coprime to `M`, so is the cofactor `n`. -/
theorem coprime_cofactor_of_coprime_mul {r n M : ℕ} (h : Nat.Coprime (r * n) M) :
    Nat.Coprime n M :=
  Nat.Coprime.coprime_dvd_left (Dvd.intro_left r rfl) h

/-- Inverses of units multiply in `ZMod M` (no primality, no `gcd(a,b) = 1`). -/
theorem zmod_inv_mul {M : ℕ} {a b : ZMod M} (ha : IsUnit a) (hb : IsUnit b) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  have hab : IsUnit (a * b) := ha.mul hb
  have h1 : (a * b) * (a⁻¹ * b⁻¹) = 1 := by
    calc (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
      _ = 1 := by rw [ZMod.mul_inv_of_unit a ha, ZMod.mul_inv_of_unit b hb]; ring
  calc (a * b)⁻¹ = (a * b)⁻¹ * ((a * b) * (a⁻¹ * b⁻¹)) := by rw [h1, mul_one]
    _ = ((a * b)⁻¹ * (a * b)) * (a⁻¹ * b⁻¹) := by ring
    _ = a⁻¹ * b⁻¹ := by rw [ZMod.inv_mul_of_unit _ hab, one_mul]

/-- **Divisor–cofactor inverse split.**  For `N = r n` with `gcd(N, M) = 1`,

`N⁻¹ = r⁻¹ · n⁻¹` in `ZMod M`.

`gcd(r, n) = 1` is *not* assumed. -/
theorem inverse_N_eq_inverse_r_mul_inverse_n_mod_M
    (M r n N : ℕ) [NeZero M] (hN : N = r * n) (hcop : Nat.Coprime N M) :
    ((N : ℕ) : ZMod M)⁻¹ = ((r : ℕ) : ZMod M)⁻¹ * ((n : ℕ) : ZMod M)⁻¹ := by
  subst hN
  have hr : IsUnit ((r : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime r M).2 (coprime_divisor_of_coprime_mul hcop)
  have hn : IsUnit ((n : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime n M).2 (coprime_cofactor_of_coprime_mul hcop)
  rw [Nat.cast_mul]
  exact zmod_inv_mul hr hn

/-! ## 2. The reciprocal phase -/

/-- The rational phase `a/M + b/rRam` (Lean's `_/0 = 0` convention is *the same*
convention as the one used by `ezExp`, see `phaseChar_eq_exp`). -/
def phaseQ (M rRam : ℕ) (a b : ℤ) : ℚ := (a : ℚ) / M + (b : ℚ) / rRam

/-- The additive character attached to a rational phase, in the repository's
`ezExp` notation: `e_M(a) · e_{rRam}(b)`. -/
noncomputable def phaseChar (M rRam : ℕ) (a b : ℤ) : ℂ := ezExp M a * ezExp rRam b

/-- **The reciprocal phase.**

`Phi(m, r, n, x) = e_M(m · r⁻¹ · n⁻¹) · e_{rRam}(x ℓ)`,

i.e. the phase `m r⁻¹ n⁻¹ / M + x ℓ / rRam` of the banked reciprocal normal
form, written in the repository's additive-character type rather than as an
informal real fraction. -/
noncomputable def Phi (M rRam : ℕ) (m invr invn x ell : ℤ) : ℂ :=
  phaseChar M rRam (m * invr * invn) (x * ell)

/-- **Post-reduction of the reciprocal phase.**  If `N⁻¹ ≡ r⁻¹ n⁻¹ (mod M)` then
the banked phase `e_M(m N⁻¹) e_{rRam}(xℓ)` *is* `Phi(m, r, n, x)`. -/
theorem phase_post_reduction (M rRam : ℕ) (m invN invr invn x ell : ℤ)
    (h : (M : ℤ) ∣ (invN - invr * invn)) :
    ezExp M (m * invN) * ezExp rRam (x * ell) = Phi M rRam m invr invn x ell := by
  unfold Phi phaseChar
  congr 1
  refine ezExp_congr M ?_
  obtain ⟨c, hc⟩ := h
  exact ⟨m * c, by linear_combination m * hc⟩

/-- The character is the exponential of its rational phase.  This is an exact
dictionary, valid also in the degenerate cases `M = 0` or `rRam = 0`. -/
theorem phaseChar_eq_exp (M rRam : ℕ) (a b : ℤ) :
    phaseChar M rRam a b
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((phaseQ M rRam a b : ℚ) : ℂ)) := by
  unfold phaseChar ezExp phaseQ
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Character equality is phase equality modulo one.**  Exact, no estimate. -/
theorem phaseChar_eq_iff (M₁ r₁ M₂ r₂ : ℕ) (a₁ b₁ a₂ b₂ : ℤ) :
    phaseChar M₁ r₁ a₁ b₁ = phaseChar M₂ r₂ a₂ b₂ ↔
      ∃ k : ℤ, phaseQ M₁ r₁ a₁ b₁ - phaseQ M₂ r₂ a₂ b₂ = (k : ℚ) := by
  rw [phaseChar_eq_exp, phaseChar_eq_exp, Complex.exp_eq_exp_iff_exists_int]
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h' : (2 * (Real.pi : ℂ) * Complex.I) * ((phaseQ M₁ r₁ a₁ b₁ : ℚ) : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * (((phaseQ M₂ r₂ a₂ b₂ : ℚ) : ℂ) + (k : ℂ)) := by
      linear_combination hk
    have h'' := mul_left_cancel₀ hne h'
    have hc : ((phaseQ M₁ r₁ a₁ b₁ - phaseQ M₂ r₂ a₂ b₂ : ℚ) : ℂ) = ((k : ℚ) : ℂ) := by
      push_cast
      linear_combination h''
    exact_mod_cast hc
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hc : ((phaseQ M₁ r₁ a₁ b₁ : ℚ) : ℂ) - ((phaseQ M₂ r₂ a₂ b₂ : ℚ) : ℂ) = (k : ℂ) := by
      have := congrArg (fun q : ℚ => (q : ℂ)) hk
      push_cast at this
      linear_combination this
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hc

/-! ## 3. Phase collision classification -/

/-- The integral form of a phase collision: clearing denominators. -/
theorem collision_integral_form {M r₁ r₂ : ℕ} (hM : 0 < M) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    {a₁ b₁ a₂ b₂ : ℤ}
    (h : ∃ k : ℤ, phaseQ M r₁ a₁ b₁ - phaseQ M r₂ a₂ b₂ = (k : ℚ)) :
    ((M : ℤ) * r₁ * r₂) ∣ ((a₁ - a₂) * r₁ * r₂ + b₁ * M * r₂ - b₂ * M * r₁) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have h1' : (r₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h₁.ne'
  have h2' : (r₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h₂.ne'
  have : ((a₁ - a₂) * r₁ * r₂ + b₁ * M * r₂ - b₂ * M * r₁ : ℚ)
      = ((M : ℚ) * r₁ * r₂) * k := by
    unfold phaseQ at hk
    field_simp at hk
    linarith [hk]
  exact_mod_cast this

/-- **Collision forces equal denominators.**

If the two reciprocal phases collide, and each twist numerator is coprime to its
own denominator while both denominators are coprime to `M`, then `r₁ = r₂`. -/
theorem collision_denominators_eq {M r₁ r₂ : ℕ} (hM : 0 < M) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    {a₁ b₁ a₂ b₂ : ℤ}
    (hc₁ : IsCoprime b₁ (r₁ : ℤ)) (hc₂ : IsCoprime b₂ (r₂ : ℤ))
    (hM₁ : IsCoprime (M : ℤ) (r₁ : ℤ)) (hM₂ : IsCoprime (M : ℤ) (r₂ : ℤ))
    (h : ∃ k : ℤ, phaseQ M r₁ a₁ b₁ - phaseQ M r₂ a₂ b₂ = (k : ℚ)) :
    r₁ = r₂ := by
  have hdvd := collision_integral_form hM h₁ h₂ h
  -- `r₁ ∣ b₁ M r₂`
  have e₁ : (r₁ : ℤ) ∣ b₁ * M * r₂ := by
    have hr₁ : (r₁ : ℤ) ∣ ((a₁ - a₂) * r₁ * r₂ + b₁ * M * r₂ - b₂ * M * r₁) :=
      dvd_trans ⟨(M : ℤ) * r₂, by ring⟩ hdvd
    have h₀ : (r₁ : ℤ) ∣ ((a₁ - a₂) * r₁ * r₂ - b₂ * M * r₁) := ⟨(a₁ - a₂) * r₂ - b₂ * M, by ring⟩
    have := dvd_sub hr₁ h₀
    simpa using (by simpa using this : (r₁ : ℤ) ∣ b₁ * M * r₂)
  have e₂ : (r₂ : ℤ) ∣ b₂ * M * r₁ := by
    have hr₂ : (r₂ : ℤ) ∣ ((a₁ - a₂) * r₁ * r₂ + b₁ * M * r₂ - b₂ * M * r₁) :=
      dvd_trans ⟨(M : ℤ) * r₁, by ring⟩ hdvd
    have h₀ : (r₂ : ℤ) ∣ ((a₁ - a₂) * r₁ * r₂ + b₁ * M * r₂) := ⟨(a₁ - a₂) * r₁ + b₁ * M, by ring⟩
    have := dvd_sub h₀ hr₂
    simpa using (by simpa using this : (r₂ : ℤ) ∣ b₂ * M * r₁)
  have d₁ : (r₁ : ℤ) ∣ (r₂ : ℤ) := by
    have h' : (r₁ : ℤ) ∣ (b₁ * M) * r₂ := by simpa [mul_assoc] using e₁
    have hcop : IsCoprime (r₁ : ℤ) (b₁ * M) := (hc₁.symm).mul_right hM₁.symm
    exact hcop.dvd_of_dvd_mul_left h'
  have d₂ : (r₂ : ℤ) ∣ (r₁ : ℤ) := by
    have h' : (r₂ : ℤ) ∣ (b₂ * M) * r₁ := by simpa [mul_assoc] using e₂
    have hcop : IsCoprime (r₂ : ℤ) (b₂ * M) := (hc₂.symm).mul_right hM₂.symm
    exact hcop.dvd_of_dvd_mul_left h'
  have : (r₁ : ℤ) = (r₂ : ℤ) := Int.dvd_antisymm (by positivity) (by positivity) d₁ d₂
  exact_mod_cast this

/-- **Collision at equal denominators: the two residual congruences.** -/
theorem collision_residual_congruences {M rRam : ℕ} (hM : 0 < M) (hr : 0 < rRam)
    {a₁ b₁ a₂ b₂ : ℤ}
    (hMr : IsCoprime (M : ℤ) (rRam : ℤ))
    (h : ∃ k : ℤ, phaseQ M rRam a₁ b₁ - phaseQ M rRam a₂ b₂ = (k : ℚ)) :
    (rRam : ℤ) ∣ (b₁ - b₂) ∧ (M : ℤ) ∣ (a₁ - a₂) := by
  obtain ⟨k, hk⟩ := h
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hr' : (rRam : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have key : ((a₁ - a₂) * rRam + (b₁ - b₂) * M : ℤ) = ((M : ℤ) * rRam) * k := by
    have : ((a₁ - a₂) * rRam + (b₁ - b₂) * M : ℚ) = ((M : ℚ) * rRam) * k := by
      unfold phaseQ at hk
      field_simp at hk
      linarith [hk]
    exact_mod_cast this
  constructor
  · have hd : (rRam : ℤ) ∣ (b₁ - b₂) * M := ⟨(M : ℤ) * k - (a₁ - a₂), by linarith [key]⟩
    exact (hMr.symm).dvd_of_dvd_mul_right hd
  · have hd : (M : ℤ) ∣ (a₁ - a₂) * rRam := ⟨(rRam : ℤ) * k - (b₁ - b₂), by linarith [key]⟩
    exact hMr.dvd_of_dvd_mul_right hd

/-- **Twist collision.**  With `gcd(ℓ, rRam) = 1`, `x₁ ℓ ≡ x₂ ℓ` forces
`x₁ ≡ x₂ (mod rRam)`. -/
theorem collision_twist_congr {rRam : ℕ} {x₁ x₂ ell : ℤ}
    (hell : IsCoprime ell (rRam : ℤ))
    (h : (rRam : ℤ) ∣ (x₁ * ell - x₂ * ell)) :
    (rRam : ℤ) ∣ (x₁ - x₂) := by
  have h' : (rRam : ℤ) ∣ (x₁ - x₂) * ell := by
    have : (x₁ - x₂) * ell = x₁ * ell - x₂ * ell := by ring
    rwa [this]
  exact (hell.symm).dvd_of_dvd_mul_right h'

/-- **Ratio collision.**  The numerator congruence `m₁ r⁻¹ n₁⁻¹ ≡ m₂ r⁻¹ n₂⁻¹`
becomes the *ratio* congruence `m₁ n₂ ≡ m₂ n₁ (mod M)`. -/
theorem collision_ratio_congruence {M : ℕ} {m₁ m₂ n₁ n₂ invr invn₁ invn₂ r : ZMod M}
    (hr : invr * r = 1) (h₁ : invn₁ * n₁ = 1) (h₂ : invn₂ * n₂ = 1)
    (h : m₁ * invr * invn₁ = m₂ * invr * invn₂) :
    m₁ * n₂ = m₂ * n₁ := by
  have h4 : m₁ * invn₁ = m₂ * invn₂ := by
    linear_combination r * h - (m₁ * invn₁ - m₂ * invn₂) * hr
  linear_combination (n₁ * n₂) * h4 - m₁ * n₂ * h₁ + m₂ * n₁ * h₂

/-- **The structured ratio coordinate** `lambda = m n⁻¹ (mod M)`. -/
def ratioCoord (M : ℕ) (m invn : ℤ) : ZMod M := (m : ZMod M) * (invn : ZMod M)

/-- The ratio coordinate is a collision invariant: `m₁ n₂ ≡ m₂ n₁` and units
`n₁, n₂` give `lambda₁ = lambda₂`. -/
theorem ratioCoord_eq_of_ratio_congruence {M : ℕ} {m₁ m₂ n₁ n₂ invn₁ invn₂ : ZMod M}
    (h₁ : invn₁ * n₁ = 1) (h₂ : invn₂ * n₂ = 1) (h : m₁ * n₂ = m₂ * n₁) :
    m₁ * invn₁ = m₂ * invn₂ := by
  linear_combination (invn₁ * invn₂) * h + (m₂ * invn₂) * h₁ - (m₁ * invn₁) * h₂

/-- **Phase collision classification (assembled).**

If two reciprocal phases collide, then the denominators agree, the twists agree
modulo the denominator, and the ratio coordinates agree. -/
theorem phase_collision_classification
    {M r₁ r₂ : ℕ} (hM : 0 < M) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    {m₁ m₂ n₁ n₂ invr invn₁ invn₂ x₁ x₂ ell : ℤ}
    (hc₁ : IsCoprime (x₁ * ell) (r₁ : ℤ)) (hc₂ : IsCoprime (x₂ * ell) (r₂ : ℤ))
    (hM₁ : IsCoprime (M : ℤ) (r₁ : ℤ)) (hM₂ : IsCoprime (M : ℤ) (r₂ : ℤ))
    (hell : IsCoprime ell (r₁ : ℤ))
    (hinvr : ((invr : ZMod M)) * ((r₁ : ℤ) : ZMod M) = 1)
    (hn₁ : ((invn₁ : ZMod M)) * ((n₁ : ℤ) : ZMod M) = 1)
    (hn₂ : ((invn₂ : ZMod M)) * ((n₂ : ℤ) : ZMod M) = 1)
    (hcol : Phi M r₁ m₁ invr invn₁ x₁ ell = Phi M r₂ m₂ invr invn₂ x₂ ell) :
    r₁ = r₂ ∧ (r₁ : ℤ) ∣ (x₁ - x₂) ∧ (M : ℤ) ∣ (m₁ * n₂ - m₂ * n₁) := by
  have hq : ∃ k : ℤ,
      phaseQ M r₁ (m₁ * invr * invn₁) (x₁ * ell)
        - phaseQ M r₂ (m₂ * invr * invn₂) (x₂ * ell) = (k : ℚ) :=
    (phaseChar_eq_iff M r₁ M r₂ _ _ _ _).1 hcol
  have hreq : r₁ = r₂ := collision_denominators_eq hM h₁ h₂ hc₁ hc₂ hM₁ hM₂ hq
  subst hreq
  obtain ⟨hb, ha⟩ := collision_residual_congruences hM h₁ hM₁ hq
  refine ⟨rfl, collision_twist_congr hell hb, ?_⟩
  have hazm : ((m₁ * invr * invn₁ : ℤ) : ZMod M) = ((m₂ * invr * invn₂ : ℤ) : ZMod M) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (m₁ * invr * invn₁ - m₂ * invr * invn₂) M).2
      (by simpa using ha)
    push_cast at this ⊢
    linear_combination this
  have := collision_ratio_congruence (M := M)
      (m₁ := ((m₁ : ℤ) : ZMod M)) (m₂ := ((m₂ : ℤ) : ZMod M))
      (n₁ := ((n₁ : ℤ) : ZMod M)) (n₂ := ((n₂ : ℤ) : ZMod M))
      (invr := ((invr : ℤ) : ZMod M))
      (invn₁ := ((invn₁ : ℤ) : ZMod M)) (invn₂ := ((invn₂ : ℤ) : ZMod M))
      (r := ((r₁ : ℤ) : ZMod M)) hinvr hn₁ hn₂ (by push_cast at hazm ⊢; linear_combination hazm)
  have : ((m₁ * n₂ - m₂ * n₁ : ℤ) : ZMod M) = 0 := by push_cast; linear_combination this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 this

/-! ## 4. Fixed-`M` ratio-fibre Cauchy (natural scale only) -/

section RatioFibre

variable {M T : ℕ}

/-- The ratio fibre of `lambda` inside a finite support `S` of pairs `(m, n)`. -/
def fibre (M : ℕ) (S : Finset (ℕ × ℕ)) (lam : ZMod M) : Finset (ℕ × ℕ) :=
  S.filter (fun p => ((p.1 : ℕ) : ZMod M) = lam * ((p.2 : ℕ) : ZMod M))

/-- Every point of the support lies in exactly one ratio fibre, provided its
`n`-coordinate is invertible mod `M`. -/
theorem fibre_unique {S : Finset (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ S)
    (hu : IsUnit ((p.2 : ℕ) : ZMod M)) :
    ∃! lam : ZMod M, p ∈ fibre M S lam := by
  classical
  obtain ⟨v, hv⟩ := hu
  refine ⟨((p.1 : ℕ) : ZMod M) * (↑v⁻¹ : ZMod M), ?_, ?_⟩
  · refine Finset.mem_filter.2 ⟨hp, ?_⟩
    rw [← hv]
    simp [mul_assoc]
  · intro lam hlam
    have h := (Finset.mem_filter.1 hlam).2
    rw [h, ← hv]
    simp [mul_assoc]

/-- **Fibre cardinality from injectivity of the `n`-coordinate.**  If the second
coordinate is injective on the fibre and always lies in `[1, T]`, then the fibre
has at most `T` elements. -/
theorem fibre_card_le (S : Finset (ℕ × ℕ)) (lam : ZMod M)
    (hrange : ∀ p ∈ S, 1 ≤ p.2 ∧ p.2 ≤ T)
    (hinj : ∀ p ∈ fibre M S lam, ∀ p' ∈ fibre M S lam, p.2 = p'.2 → p = p') :
    (fibre M S lam).card ≤ T := by
  classical
  have hsub : (fibre M S lam).card ≤ (Finset.Icc 1 T).card := by
    refine Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_
    · intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.1 hp).1
      exact Finset.mem_Icc.2 (hrange p hpS)
    · intro p hp p' hp' h
      exact hinj p hp p' hp' h
  simpa using hsub

/-- **Fixed-`M` ratio-fibre Cauchy at natural scale.**

`∑_{lambda} |∑_{fibre} b|² ≤ T · ∑ |b|²`.

All hypotheses are explicit and finite: the support `S` is a `Finset`, each
`n`-coordinate is a unit mod `M` (so the fibres partition `S`), and each fibre
has at most `T` elements.  **This is only the natural-scale bound; no log saving
is encoded.** -/
theorem ratio_fibre_cauchy [NeZero M] (S : Finset (ℕ × ℕ)) (b : ℕ × ℕ → ℂ)
    (hunit : ∀ p ∈ S, IsUnit ((p.2 : ℕ) : ZMod M))
    (hcard : ∀ lam : ZMod M, (fibre M S lam).card ≤ T) :
    ∑ lam : ZMod M, ‖∑ p ∈ fibre M S lam, b p‖ ^ 2
      ≤ (T : ℝ) * ∑ p ∈ S, ‖b p‖ ^ 2 := by
  classical
  have step : ∀ lam : ZMod M,
      ‖∑ p ∈ fibre M S lam, b p‖ ^ 2 ≤ (T : ℝ) * ∑ p ∈ fibre M S lam, ‖b p‖ ^ 2 := by
    intro lam
    have h1 : ‖∑ p ∈ fibre M S lam, b p‖ ≤ ∑ p ∈ fibre M S lam, ‖b p‖ :=
      norm_sum_le _ _
    have h2 : (∑ p ∈ fibre M S lam, ‖b p‖) ^ 2
        ≤ ((fibre M S lam).card : ℝ) * ∑ p ∈ fibre M S lam, ‖b p‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖∑ p ∈ fibre M S lam, b p‖ ^ 2 ≤ (∑ p ∈ fibre M S lam, ‖b p‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ p ∈ fibre M S lam, b p), h1]
    refine h3.trans (h2.trans ?_)
    have hc : ((fibre M S lam).card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hcard lam
    have hnn : (0 : ℝ) ≤ ∑ p ∈ fibre M S lam, ‖b p‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    exact mul_le_mul_of_nonneg_right hc hnn
  calc ∑ lam : ZMod M, ‖∑ p ∈ fibre M S lam, b p‖ ^ 2
      ≤ ∑ lam : ZMod M, (T : ℝ) * ∑ p ∈ fibre M S lam, ‖b p‖ ^ 2 :=
        Finset.sum_le_sum fun lam _ => step lam
    _ = (T : ℝ) * ∑ lam : ZMod M, ∑ p ∈ fibre M S lam, ‖b p‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (T : ℝ) * ∑ p ∈ S, ‖b p‖ ^ 2 := by
        congr 1
        rw [← Finset.sum_biUnion]
        · refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext p
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨lam, hlam⟩
            exact (Finset.mem_filter.1 hlam).1
          · intro hp
            obtain ⟨lam, hlam, -⟩ := fibre_unique hp (hunit p hp)
            exact ⟨lam, hlam⟩
        · intro l₁ _ l₂ _ hne
          simp only [Function.onFun, Finset.disjoint_left]
          intro p hp₁ hp₂
          have hpS : p ∈ S := (Finset.mem_filter.1 hp₁).1
          obtain ⟨lam, -, huniq⟩ := fibre_unique hpS (hunit p hpS)
          exact hne ((huniq l₁ hp₁).trans (huniq l₂ hp₂).symm)

end RatioFibre

/-! ## 5. Status metadata for this phase (metadata only — never evidence) -/

open Status in
/-- Status rows contributed by the post-Ramanujan exact algebra bank.  The three
formally banked rows correspond to theorems of *this* module; the three
research rows are metadata and are **not** proved here. -/
def statusRows : List LedgerEntry :=
  [ ⟨"ADDMIN-RAMREC-DIVISOR-COFACTOR-SPLIT45", Status.provedAlgebraic,
     "FORMALLY BANKED. coprime_divisor_of_coprime_mul, coprime_cofactor_of_coprime_mul, zmod_inv_mul, inverse_N_eq_inverse_r_mul_inverse_n_mod_M. No gcd(r,n)=1 hypothesis is used."⟩,
    ⟨"ADDMIN-RAMREC-PHASE-COLLISION45", Status.provedAlgebraic,
     "FORMALLY BANKED. phaseQ / phaseChar / Phi with the exact dictionary phaseChar_eq_exp and phaseChar_eq_iff; collision_denominators_eq, collision_residual_congruences, collision_twist_congr, collision_ratio_congruence, phase_collision_classification, ratioCoord. NO analytic spacing estimate is imported."⟩,
    ⟨"DETLINE-RAMREC-FIXEDM-RECIPROCAL-LS45", Status.provedFinite,
     "FORMALLY BANKED AT NATURAL SCALE. ratio_fibre_cauchy: sum over lambda of |fibre sum|^2 <= T * sum |b|^2, from explicit finite-support hypotheses (unit n-coordinates, fibre cardinality <= T). NO negative-log saving is encoded."⟩,
    ⟨"RAMREC-LARGE-COFACTOR-BRANCH45", Status.externallyAudited,
     "RESEARCH CLOSED (metadata only). No analytic bound for this branch is formalised in this repository."⟩,
    ⟨"RAMREC-MZERO-BRANCH45", Status.externallyAudited,
     "RESEARCH POWER CLOSED (metadata only) for the m_M = 0 branch. Not formalised."⟩,
    ⟨"RAMREC-HYBRID-M-TIMES-R-OFFDIAGONAL45", Status.externallyAudited,
     "RESEARCH POWER CLOSED (metadata only) for the hybrid M x r off-diagonal. Not formalised."⟩ ]

/-- No row of this phase is `closed`. -/
theorem statusRows_no_closed : ∀ e ∈ statusRows, e.status ≠ Status.closed := by decide

/-- Every research row of this phase is explicitly *not* kernel-proved. -/
theorem research_rows_not_kernel_proved :
    ∀ e ∈ statusRows, e.status = Status.externallyAudited →
      e.status.isKernelProved = false := by decide

end RamRecPostReduction
end CurrentProgramme
end TwinPrimeProject
