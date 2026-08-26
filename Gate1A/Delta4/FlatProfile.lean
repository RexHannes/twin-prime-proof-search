/-
# Gate-1A Δv4 §7 / §8 — the flat-main decomposition and the root-level error

The Δv4 closure route replaces the (retracted) two-sided norm comparison by a
*flat main* comparison: after quotient recombination the smooth profile is

```
Φ_y(x) = ζ₁ Ŵ(ζ₁ x) · e(c_y x) · Amplitude_y(x),      ζ₁ = L²/(p q),
Φ_flat(x) = ζ₁ Ŵ(ζ₁ x),
```

with `|c_y| ≤ C U⁻¹` and `Amplitude_y = 1 + O(U⁻² x²)`.

What is **proved here** is the exact perturbation algebra that turns those
factorwise statements into the flat-profile remainder bound, in a normed
algebra (the Schwartz seminorm layer of the actual source is a *seminorm* on
a commutative normed algebra of profiles, and the estimates used below are
exactly the submultiplicative ones):

* `norm_prod_sub_one_le` — `‖∏ f_i − 1‖ ≤ ∏ (1 + e_i) − 1` when `‖f_i − 1‖ ≤ e_i`;
* `one_add_pow_le` — `(1+ε)^n ≤ 1 + (2^n − 1) ε` for `0 ≤ ε ≤ 1`;
* `flat_profile_remainder_le_Uinv` — the assembled bound
  `‖Φ_y − Φ_flat‖ ≤ (2^n − 1) · ‖Φ_flat‖ · U⁻¹`
  for a profile differing from the flat one by `n` factors each within
  `U⁻¹` of `1` (source-`α` phase, `θ` phase, exact sine linear phase, TLSR
  Archimedean phase, sine amplitude correction: `n = 5`);
* `phase_factor_close_to_one` — the literal modular/Archimedean phase input
  `‖e(c x) − 1‖ ≤ 2π |c x|`, so that a phase with `|c| ≤ C U⁻¹` on the
  support `|x| ≤ 1` is within `2πC U⁻¹` of `1`;
* `error_absorbed_root_scale` — the §8 root-level absorption
  `(main + err)² ≤ 4 δ B²` when `main ≤ √δ B`, `err ≤ ε B`, `ε ≤ √δ`.

Nothing here claims the *identification* of the actual source profile with
this schematic form; that identification is carried as an explicit interface
field (`flatProfileSourceLegality`) in `Gate1A/Delta4/Interfaces.lean`.
-/
import Mathlib

namespace Gate1A

namespace Delta4

open Finset

/-! ## Factorwise perturbation algebra -/

/-- If each factor of a finite product is within `e i` of `1`, the product is
within `∏ (1 + e i) − 1` of `1`. -/
theorem norm_prod_sub_one_le {A : Type*} [NormedCommRing A] [NormOneClass A]
    {ι : Type*} (s : Finset ι) (f : ι → A) (e : ι → ℝ)
    (he : ∀ i ∈ s, ‖f i - 1‖ ≤ e i) (he0 : ∀ i ∈ s, 0 ≤ e i) :
    ‖(∏ i ∈ s, f i) - 1‖ ≤ (∏ i ∈ s, (1 + e i)) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hea : 0 ≤ e a := he0 a (Finset.mem_insert_self a s)
      have he' : ∀ i ∈ s, ‖f i - 1‖ ≤ e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
      have he0' : ∀ i ∈ s, 0 ≤ e i := fun i hi => he0 i (Finset.mem_insert_of_mem hi)
      have hIH := ih he' he0'
      have hPnn : (0 : ℝ) ≤ ∏ i ∈ s, (1 + e i) :=
        Finset.prod_nonneg fun i hi => by linarith [he0' i hi]
      have hPnorm : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, (1 + e i) := by
        have h1 : ‖∏ i ∈ s, f i‖ ≤ ‖(∏ i ∈ s, f i) - 1‖ + 1 := by
          have h2 := norm_add_le ((∏ i ∈ s, f i) - 1) (1 : A)
          simpa using h2
        linarith [hIH, h1]
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hsplit : f a * (∏ i ∈ s, f i) - 1
          = (f a - 1) * (∏ i ∈ s, f i) + ((∏ i ∈ s, f i) - 1) := by ring
      have hb1 : ‖(f a - 1) * (∏ i ∈ s, f i)‖ ≤ e a * (∏ i ∈ s, (1 + e i)) := by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul (he a (Finset.mem_insert_self a s)) hPnorm (norm_nonneg _) hea
      calc ‖f a * (∏ i ∈ s, f i) - 1‖
          = ‖(f a - 1) * (∏ i ∈ s, f i) + ((∏ i ∈ s, f i) - 1)‖ := by rw [hsplit]
        _ ≤ ‖(f a - 1) * (∏ i ∈ s, f i)‖ + ‖(∏ i ∈ s, f i) - 1‖ := norm_add_le _ _
        _ ≤ e a * (∏ i ∈ s, (1 + e i)) + ((∏ i ∈ s, (1 + e i)) - 1) := by
            linarith [hb1, hIH]
        _ = (1 + e a) * (∏ i ∈ s, (1 + e i)) - 1 := by ring

/-- `(1+ε)^n ≤ 1 + (2^n − 1) ε` for `0 ≤ ε ≤ 1`. -/
theorem one_add_pow_le {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1) (n : ℕ) :
    (1 + eps) ^ n ≤ 1 + (2 ^ n - 1) * eps := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hsq : eps * eps ≤ eps := by nlinarith
      have hstep : (1 + eps) ^ (n + 1) = (1 + eps) ^ n * (1 + eps) := by ring
      have hnn : (0 : ℝ) ≤ 1 + eps := by linarith
      calc (1 + eps) ^ (n + 1) = (1 + eps) ^ n * (1 + eps) := hstep
        _ ≤ (1 + (2 ^ n - 1) * eps) * (1 + eps) :=
            mul_le_mul_of_nonneg_right ih hnn
        _ ≤ 1 + (2 ^ (n + 1) - 1) * eps := by
            have : (1 + (2 ^ n - 1) * eps) * (1 + eps)
                = 1 + (2 ^ n) * eps + (2 ^ n - 1) * (eps * eps) := by ring
            rw [this]
            have h2 : (2 ^ n - 1) * (eps * eps) ≤ (2 ^ n - 1) * eps :=
              mul_le_mul_of_nonneg_left hsq (by linarith)
            have : (2 : ℝ) ^ (n + 1) - 1 = 2 ^ n + (2 ^ n - 1) := by ring
            rw [this]
            nlinarith [h2]

/-- **§7 (`flat_profile_remainder_le_Uinv`).**  If the profile `Phi` differs
from the flat profile `Phiflat` by a product of `n` factors, each within
`Uinv` of `1`, then

`‖Phi − Phiflat‖ ≤ (2^n − 1) · ‖Phiflat‖ · Uinv`.

With `n = 5` (source-`α` phase, `θ` phase, exact sine linear phase, TLSR
Archimedean phase, sine amplitude correction) the constant is `31`. -/
theorem flat_profile_remainder_le_Uinv {A : Type*} [NormedCommRing A] [NormOneClass A]
    {ι : Type*} (s : Finset ι) (f : ι → A) (Phiflat : A) (Uinv : ℝ)
    (hU0 : 0 ≤ Uinv) (hU1 : Uinv ≤ 1)
    (hf : ∀ i ∈ s, ‖f i - 1‖ ≤ Uinv) :
    ‖Phiflat * (∏ i ∈ s, f i) - Phiflat‖
      ≤ (2 ^ s.card - 1) * ‖Phiflat‖ * Uinv := by
  classical
  have hsplit : Phiflat * (∏ i ∈ s, f i) - Phiflat
      = Phiflat * ((∏ i ∈ s, f i) - 1) := by ring
  have hprod : ‖(∏ i ∈ s, f i) - 1‖ ≤ (∏ _i ∈ s, (1 + Uinv)) - 1 :=
    norm_prod_sub_one_le s f (fun _ => Uinv) (fun i hi => hf i hi) (fun _ _ => hU0)
  have hconst : (∏ _i ∈ s, (1 + Uinv)) = (1 + Uinv) ^ s.card := by
    rw [Finset.prod_const]
  have hpow : (1 + Uinv) ^ s.card ≤ 1 + (2 ^ s.card - 1) * Uinv :=
    one_add_pow_le hU0 hU1 s.card
  have hfin : ‖(∏ i ∈ s, f i) - 1‖ ≤ (2 ^ s.card - 1) * Uinv := by
    rw [hconst] at hprod
    linarith
  calc ‖Phiflat * (∏ i ∈ s, f i) - Phiflat‖
      = ‖Phiflat * ((∏ i ∈ s, f i) - 1)‖ := by rw [hsplit]
    _ ≤ ‖Phiflat‖ * ‖(∏ i ∈ s, f i) - 1‖ := norm_mul_le _ _
    _ ≤ ‖Phiflat‖ * ((2 ^ s.card - 1) * Uinv) :=
        mul_le_mul_of_nonneg_left hfin (norm_nonneg _)
    _ = (2 ^ s.card - 1) * ‖Phiflat‖ * Uinv := by ring

/-- The literal phase input: `‖e(c x) − 1‖ ≤ 2π |c x|` where `e(t) = exp(2πi t)`.
A removed Archimedean phase coefficient with `|c| ≤ C U⁻¹` on the support
`|x| ≤ 1` is therefore within `2π C U⁻¹` of `1`. -/
theorem phase_factor_close_to_one (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * t) - 1‖ ≤ 2 * Real.pi * |t| := by
  have hrw : (2 : ℂ) * Real.pi * Complex.I * t = Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast; ring
  rw [hrw]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]

/-- The amplitude input: a factor of the form `1 + w` with `‖w‖ ≤ c U⁻²x²`
is within `c U⁻¹` of `1` on the support `|x| ≤ 1`, `U⁻¹ ≤ 1`. -/
theorem amplitude_factor_close_to_one {A : Type*} [NormedCommRing A]
    (w : A) (c Uinv x : ℝ) (hc : 0 ≤ c) (hU0 : 0 ≤ Uinv) (hU1 : Uinv ≤ 1)
    (hx : |x| ≤ 1) (hw : ‖w‖ ≤ c * Uinv ^ 2 * x ^ 2) :
    ‖(1 + w) - 1‖ ≤ c * Uinv := by
  have hx2 : x ^ 2 ≤ 1 := by
    have : |x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg x]
    rwa [sq_abs] at this
  have hUsq : Uinv ^ 2 ≤ Uinv := by nlinarith
  have : ‖w‖ ≤ c * Uinv := by
    refine hw.trans ?_
    calc c * Uinv ^ 2 * x ^ 2 ≤ c * Uinv ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hx2 (by positivity)
      _ = c * Uinv ^ 2 := by ring
      _ ≤ c * Uinv := mul_le_mul_of_nonneg_left hUsq hc
  simpa using this

/-! ## §8 The root-level error absorption -/

/-- **§8 (`error_absorbed_root_scale`).**  Scalar form of the root-level
absorption: an error at *amplitude* level `ε` with `ε ≤ √δ` is absorbed at
the square-root scale, giving `(main + err)² ≤ 4 δ B²`.  The error may
**not** be compared with `δ` itself. -/
theorem error_absorbed_root_scale (main err B delta eps : ℝ)
    (hB : 0 ≤ B) (hdelta : 0 ≤ delta) (hmain0 : 0 ≤ main) (herr0 : 0 ≤ err)
    (hmain : main ≤ Real.sqrt delta * B) (herr : err ≤ eps * B)
    (heps : eps ≤ Real.sqrt delta) :
    (main + err) ^ 2 ≤ 4 * delta * B ^ 2 := by
  have hsq : Real.sqrt delta ^ 2 = delta := Real.sq_sqrt hdelta
  have hs0 : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsum : main + err ≤ 2 * (Real.sqrt delta * B) := by
    have : err ≤ Real.sqrt delta * B :=
      herr.trans (mul_le_mul_of_nonneg_right heps hB)
    linarith
  have h0 : 0 ≤ main + err := by linarith
  calc (main + err) ^ 2 ≤ (2 * (Real.sqrt delta * B)) ^ 2 :=
        pow_le_pow_left₀ h0 hsum 2
    _ = 4 * (Real.sqrt delta ^ 2) * B ^ 2 := by ring
    _ = 4 * delta * B ^ 2 := by rw [hsq]

end Delta4

end Gate1A
