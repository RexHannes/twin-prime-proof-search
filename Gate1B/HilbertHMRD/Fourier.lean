/-
# Gate1B / Hilbert-HMRD : finite Fourier analysis on `ZMod s`

Exact, elementary finite Fourier analysis for the effective modulus `s`:

* the additive character `ez s a = e_s(a)` on `ZMod s` and its exact orthogonality;
* Fourier coefficients, inversion, and Parseval;
* the `ℓ¹ ≤ √(#support) · ℓ²` Cauchy estimate, and its specialisation to a phase supported
  on the units: `∑_t |f̂(t)| ≤ √(φ(s))`.

Every constant below is kernel-checked in the stated normalisation
`f̂(t) = s⁻¹ ∑_x f(x) e_s(−t x)`, `f(x) = ∑_t f̂(t) e_s(t x)`.

No analytic input, no external theorem.
-/
import Universal.D0WP.AdditiveCharacterCore

namespace Gate1B.HilbertHMRD

open Finset Universal.D0WP

noncomputable section

variable {s : ℕ} [NeZero s]

/-! ## 1. The additive character on `ZMod s` -/

/-- The additive character `e_s` viewed on `ZMod s`. -/
def ez (s : ℕ) (a : ZMod s) : ℂ := ac s (a.val : ℤ)

omit [NeZero s] in
theorem ez_norm (a : ZMod s) : ‖ez s a‖ = 1 := ac_norm _ _

omit [NeZero s] in
theorem ez_ne_zero (a : ZMod s) : ez s a ≠ 0 := ac_ne_zero _ _

/-- If an integer `z` represents `a` in `ZMod s`, then `ez s a = e_s(z)`. -/
theorem ez_eq_ac {a : ZMod s} {z : ℤ} (h : (z : ZMod s) = a) : ez s a = ac s z := by
  refine ac_congr (NeZero.ne s) ?_
  have hcast : ((a.val : ℤ) : ZMod s) = ((z : ℤ) : ZMod s) := by
    push_cast
    simp [h]
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).1 hcast

@[simp] theorem ez_zero : ez s 0 = 1 := by
  rw [ez_eq_ac (a := (0 : ZMod s)) (z := 0) (by simp), ac_zero]

theorem ez_add (a b : ZMod s) : ez s (a + b) = ez s a * ez s b := by
  rw [ez_eq_ac (a := a + b) (z := (a.val : ℤ) + (b.val : ℤ)) (by push_cast; simp), ac_add]
  rfl

theorem ez_conj (a : ZMod s) : (starRingEnd ℂ) (ez s a) = ez s (-a) := by
  rw [ez, ac_conj, ez_eq_ac (a := -a) (z := -(a.val : ℤ)) (by push_cast; simp)]

/-- **Exact orthogonality on `ZMod s`.** -/
theorem sum_ez_orth (c : ZMod s) :
    ∑ a : ZMod s, ez s (c * a) = if c = 0 then (s : ℂ) else 0 := by
  have hs : s ≠ 0 := NeZero.ne s
  have hrange : ∑ a : ZMod s, ez s (c * a) = ∑ j ∈ range s, ez s (c * (j : ZMod s)) := by
    refine Finset.sum_nbij' (fun a => a.val) (fun j => (j : ZMod s)) ?_ ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_range.2 (ZMod.val_lt a)
    · intro j _; exact Finset.mem_univ _
    · intro a _; simp [ZMod.natCast_val, ZMod.cast_id]
    · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hj)
    · intro a _; simp [ZMod.natCast_val, ZMod.cast_id]
  have hterm : ∀ j ∈ range s, ez s (c * (j : ZMod s)) = ac s ((c.val : ℤ) * (j : ℕ)) := by
    intro j _
    refine ez_eq_ac ?_
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  rw [hrange, Finset.sum_congr rfl hterm, sum_ac_range hs]
  by_cases hc : c = 0
  · subst hc; simp
  · have hnd : ¬ ((s : ℤ) ∣ (c.val : ℤ)) := by
      intro hdvd
      have hlt : |(c.val : ℤ)| < (s : ℤ) := by
        rw [abs_of_nonneg (by positivity)]
        exact_mod_cast ZMod.val_lt c
      have h0 : (c.val : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      exact hc ((ZMod.val_eq_zero c).mp (by exact_mod_cast h0))
    rw [if_neg hnd, if_neg hc]

/-- Orthogonality in the form used below: the character sum in `t`. -/
theorem sum_ez_orth' (x y : ZMod s) :
    ∑ t : ZMod s, ez s (-(t * x)) * (starRingEnd ℂ) (ez s (-(t * y)))
      = if x = y then (s : ℂ) else 0 := by
  have hterm : ∀ t : ZMod s,
      ez s (-(t * x)) * (starRingEnd ℂ) (ez s (-(t * y))) = ez s ((y - x) * t) := by
    intro t
    rw [ez_conj, ← ez_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, sum_ez_orth]
  by_cases h : x = y
  · subst h; simp
  · have hne : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    simp [hne, h]

/-! ## 2. Fourier coefficients, inversion, Parseval -/

/-- The finite Fourier coefficient `f̂(t) = s⁻¹ ∑_x f(x) e_s(−t x)`. -/
def fcoef (s : ℕ) [NeZero s] (f : ZMod s → ℂ) (t : ZMod s) : ℂ :=
  (s : ℂ)⁻¹ * ∑ x : ZMod s, f x * ez s (-(t * x))

/-- **Fourier inversion (kernel-proved).** -/
theorem fourier_inversion (f : ZMod s → ℂ) (x : ZMod s) :
    ∑ t : ZMod s, fcoef s f t * ez s (t * x) = f x := by
  have hs0 : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne s)
  have expand : ∀ t : ZMod s, fcoef s f t * ez s (t * x)
      = (s : ℂ)⁻¹ * ∑ y : ZMod s,
          (ez s (-(t * y)) * (starRingEnd ℂ) (ez s (-(t * x)))) * f y := by
    intro t
    rw [fcoef, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ez_conj, neg_neg]
    ring
  rw [Finset.sum_congr rfl fun t _ => expand t, ← Finset.mul_sum, Finset.sum_comm]
  have inner : ∀ y : ZMod s,
      ∑ t : ZMod s, (ez s (-(t * y)) * (starRingEnd ℂ) (ez s (-(t * x)))) * f y
        = (if y = x then (s : ℂ) else 0) * f y := by
    intro y
    rw [← Finset.sum_mul, sum_ez_orth']
  rw [Finset.sum_congr rfl fun y _ => inner y]
  simp [Finset.sum_ite_eq', hs0]

/-- **Parseval (kernel-proved).** -/
theorem fcoef_parseval (f : ZMod s → ℂ) :
    ∑ t : ZMod s, ‖fcoef s f t‖ ^ 2 = (s : ℝ)⁻¹ * ∑ x : ZMod s, ‖f x‖ ^ 2 := by
  have hs0R : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne s)
  have hc : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj']
    push_cast
    ring
  set G : ZMod s → ℂ := fun t => ∑ x : ZMod s, f x * ez s (-(t * x)) with hG
  have hmain : ∑ t : ZMod s, G t * (starRingEnd ℂ) (G t)
      = (s : ℂ) * ∑ x : ZMod s, f x * (starRingEnd ℂ) (f x) := by
    have e1 : ∀ t : ZMod s, G t * (starRingEnd ℂ) (G t)
        = ∑ x : ZMod s, ∑ y : ZMod s,
            (ez s (-(t * x)) * (starRingEnd ℂ) (ez s (-(t * y))))
              * (f x * (starRingEnd ℂ) (f y)) := by
      intro t
      rw [hG]
      simp only [map_sum]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [map_mul]
      ring
    rw [Finset.sum_congr rfl fun t _ => e1 t, Finset.sum_comm]
    have step : ∀ x : ZMod s, ∑ t : ZMod s, ∑ y : ZMod s,
        (ez s (-(t * x)) * (starRingEnd ℂ) (ez s (-(t * y)))) * (f x * (starRingEnd ℂ) (f y))
        = (s : ℂ) * (f x * (starRingEnd ℂ) (f x)) := by
      intro x
      rw [Finset.sum_comm]
      have inner : ∀ y : ZMod s, ∑ t : ZMod s,
          (ez s (-(t * x)) * (starRingEnd ℂ) (ez s (-(t * y)))) * (f x * (starRingEnd ℂ) (f y))
          = (if x = y then (s : ℂ) else 0) * (f x * (starRingEnd ℂ) (f y)) := by
        intro y
        rw [← Finset.sum_mul, sum_ez_orth']
      rw [Finset.sum_congr rfl fun y _ => inner y]
      simp
    rw [Finset.sum_congr rfl fun x _ => step x, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hc (G t),
    Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hc (f x)] at hmain
  have hreal : ∑ t : ZMod s, ‖G t‖ ^ 2 = (s : ℝ) * ∑ x : ZMod s, ‖f x‖ ^ 2 := by
    exact_mod_cast hmain
  have hfc : ∀ t : ZMod s, ‖fcoef s f t‖ ^ 2 = ((s : ℝ)⁻¹) ^ 2 * ‖G t‖ ^ 2 := by
    intro t
    have hrfl : fcoef s f t = (s : ℂ)⁻¹ * G t := rfl
    rw [hrfl, norm_mul, mul_pow]
    congr 1
    simp
  rw [Finset.sum_congr rfl fun t _ => hfc t, ← Finset.mul_sum, hreal]
  field_simp

/-! ## 3. The `ℓ¹` Fourier cost -/

/-- **`ℓ¹ ≤ √(#S) · ℓ²` for a phase supported on `S`.**  If `f` vanishes off a finset `S`
and `‖f‖ ≤ 1` pointwise, then `∑_t |f̂(t)| ≤ √(#S)`. -/
theorem fcoef_l1_le_sqrt_card (f : ZMod s → ℂ) (S : Finset (ZMod s))
    (hsupp : ∀ x, x ∉ S → f x = 0) (hb : ∀ x, ‖f x‖ ≤ 1) :
    ∑ t : ZMod s, ‖fcoef s f t‖ ≤ Real.sqrt S.card := by
  have hs0R : (0 : ℝ) < s := by
    have := Nat.pos_of_ne_zero (NeZero.ne s)
    exact_mod_cast this
  have hcard : (Fintype.card (ZMod s) : ℝ) = s := by
    simp [ZMod.card]
  have henergy : ∑ x : ZMod s, ‖f x‖ ^ 2 ≤ (S.card : ℝ) := by
    have hsplit : ∑ x : ZMod s, ‖f x‖ ^ 2 = ∑ x ∈ S, ‖f x‖ ^ 2 := by
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro x _ hx
      rw [hsupp x hx]
      simp
    rw [hsplit]
    calc ∑ x ∈ S, ‖f x‖ ^ 2 ≤ ∑ _x ∈ S, (1 : ℝ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          nlinarith [norm_nonneg (f x), hb x]
      _ = (S.card : ℝ) := by simp
  have cs : ∑ t : ZMod s, ‖fcoef s f t‖ * 1
      ≤ Real.sqrt (∑ t : ZMod s, ‖fcoef s f t‖ ^ 2)
          * Real.sqrt (∑ _t : ZMod s, (1 : ℝ) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h2 : Real.sqrt (∑ _t : ZMod s, (1 : ℝ) ^ 2) = Real.sqrt s := by
    simp
  have h1 : Real.sqrt (∑ t : ZMod s, ‖fcoef s f t‖ ^ 2)
      ≤ Real.sqrt ((s : ℝ)⁻¹ * (S.card : ℝ)) := by
    rw [fcoef_parseval]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left henergy (by positivity))
  calc ∑ t : ZMod s, ‖fcoef s f t‖ = ∑ t : ZMod s, ‖fcoef s f t‖ * 1 := by simp
    _ ≤ Real.sqrt (∑ t : ZMod s, ‖fcoef s f t‖ ^ 2)
          * Real.sqrt (∑ _t : ZMod s, (1 : ℝ) ^ 2) := cs
    _ ≤ Real.sqrt ((s : ℝ)⁻¹ * (S.card : ℝ)) * Real.sqrt s := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    _ = Real.sqrt S.card := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        field_simp

/-- The unit residues of `ZMod s`, as a finset. -/
def unitSet (s : ℕ) [NeZero s] : Finset (ZMod s) := Finset.univ.filter (fun x => IsUnit x)

/-- `#{units} = φ(s)`. -/
theorem card_unitSet : (unitSet s).card = Nat.totient s := by
  classical
  rw [← ZMod.card_units_eq_totient s]
  refine (Finset.card_bij (fun (u : (ZMod s)ˣ) _ => (u : ZMod s)) ?_ ?_ ?_).symm
  · intro u _
    simp [unitSet, Units.isUnit]
  · intro u _ v _ h
    exact Units.ext h
  · intro x hx
    simp only [unitSet, Finset.mem_filter] at hx
    obtain ⟨w, hw⟩ := hx.2
    exact ⟨w, Finset.mem_univ _, hw⟩

/-- **`ℓ¹` Fourier cost of a unimodular phase supported on the units: `≤ √(φ(s))`.** -/
theorem fcoef_l1_le_sqrt_totient (f : ZMod s → ℂ)
    (hsupp : ∀ x, ¬ IsUnit x → f x = 0) (hb : ∀ x, ‖f x‖ ≤ 1) :
    ∑ t : ZMod s, ‖fcoef s f t‖ ≤ Real.sqrt (Nat.totient s) := by
  have hmain := fcoef_l1_le_sqrt_card f (unitSet s)
    (fun x hx => hsupp x (by simpa [unitSet] using hx)) hb
  rwa [card_unitSet] at hmain

end

end Gate1B.HilbertHMRD
