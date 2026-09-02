/-
# Universal / D0WP — the small-`rSharp` finite Fourier lane

**Status of this module: KERNEL_PROVED finite Fourier analysis, plus one
explicitly external analytic input.**

For fixed `wp` the provider meets the *reciprocal periodic function*
`u ↦ e_{rSharp}(A · inverse(u))`, which is an arbitrary function on the finite
cyclic group.  Kernel-proved here:

* the normalized finite Fourier expansion (inversion formula);
* Parseval;
* the `L¹` Fourier-coefficient cost `Σ_k |f̂(k)| ≤ sqrt rSharp` for `|f| ≤ 1`.

The remaining ingredient — a bound for a *pure Möbius linear/polynomial phase
sum* over the `d0`-source — is **not** proved here.  It is recorded as an
explicit external input with its own source contract
(`PureMobiusPolynomialPhaseInput`), status `PAPER_CLOSED_EXTERNAL`, and the
small-`rSharp` estimate is compiled *conditionally* on it.
-/
import Universal.D0WP.FiniteFourierMatrix

namespace Universal.D0WP

open Finset

noncomputable section

/-- Normalized finite Fourier coefficient. -/
def fhat (n : ℕ) (f : Fin n → ℂ) (k : Fin n) : ℂ :=
  (n : ℂ)⁻¹ * ∑ v : Fin n, ac n (-(((k : ℕ) : ℤ) * (v : ℕ))) * f v

theorem fhat_eq (n : ℕ) (f : Fin n → ℂ) (k : Fin n) :
    fhat n f k = (n : ℂ)⁻¹ * Ktrans 1 n f k := by
  unfold fhat Ktrans Kker
  congr 1
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 2
  push_cast
  ring

/-- **Finite Fourier inversion (kernel-proved).** -/
theorem fourier_inversion {n : ℕ} (hn : n ≠ 0) (f : Fin n → ℂ) (u : Fin n) :
    ∑ k : Fin n, fhat n f k * ac n (((k : ℕ) : ℤ) * (u : ℕ)) = f u := by
  have hcop : Nat.Coprime 1 n := Nat.coprime_one_left n
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hconj : ∀ k : Fin n, ac n (((k : ℕ) : ℤ) * (u : ℕ))
      = (starRingEnd ℂ) (Kker 1 n k u) := by
    intro k
    unfold Kker
    rw [ac_conj]
    congr 1
    push_cast
    ring
  have expand : ∀ k : Fin n, fhat n f k * ac n (((k : ℕ) : ℤ) * (u : ℕ))
      = (n : ℂ)⁻¹ * ∑ v : Fin n, (Kker 1 n k v * (starRingEnd ℂ) (Kker 1 n k u)) * f v := by
    intro k
    rw [fhat_eq, hconj k]
    unfold Ktrans
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [Finset.sum_congr rfl (fun k _ => expand k), ← Finset.mul_sum, Finset.sum_comm]
  have inner : ∀ v : Fin n, ∑ k : Fin n, (Kker 1 n k v * (starRingEnd ℂ) (Kker 1 n k u)) * f v
      = (if v = u then (n : ℂ) else 0) * f v := by
    intro v
    rw [← Finset.sum_mul, Kker_col_orth hn hcop]
  rw [Finset.sum_congr rfl (fun v _ => inner v)]
  simp [Finset.sum_ite_eq', hn0]

/-- **Parseval (kernel-proved).** -/
theorem fhat_parseval {n : ℕ} (hn : n ≠ 0) (f : Fin n → ℂ) :
    ∑ k : Fin n, ‖fhat n f k‖ ^ 2 = (n : ℝ)⁻¹ * ∑ u : Fin n, ‖f u‖ ^ 2 := by
  have hcop : Nat.Coprime 1 n := Nat.coprime_one_left n
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h : ∀ k : Fin n, ‖fhat n f k‖ ^ 2 = ((n : ℝ)⁻¹) ^ 2 * ‖Ktrans 1 n f k‖ ^ 2 := by
    intro k
    rw [fhat_eq, norm_mul]
    simp [mul_pow]
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, Ktrans_l2 hn hcop]
  field_simp

/-- **`L¹` Fourier cost `≤ sqrt rSharp` (kernel-proved).** -/
theorem fhat_l1_le {n : ℕ} (hn : n ≠ 0) (f : Fin n → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1) :
    ∑ k : Fin n, ‖fhat n f k‖ ≤ Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by
    have := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hsum : ∑ u : Fin n, ‖f u‖ ^ 2 ≤ (n : ℝ) := by
    calc ∑ u : Fin n, ‖f u‖ ^ 2 ≤ ∑ _u : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun u _ => ?_)
          have h1 := hf u
          nlinarith [norm_nonneg (f u)]
      _ = (n : ℝ) := by simp
  have cs : ∑ k : Fin n, ‖fhat n f k‖ * 1
      ≤ Real.sqrt (∑ k : Fin n, ‖fhat n f k‖ ^ 2) * Real.sqrt (∑ _k : Fin n, (1:ℝ) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h1 : Real.sqrt (∑ k : Fin n, ‖fhat n f k‖ ^ 2) ≤ 1 := by
    rw [fhat_parseval hn]
    have : (n : ℝ)⁻¹ * ∑ u : Fin n, ‖f u‖ ^ 2 ≤ 1 := by
      rw [inv_mul_le_iff₀ hn0]
      simpa using hsum
    calc Real.sqrt ((n : ℝ)⁻¹ * ∑ u : Fin n, ‖f u‖ ^ 2) ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt this
      _ = 1 := Real.sqrt_one
  have h2 : Real.sqrt (∑ _k : Fin n, (1:ℝ) ^ 2) = Real.sqrt n := by simp
  calc ∑ k : Fin n, ‖fhat n f k‖ = ∑ k : Fin n, ‖fhat n f k‖ * 1 := by simp
    _ ≤ Real.sqrt (∑ k : Fin n, ‖fhat n f k‖ ^ 2) * Real.sqrt (∑ _k : Fin n, (1:ℝ) ^ 2) := cs
    _ ≤ 1 * Real.sqrt n := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    _ = Real.sqrt n := by ring

/-- The reciprocal periodic function attached to a fixed `wp`: `u ↦ e_n(A u⁻¹)`,
with the inverse taken in `ZMod n` (zero-extended off the units). -/
def recipPhase (A n : ℕ) (u : Fin n) : ℂ :=
  ac n ((A : ℤ) * ((((u : ℕ) : ZMod n)⁻¹).val))

theorem recipPhase_norm (A n : ℕ) (u : Fin n) : ‖recipPhase A n u‖ = 1 :=
  ac_norm _ _

/-- **Source contract of the external pure-Möbius polynomial-phase input.**

These are the *hypotheses of the external theorem*, recorded literally.  This
structure carries no estimate. -/
structure PureMobiusPolynomialPhaseContract where
  /-- The `d0`-scale lower bound exponent. -/
  eta : ℝ
  /-- `eta > 0` is fixed. -/
  eta_pos : 0 < eta
  /-- The size parameter. -/
  X : ℝ
  /-- The `d0`-scale. -/
  D : ℝ
  /-- Literal range hypothesis `D ≥ X ^ eta`. -/
  D_lower : D ≥ X ^ eta
  /-- The vertical parameter bound exponent. -/
  C0 : ℝ
  /-- The vertical parameter. -/
  t : ℝ
  /-- Literal range hypothesis `|t| ≤ X ^ C0`. -/
  t_bound : |t| ≤ X ^ C0
  /-- The phase is additive and linear in the summation variable. -/
  additiveLinearPhase : Prop
  /-- The weight is a smooth dyadic weight. -/
  smoothDyadicWeight : Prop

/-- **External analytic input, status `PAPER_CLOSED_EXTERNAL`.**

The field `bound` is the *external theorem's conclusion*: for every frequency,
the pure-Möbius linear-phase sum over the `d0`-source is at most `Bd`.  It is
supplied from outside; nothing in this repository proves it, and no default
inhabitant is provided. -/
structure PureMobiusPolynomialPhaseInput (n : ℕ) (g : Fin n → ℂ) (Bd : ℝ) where
  /-- The literal source contract of the external theorem. -/
  contract : PureMobiusPolynomialPhaseContract
  /-- The external conclusion, frequency by frequency. -/
  bound : ∀ k : Fin n, ‖∑ u : Fin n, g u * ac n (((k : ℕ) : ℤ) * (u : ℕ))‖ ≤ Bd

/-- **SMALL-`rSharp` CONDITIONAL COMPILER (kernel-proved implication).**

Given the external per-frequency bound, the finite Fourier `L¹` cost turns it
into a bound for the twisted sum, with the loss `sqrt rSharp` and nothing else.
The analytic content is entirely in the hypothesis `hg`. -/
theorem small_rSharp_compiler {n : ℕ} (hn : n ≠ 0) (f g : Fin n → ℂ) (Bd : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ 1)
    (hg : ∀ k : Fin n, ‖∑ u : Fin n, g u * ac n (((k : ℕ) : ℤ) * (u : ℕ))‖ ≤ Bd) :
    ‖∑ u : Fin n, f u * g u‖ ≤ Real.sqrt n * Bd := by
  have hBd : 0 ≤ Bd := le_trans (norm_nonneg _) (hg ⟨0, Nat.pos_of_ne_zero hn⟩)
  have hrw : ∑ u : Fin n, f u * g u
      = ∑ k : Fin n, fhat n f k * ∑ u : Fin n, g u * ac n (((k : ℕ) : ℤ) * (u : ℕ)) := by
    have h1 : ∀ u : Fin n, f u * g u
        = ∑ k : Fin n, fhat n f k * ac n (((k : ℕ) : ℤ) * (u : ℕ)) * g u := by
      intro u
      rw [← Finset.sum_mul, fourier_inversion hn f u]
    rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  rw [hrw]
  calc ‖∑ k : Fin n, fhat n f k * ∑ u : Fin n, g u * ac n (((k : ℕ) : ℤ) * (u : ℕ))‖
      ≤ ∑ k : Fin n, ‖fhat n f k * ∑ u : Fin n, g u * ac n (((k : ℕ) : ℤ) * (u : ℕ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k : Fin n, ‖fhat n f k‖ * Bd := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hg k) (norm_nonneg _)
    _ = (∑ k : Fin n, ‖fhat n f k‖) * Bd := by rw [Finset.sum_mul]
    _ ≤ Real.sqrt n * Bd := mul_le_mul_of_nonneg_right (fhat_l1_le hn f hf) hBd

/-- The conditional small-`rSharp` estimate, stated through the external input
record so that the dependency is visible in the statement. -/
theorem small_rSharp_estimate_of_input {n : ℕ} (hn : n ≠ 0) (f g : Fin n → ℂ) (Bd : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ 1) (input : PureMobiusPolynomialPhaseInput n g Bd) :
    ‖∑ u : Fin n, f u * g u‖ ≤ Real.sqrt n * Bd :=
  small_rSharp_compiler hn f g Bd hf input.bound

end

end Universal.D0WP
