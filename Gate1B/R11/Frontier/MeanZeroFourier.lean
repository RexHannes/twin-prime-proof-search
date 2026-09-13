/-
# Gate1B / R11 / Frontier : line-mean-zero finite Fourier bank

Finite, exact Fourier algebra for a **line interval** `I ⊆ ZMod Q` and a target `b`.

* `lineMean I b = |I|⁻¹ ∑_{t ∈ I} b t`;
* `bPerp I b = 1_I · (b − lineMean I b)`, the zero-padded mean-zero projection;
* `∑_t bPerp I b t = 0` (over `I` and over the whole cyclic group);
* in the banked normalisation `f̂(t) = Q⁻¹ ∑_x f(x) e_Q(−t x)` of
  `Gate1B.HilbertHMRD.Fourier` (reused, not duplicated): `bPerp̂(0) = 0`, together with the
  already kernel-proved Fourier inversion and Parseval.

**Firewall.**  The last section exhibits an explicit finite datum with `f̂(0) = 0` and
`f̂(ξ) ≠ 0` for a nonzero frequency `ξ`.  So mean zero alone gives *no* high-frequency
saving: it kills exactly one Fourier mode and nothing else.  No analytic statement is made.
-/
import Gate1B.HilbertHMRD.Fourier

namespace Gate1B.R11.Frontier

open Finset Gate1B.HilbertHMRD Universal.D0WP

noncomputable section

variable {Q : ℕ} [NeZero Q]

/-! ## 1. Mean and mean-zero projection on a line interval -/

/-- The mean of `b` over the line interval `I`. -/
def lineMean (I : Finset (ZMod Q)) (b : ZMod Q → ℂ) : ℂ :=
  (I.card : ℂ)⁻¹ * ∑ t ∈ I, b t

/-- The zero-padded mean-zero projection `b_⊥ = 1_I · (b − mean)`. -/
def bPerp (I : Finset (ZMod Q)) (b : ZMod Q → ℂ) (t : ZMod Q) : ℂ :=
  if t ∈ I then b t - lineMean I b else 0

omit [NeZero Q] in
theorem bPerp_of_not_mem {I : Finset (ZMod Q)} {b : ZMod Q → ℂ} {t : ZMod Q} (ht : t ∉ I) :
    bPerp I b t = 0 := if_neg ht

omit [NeZero Q] in
/-- **MEAN ZERO on the interval.** -/
theorem sum_bPerp_interval (I : Finset (ZMod Q)) (b : ZMod Q → ℂ) (hI : I.Nonempty) :
    ∑ t ∈ I, bPerp I b t = 0 := by
  have hcard : (I.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hI).ne'
  have hsplit : ∑ t ∈ I, bPerp I b t = (∑ t ∈ I, b t) - I.card * lineMean I b := by
    calc ∑ t ∈ I, bPerp I b t = ∑ t ∈ I, (b t - lineMean I b) :=
          Finset.sum_congr rfl fun t ht => if_pos ht
      _ = (∑ t ∈ I, b t) - I.card * lineMean I b := by
          rw [Finset.sum_sub_distrib]; simp
  rw [hsplit, lineMean]
  field_simp
  ring

/-- **MEAN ZERO on the whole cyclic group** (the padding contributes nothing). -/
theorem sum_bPerp_univ (I : Finset (ZMod Q)) (b : ZMod Q → ℂ) (hI : I.Nonempty) :
    ∑ t : ZMod Q, bPerp I b t = 0 := by
  rw [← Finset.sum_subset (Finset.subset_univ I) (fun x _ hx => bPerp_of_not_mem hx)]
  exact sum_bPerp_interval I b hI

/-! ## 2. The zero frequency -/

/-- In the banked normalisation, `f̂(0) = Q⁻¹ ∑_x f(x)`. -/
theorem fcoef_zero_eq (f : ZMod Q → ℂ) :
    fcoef Q f 0 = (Q : ℂ)⁻¹ * ∑ x : ZMod Q, f x := by
  simp [fcoef]

/-- `f̂(0) = 0` exactly when the total sum vanishes. -/
theorem fcoef_zero_eq_zero_iff (f : ZMod Q → ℂ) :
    fcoef Q f 0 = 0 ↔ ∑ x : ZMod Q, f x = 0 := by
  have hQ : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
  rw [fcoef_zero_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd (inv_eq_zero.mp h1) hQ
    · exact h2
  · intro h; rw [h, mul_zero]

/-- **`b̂_⊥(0) = 0`.** -/
theorem fcoef_bPerp_zero (I : Finset (ZMod Q)) (b : ZMod Q → ℂ) (hI : I.Nonempty) :
    fcoef Q (bPerp I b) 0 = 0 :=
  (fcoef_zero_eq_zero_iff _).2 (sum_bPerp_univ I b hI)

/-! ## 3. Inversion and Parseval (reused, kernel-proved) -/

/-- FINITE FOURIER INVERSION: kernel-proved (banked in `Gate1B.HilbertHMRD.Fourier`). -/
theorem bank_fourier_inversion (f : ZMod Q → ℂ) (x : ZMod Q) :
    ∑ t : ZMod Q, fcoef Q f t * ez Q (t * x) = f x := fourier_inversion f x

/-- PARSEVAL: kernel-proved (banked in `Gate1B.HilbertHMRD.Fourier`). -/
theorem bank_parseval (f : ZMod Q → ℂ) :
    ∑ t : ZMod Q, ‖fcoef Q f t‖ ^ 2 = (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖f x‖ ^ 2 := fcoef_parseval f

/-! ## 4. Firewall: mean zero is exactly one mode, and nothing more -/

/-- `e_2(1) = −1`. -/
theorem ez_two_one : ez 2 (1 : ZMod 2) = -1 := by
  have hval : (((1 : ZMod 2).val : ℤ)) = 1 := by decide
  rw [ez, hval, ac]
  have harg : (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) / ((2 : ℕ) : ℂ))
      = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_pi_mul_I]

/-- The two-point test function `f(0) = 1`, `f(1) = −1`. -/
def signTest : ZMod 2 → ℂ := fun x => if x = 0 then 1 else -1

theorem fcoef_signTest_zero : fcoef 2 signTest 0 = 0 := by
  rw [fcoef_zero_eq_zero_iff, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  norm_num [signTest]

theorem fcoef_signTest_one : fcoef 2 signTest 1 = 1 := by
  have h0 : signTest (0 : ZMod 2) * ez 2 (-(1 * (0 : ZMod 2))) = 1 := by
    simp [signTest]
  have h1 : signTest (1 : ZMod 2) * ez 2 (-(1 * (1 : ZMod 2))) = 1 := by
    rw [show (-(1 * (1 : ZMod 2))) = 1 from rfl, ez_two_one]
    simp [signTest]
  rw [fcoef, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl,
    Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), h0, h1]
  norm_num

/-- **MEAN-ZERO FIREWALL.**  There is a finite datum whose zero Fourier mode vanishes while a
nonzero mode does not.  Hence `b̂_⊥(0) = 0` does **not** imply `b̂_⊥(ξ) = 0` for `ξ ≠ 0`, and
mean zero by itself provides no quantitative high-frequency saving. -/
theorem meanZero_does_not_kill_high_frequencies :
    ∃ (f : ZMod 2 → ℂ), fcoef 2 f 0 = 0 ∧ ∃ ξ : ZMod 2, ξ ≠ 0 ∧ fcoef 2 f ξ ≠ 0 := by
  refine ⟨signTest, fcoef_signTest_zero, 1, by decide, ?_⟩
  rw [fcoef_signTest_one]
  exact one_ne_zero

/-- The same firewall stated for a genuine mean-zero projection of a line interval. -/
theorem bPerp_high_frequency_not_zero :
    ∃ (I : Finset (ZMod 2)) (b : ZMod 2 → ℂ), I.Nonempty ∧
      fcoef 2 (bPerp I b) 0 = 0 ∧ ∃ ξ : ZMod 2, ξ ≠ 0 ∧ fcoef 2 (bPerp I b) ξ ≠ 0 := by
  refine ⟨Finset.univ, signTest, ⟨0, Finset.mem_univ _⟩, ?_, 1, by decide, ?_⟩
  · exact fcoef_bPerp_zero _ _ ⟨0, Finset.mem_univ _⟩
  · have hmean : lineMean (Finset.univ : Finset (ZMod 2)) signTest = 0 := by
      rw [lineMean, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
      norm_num [signTest]
    have hEq : bPerp (Finset.univ : Finset (ZMod 2)) signTest = signTest := by
      funext t
      simp [bPerp, hmean]
    rw [hEq, fcoef_signTest_one]
    exact one_ne_zero

end

end Gate1B.R11.Frontier
