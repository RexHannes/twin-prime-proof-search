/-
# Gate1B / R11 / Frontier : low/high frequency projection and first-moment reassembly

Exact finite algebra, no analytic content.

* `lowProj S f` is the finite frequency projection of `f` onto the low-frequency set
  `S ⊆ ZMod Q`, and `highProj S f = f − lowProj S f`;
* `f = lowProj S f + highProj S f` (in particular for `f = b_⊥`);
* `lowProj` is a genuine spectral projection: `(lowProj S f)^(t) = f̂(t)` for `t ∈ S` and `0`
  otherwise;
* at the **first-moment** level, for any weight `w`, the linear functionals
  `R_lo, R_hi, R_total` satisfy `R_total = R_lo + R_hi`.

**Mixed-quadratic firewall.**  Nothing in this bank asserts `|L_lo + L_hi|² = |L_lo|² + |L_hi|²`.
The actual identity, `|L_lo + L_hi|² = |L_lo|² + |L_hi|² + 2 Re(L_lo · conj L_hi)`, is recorded,
together with an explicit datum for which the mixed term is nonzero.  The mixed term may not be
deleted.
-/
import Gate1B.R11.Frontier.MeanZeroFourier

namespace Gate1B.R11.Frontier

open Finset Gate1B.HilbertHMRD Universal.D0WP

noncomputable section

variable {Q : ℕ} [NeZero Q]

/-! ## 1. The projections -/

/-- The low-frequency part of `f` relative to the frequency set `S`. -/
def lowProj (S : Finset (ZMod Q)) (f : ZMod Q → ℂ) (x : ZMod Q) : ℂ :=
  ∑ t ∈ S, fcoef Q f t * ez Q (t * x)

/-- The high-frequency part, `(I − P_lo) f`. -/
def highProj (S : Finset (ZMod Q)) (f : ZMod Q → ℂ) (x : ZMod Q) : ℂ :=
  f x - lowProj S f x

/-- **EXACT DECOMPOSITION** `f = P_lo f + (I − P_lo) f`. -/
theorem low_add_high (S : Finset (ZMod Q)) (f : ZMod Q → ℂ) (x : ZMod Q) :
    lowProj S f x + highProj S f x = f x := by
  rw [highProj]; ring

/-- The decomposition applied to the mean-zero projection `b_⊥`. -/
theorem bPerp_low_add_high (S I : Finset (ZMod Q)) (b : ZMod Q → ℂ) (x : ZMod Q) :
    lowProj S (bPerp I b) x + highProj S (bPerp I b) x = bPerp I b x :=
  low_add_high S (bPerp I b) x

/-! ## 2. `lowProj` is a spectral projection -/

/-- Fourier coefficient of a single pure frequency. -/
theorem fcoef_pure (t0 t : ZMod Q) :
    fcoef Q (fun x => ez Q (t0 * x)) t = if t = t0 then 1 else 0 := by
  have hQ : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
  have hterm : ∀ x : ZMod Q, ez Q (t0 * x) * ez Q (-(t * x)) = ez Q ((t0 - t) * x) := by
    intro x
    rw [← ez_add]
    congr 1
    ring
  rw [fcoef, Finset.sum_congr rfl fun x _ => hterm x, sum_ez_orth]
  by_cases h : t = t0
  · subst h
    simp [hQ]
  · have hne : t0 - t ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    simp [hne, h]

/-- Additivity of the Fourier coefficient over a finite sum. -/
theorem fcoef_sum {ι : Type*} (S : Finset ι) (g : ι → ZMod Q → ℂ) (t : ZMod Q) :
    fcoef Q (fun x => ∑ i ∈ S, g i x) t = ∑ i ∈ S, fcoef Q (g i) t := by
  simp only [fcoef, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Homogeneity of the Fourier coefficient. -/
theorem fcoef_const_mul (c : ℂ) (g : ZMod Q → ℂ) (t : ZMod Q) :
    fcoef Q (fun x => c * g x) t = c * fcoef Q g t := by
  simp only [fcoef, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **`P_lo` is the exact spectral cutoff**: it keeps the frequencies in `S` and kills the rest. -/
theorem fcoef_lowProj (S : Finset (ZMod Q)) (f : ZMod Q → ℂ) (t : ZMod Q) :
    fcoef Q (lowProj S f) t = if t ∈ S then fcoef Q f t else 0 := by
  have hlin : fcoef Q (lowProj S f) t
      = ∑ t0 ∈ S, fcoef Q f t0 * fcoef Q (fun x => ez Q (t0 * x)) t := by
    rw [show lowProj S f = fun x => ∑ t0 ∈ S, fcoef Q f t0 * ez Q (t0 * x) from rfl,
      fcoef_sum]
    exact Finset.sum_congr rfl fun t0 _ => fcoef_const_mul _ _ _
  rw [hlin, Finset.sum_congr rfl fun t0 _ => by rw [fcoef_pure]]
  by_cases h : t ∈ S
  · rw [if_pos h]
    rw [Finset.sum_eq_single t]
    · simp
    · intro t0 _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact absurd h hnot
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun t0 ht0 => ?_
    have : t ≠ t0 := fun hEq => h (hEq ▸ ht0)
    simp [this]

/-! ## 3. First-moment functionals -/

/-- The total first moment `R_total(w, f) = ∑_x w(x) f(x)`. -/
def Rtotal (w f : ZMod Q → ℂ) : ℂ := ∑ x : ZMod Q, w x * f x

/-- The low-frequency first moment. -/
def Rlo (S : Finset (ZMod Q)) (w f : ZMod Q → ℂ) : ℂ := Rtotal w (lowProj S f)

/-- The high-frequency first moment — the authoritative physical residual `R_hi`. -/
def Rhi (S : Finset (ZMod Q)) (w f : ZMod Q → ℂ) : ℂ := Rtotal w (highProj S f)

/-- **FIRST-MOMENT REASSEMBLY** `R_total = R_lo + R_hi`. -/
theorem Rtotal_eq_Rlo_add_Rhi (S : Finset (ZMod Q)) (w f : ZMod Q → ℂ) :
    Rtotal w f = Rlo S w f + Rhi S w f := by
  rw [Rlo, Rhi, Rtotal, Rtotal, Rtotal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_add, low_add_high]

/-- Linearity of `R_lo`/`R_hi` in the low-frequency set: enlarging `S` moves mass from `R_hi`
to `R_lo` and changes nothing else. -/
theorem Rhi_eq_sub (S : Finset (ZMod Q)) (w f : ZMod Q → ℂ) :
    Rhi S w f = Rtotal w f - Rlo S w f := by
  rw [Rtotal_eq_Rlo_add_Rhi S w f]; ring

/-! ## 4. Mixed-quadratic firewall -/

/-- The **actual** quadratic identity, mixed term included. -/
theorem norm_sq_add (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * (starRingEnd ℂ) w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **MIXED-QUADRATIC FIREWALL.**  Pythagoras is *false* for a general low/high split of a first
moment: there are `L_lo, L_hi` with `|L_lo + L_hi|² ≠ |L_lo|² + |L_hi|²`.  Hence no theorem of
this bank may delete the cross term `2 Re(L_lo · conj L_hi)`. -/
theorem mixed_term_not_deletable :
    ∃ z w : ℂ, ‖z + w‖ ^ 2 ≠ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  refine ⟨1, 1, ?_⟩
  norm_num

/-- The two-point delta datum `f(0) = 1`, `f(1) = 0`, used as both weight and target. -/
def deltaTest : ZMod 2 → ℂ := fun x => if x = 0 then 1 else 0

theorem fcoef_deltaTest_zero : fcoef 2 deltaTest 0 = 1 / 2 := by
  rw [fcoef_zero_eq, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  norm_num [deltaTest]

theorem lowProj_deltaTest (x : ZMod 2) : lowProj {0} deltaTest x = 1 / 2 := by
  rw [lowProj, Finset.sum_singleton, fcoef_deltaTest_zero, zero_mul, ez_zero, mul_one]

theorem Rlo_deltaTest : Rlo ({0} : Finset (ZMod 2)) deltaTest deltaTest = 1 / 2 := by
  rw [Rlo, Rtotal, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl,
    Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), lowProj_deltaTest, lowProj_deltaTest]
  norm_num [deltaTest]

theorem Rhi_deltaTest : Rhi ({0} : Finset (ZMod 2)) deltaTest deltaTest = 1 / 2 := by
  rw [Rhi, Rtotal, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl,
    Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), highProj, highProj,
    lowProj_deltaTest, lowProj_deltaTest]
  norm_num [deltaTest]

theorem Rtotal_deltaTest : Rtotal (Q := 2) deltaTest deltaTest = 1 := by
  rw [Rtotal, show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl,
    Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  norm_num [deltaTest]

/-- The two functionals `R_lo`, `R_hi` really can have a nonvanishing cross term. -/
theorem Rlo_Rhi_cross_term_nonzero :
    ∃ (S : Finset (ZMod 2)) (w f : ZMod 2 → ℂ),
      2 * (Rlo S w f * (starRingEnd ℂ) (Rhi S w f)).re ≠ 0 := by
  refine ⟨{0}, deltaTest, deltaTest, ?_⟩
  rw [Rlo_deltaTest, Rhi_deltaTest]
  norm_num

/-- **NO PYTHAGORAS AT FIRST-MOMENT LEVEL.**  For explicit finite data,
`|R_total|² ≠ |R_lo|² + |R_hi|²`; the difference is exactly the mixed term of `norm_sq_add`. -/
theorem Rtotal_sq_ne_sum_of_squares :
    ∃ (S : Finset (ZMod 2)) (w f : ZMod 2 → ℂ),
      ‖Rtotal w f‖ ^ 2 ≠ ‖Rlo S w f‖ ^ 2 + ‖Rhi S w f‖ ^ 2 := by
  refine ⟨{0}, deltaTest, deltaTest, ?_⟩
  rw [Rlo_deltaTest, Rhi_deltaTest, Rtotal_deltaTest]
  norm_num

end

end Gate1B.R11.Frontier
