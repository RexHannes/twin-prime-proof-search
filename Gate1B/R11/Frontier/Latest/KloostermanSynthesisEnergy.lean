/-
# Gate1B / R11 / Frontier / Latest : the global Kloosterman energy ledger

Append-only module.  **Exact finite algebra and explicit countermodels only.**  Nothing here
asserts a source-energy contraction, and no open proposition is inhabited.

The current analytic frontier states that the simultaneous prime-`q` Kloosterman synthesis

* removes the artificial termwise `a/C` bookkeeping costs, **and**
* is only a *scaled isometry* on the mean-zero space, hence supplies **no** contraction.

Both halves are formalised:

* §1 the mean-zero space and the abstract scaled-isometry property;
* §2 `scaledIsometry_no_contraction` — a scaled isometry with scale `c ≥ 1` never contracts any
  nonzero mean-zero vector.  So an isometry statement can never be upgraded to a source-energy
  gain;
* §3 the **firewall** `per_mode_bound_does_not_close`: bounding each of `N` modes by `ε` gives
  only `N ε`, and this is attained; a per-mode KMS-type callable therefore does not close a
  global covariance whose target is smaller than `N ε`;
* §4 the exact Kloosterman-type Gram identity in the finite model (`affine_parseval` transported
  to a synthesis operator): the synthesis energy equals the scaled source residue energy.
-/
import Gate1B.R11.Frontier.Latest.AffineCharacterGram

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. Mean-zero vectors and scaled isometries -/

/-- The mean-zero space of the finite model. -/
def MeanZeroVec (l : ℕ) (f : ℕ → ℂ) : Prop := ∑ x ∈ range l, f x = 0

/-- The squared `ℓ²` energy on the finite model. -/
noncomputable def energy (l : ℕ) (f : ℕ → ℂ) : ℝ := ∑ x ∈ range l, ‖f x‖ ^ 2

/-- An operator is a *scaled isometry with scale `c` on the mean-zero space* if it multiplies the
energy of every mean-zero vector by exactly `c`. -/
def ScaledIsometryOnMeanZero (l : ℕ) (S : (ℕ → ℂ) → (ℕ → ℂ)) (c : ℝ) : Prop :=
  ∀ f : ℕ → ℂ, MeanZeroVec l f → energy l (S f) = c * energy l f

/-! ## 2. An isometry is not a contraction -/

/-- Energies are nonnegative. -/
theorem energy_nonneg (l : ℕ) (f : ℕ → ℂ) : 0 ≤ energy l f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Isometry firewall.**  A scaled isometry with scale `c ≥ 1` provides *no* contraction: the
output energy of every mean-zero vector is at least its input energy.  In particular no
source-energy gain can be extracted from the synthesis identity alone. -/
theorem scaledIsometry_no_contraction {l : ℕ} {S : (ℕ → ℂ) → (ℕ → ℂ)} {c : ℝ}
    (hS : ScaledIsometryOnMeanZero l S c) (hc : 1 ≤ c) (f : ℕ → ℂ) (hf : MeanZeroVec l f) :
    energy l f ≤ energy l (S f) := by
  rw [hS f hf]
  nlinarith [energy_nonneg l f]

/-- The same statement in the contrapositive form used in the ledger: a scale `c ≥ 1` is
incompatible with any strict contraction factor `θ < 1` on a mean-zero vector of positive
energy. -/
theorem no_contraction_factor {l : ℕ} {S : (ℕ → ℂ) → (ℕ → ℂ)} {c θ : ℝ}
    (hS : ScaledIsometryOnMeanZero l S c) (hc : 1 ≤ c) (hθ : θ < 1) (f : ℕ → ℂ)
    (hf : MeanZeroVec l f) (hpos : 0 < energy l f) :
    ¬ energy l (S f) ≤ θ * energy l f := by
  intro hcon
  rw [hS f hf] at hcon
  nlinarith

/-! ## 3. The per-mode / global firewall -/

/-- **Per-mode firewall.**  A bound of `ε` on each of `N` modes yields exactly `N ε` in the worst
case: the termwise (per-mode) callable is attained and therefore cannot close a global target
smaller than `N ε`.  This is the quantitative statement that termwise summation is
*nonclosing*. -/
theorem per_mode_bound_does_not_close (N : ℕ) (eps target : ℝ) (heps : 0 < eps)
    (htarget : target < N * eps) :
    ∃ a : ℕ → ℝ, (∀ i, |a i| ≤ eps) ∧ target < ∑ i ∈ range N, a i := by
  refine ⟨fun _ => eps, fun i => by rw [abs_of_pos heps], ?_⟩
  rw [Finset.sum_const, card_range, nsmul_eq_mul]
  exact htarget

/-- The ledger form: for every `N ≥ 1` and every per-mode budget `ε`, the summed wrapper is
nonclosing against any target below `N ε`; the deficiency factor is exactly `N`. -/
theorem summed_wrapper_nonclosing (N : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ a : ℕ → ℝ, (∀ i, |a i| ≤ eps) ∧ ∑ i ∈ range N, a i = (N : ℝ) * eps := by
  refine ⟨fun _ => eps, fun i => by rw [abs_of_pos heps], ?_⟩
  rw [Finset.sum_const, card_range, nsmul_eq_mul]

/-! ## 4. The synthesis Gram identity in the finite model -/

/-- The simultaneous synthesis operator of the finite model: the affine character transform. -/
noncomputable def synthesis (l : ℕ) (f : ℕ → ℂ) : ℕ → ℂ := affineTransform l f

/-- **Synthesis Gram identity / scaled isometry.**  The synthesis energy is exactly `ℓ` times
the source residue energy — on the whole space, hence in particular on the mean-zero space.
This is the exact content of `‖synthesis‖₂ = scaled source residue energy`; it contains no
contraction. -/
theorem synthesis_scaled_isometry {l : ℕ} (hl : 0 < l) :
    ScaledIsometryOnMeanZero l (synthesis l) (l : ℝ) := by
  intro f _
  exact affine_parseval hl f

/-- **The ledger firewall in its final form**: the synthesis is a scaled isometry with scale
`ℓ ≥ 1`, hence it never contracts a mean-zero source. -/
theorem synthesis_no_source_contraction {l : ℕ} (hl : 0 < l) (f : ℕ → ℂ)
    (hf : MeanZeroVec l f) : energy l f ≤ energy l (synthesis l f) :=
  scaledIsometry_no_contraction (synthesis_scaled_isometry hl) (by exact_mod_cast hl) f hf

end Gate1B.R11.Frontier.Latest
