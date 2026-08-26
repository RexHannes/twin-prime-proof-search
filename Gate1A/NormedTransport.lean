/-
# Gate-1A §18 and §19: the two abstract *sufficient* theorems

Both theorems in this file are fully proved.  What remains open in the
programme is **not** these implications, but the assertion that the actual
Gate-1A source satisfies their hypotheses; those live in
`Gate1A/SourceInterfaces.lean`.

* §18 `normed_transported_curvature` — the corrected normed source-transport
  statement.  The normalisation hypothesis is **explicit**:
  `S · Nuclear² ≤ B_nat`, where `Nuclear` is the genuine `ℓ¹` nuclear mass
  `∑_λ ∑_X |a_λ(X)|` and `B_nat` is the *conservative natural* scale.
  Hostile test 11: `B_nat` is deliberately **not** identified with any
  diagonal `ℓ²` scale — the countermodels in `Gate1A/NuclearCountermodels.lean`
  show that identification is false.

* §19 `nuclear_projective_pushforward_bound` — if the projective packet
  admits a nuclear decomposition whose `ℓ¹`-weighted `ℓ²` mass is at most
  `√N_diag`, then under factor multiplicity `≤ τ` the projective energy is at
  most `τ · N_diag`.  Proved from `projective_crossed_convolution`'s
  multiplicity bound plus Minkowski.
-/
import Mathlib
import Gate1A.MovingFamily
import Gate1A.ProjectivePacket

namespace Gate1A

namespace NormedTransport

open Finset

/-! ### An `ℓ²` Minkowski inequality for finite families -/

/-- Minkowski: the `ℓ²` norm of a finite sum is at most the sum of the
`ℓ²` norms. -/
theorem l2_sum_le {ι Lam : Type*} [Fintype ι] [Fintype Lam] (F : Lam → ι → ℂ) :
    Real.sqrt (∑ x, ‖∑ l, F l x‖ ^ 2) ≤ ∑ l, Real.sqrt (∑ x, ‖F l x‖ ^ 2) := by
  classical
  have key : ∀ f : ι → ℂ, Real.sqrt (∑ x, ‖f x‖ ^ 2)
      = ‖(WithLp.toLp 2 f : EuclideanSpace ℂ ι)‖ := by
    intro f
    rw [EuclideanSpace.norm_eq]
  rw [key]
  have hsum : (WithLp.toLp 2 (fun x => ∑ l, F l x) : EuclideanSpace ℂ ι)
      = ∑ l, (WithLp.toLp 2 (F l) : EuclideanSpace ℂ ι) := by
    ext x
    simp
  rw [hsum]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun l _ => (key (F l)).symm

/-! ### §18: the normed source-transport theorem -/

section Transport

variable {P X Lam : Type*} [Fintype P] [Fintype X] [DecidableEq X] [Fintype Lam]
variable {Xi : P → Type*} [∀ p, DecidableEq (Xi p)] [∀ p, Fintype (Xi p)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The genuine `ℓ¹` nuclear mass of the transported coefficients. -/
noncomputable def nuclearMass (a : Lam → X → ℂ) : ℝ := ∑ l : Lam, ∑ x : X, ‖a l x‖

/-- The transported vector `c_r(X) = ∑_λ a_λ(X) u_λ(r,X)`. -/
noncomputable def transported (a : Lam → X → ℂ) (u : Lam → P → X → E) :
    ∀ _ : P, X → E :=
  fun p x => ∑ l : Lam, a l x • u l p x

/-- The pointwise envelope of the transported vectors. -/
noncomputable def envelope (a : Lam → X → ℂ) : X → ℝ := fun x => ∑ l : Lam, ‖a l x‖

omit [Fintype X] [DecidableEq X] in
theorem envelope_nonneg (a : Lam → X → ℂ) (x : X) : 0 ≤ envelope a x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

omit [Fintype P] [Fintype X] [DecidableEq X] in
theorem transported_norm_le (a : Lam → X → ℂ) (u : Lam → P → X → E)
    (hu : ∀ l p x, ‖u l p x‖ ≤ 1) (p : P) (x : X) :
    ‖transported a u p x‖ ≤ envelope a x := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_smul]
  calc ‖a l x‖ * ‖u l p x‖ ≤ ‖a l x‖ * 1 :=
        mul_le_mul_of_nonneg_left (hu l p x) (norm_nonneg _)
    _ = ‖a l x‖ := mul_one _

omit [DecidableEq X] in
theorem sum_envelope_eq_nuclearMass (a : Lam → X → ℂ) :
    (∑ x : X, envelope a x) = nuclearMass a := by
  simp only [nuclearMass, envelope]
  exact Finset.sum_comm

/-- **`normed_transported_curvature`** (§18, A14).

Off-diagonal ("nonzero-curvature") collision energy of the transported main
modes, under the **explicit** normalisation `S · Nuclear² ≤ B_nat`:

`E_off ≤ (D / S) · B_nat`.

Here `S = #P` is the moving-family size, `D` the pairwise collision
codegree, and `Nuclear = ∑_λ ∑_X |a_λ(X)|` the genuine `ℓ¹` nuclear mass.
The theorem is false if `B_nat` is silently replaced by a diagonal `ℓ²`
scale. -/
theorem normed_transported_curvature
    (a : Lam → X → ℂ) (u : Lam → P → X → E) (pr : ∀ p, X → Xi p)
    (D Bnat : ℝ) (hD0 : 0 ≤ D) (hS : 0 < (Fintype.card P : ℝ))
    (hu : ∀ l p x, ‖u l p x‖ ≤ 1)
    (hD : ∀ x y : X, x ≠ y →
      ((univ.filter (fun p : P => pr p x = pr p y)).card : ℝ) ≤ D)
    (hnorm : (Fintype.card P : ℝ) * nuclearMass a ^ 2 ≤ Bnat) :
    collisionEnergy (transported a u) pr
        - (∑ p : P, ∑ x : X, ‖transported a u p x‖ ^ 2)
      ≤ (D / (Fintype.card P : ℝ)) * Bnat := by
  have hoff := offdiag_energy_le_D_mul_coherence (transported a u) pr (envelope a) D
    (fun p x => transported_norm_le a u hu p x) (envelope_nonneg a) hD0 hD
  refine hoff.trans ?_
  rw [coherenceNumerator, sum_envelope_eq_nuclearMass]
  rw [div_mul_eq_mul_div, le_div_iff₀ hS]
  calc D * nuclearMass a ^ 2 * (Fintype.card P : ℝ)
      = D * ((Fintype.card P : ℝ) * nuclearMass a ^ 2) := by ring
    _ ≤ D * Bnat := mul_le_mul_of_nonneg_left hnorm hD0

end Transport

/-! ### §19: the nuclear projective pushforward bound -/

section Projective

open ProjectivePacket

variable {Z L W I J Lam : Type*}
variable [Fintype Z] [Fintype L] [Fintype W] [DecidableEq W] [Fintype I] [Fintype J]
variable [Fintype Lam]

/-- The projective energy of a nuclear packet
`C = ∑_λ α_λ · (A_λ ⊗ conj B_λ)`. -/
noncomputable def nuclearProjectiveEnergy (mulZL : Z → L → W) (alpha : Lam → ℂ)
    (A : Lam → Z → I → ℂ) (B : Lam → L → J → ℂ) : ℝ :=
  ∑ w : W, ∑ i : I, ∑ j : J,
    ‖∑ l : Lam, alpha l * crossedPacket mulZL (A l) (B l) w i j‖ ^ 2

/-- **`nuclear_projective_pushforward_bound`** (§19).

If the projective packet has a nuclear decomposition with
`∑_λ |α_λ| ‖A_λ‖₂ ‖B_λ‖₂ ≤ √N_diag`, and every `w` has at most `τ` factor
representations, then the projective energy is at most `τ · N_diag`. -/
theorem nuclear_projective_pushforward_bound (mulZL : Z → L → W) (alpha : Lam → ℂ)
    (A : Lam → Z → I → ℂ) (B : Lam → L → J → ℂ) (tau Ndiag : ℝ)
    (htau0 : 0 ≤ tau) (hNdiag : 0 ≤ Ndiag)
    (htau : ∀ w : W, ((fibre mulZL w).card : ℝ) ≤ tau)
    (hnuc : (∑ l : Lam, ‖alpha l‖
        * Real.sqrt (∑ z : Z, ∑ i : I, ‖A l z i‖ ^ 2)
        * Real.sqrt (∑ x : L, ∑ j : J, ‖B l x j‖ ^ 2)) ≤ Real.sqrt Ndiag) :
    nuclearProjectiveEnergy mulZL alpha A B ≤ tau * Ndiag := by
  classical
  set SA : Lam → ℝ := fun l => ∑ z : Z, ∑ i : I, ‖A l z i‖ ^ 2 with hSA
  set SB : Lam → ℝ := fun l => ∑ x : L, ∑ j : J, ‖B l x j‖ ^ 2 with hSB
  have hSA0 : ∀ l, 0 ≤ SA l := fun l =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSB0 : ∀ l, 0 ≤ SB l := fun l =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- rewrite the triple sums as sums over the product index
  have hconv : ∀ G : W → I → J → ℂ,
      (∑ w : W, ∑ i : I, ∑ j : J, ‖G w i j‖ ^ 2)
        = ∑ p : W × I × J, ‖G p.1 p.2.1 p.2.2‖ ^ 2 := by
    intro G
    simp [Fintype.sum_prod_type]
  set F : Lam → W × I × J → ℂ :=
    fun l p => alpha l * crossedPacket mulZL (A l) (B l) p.1 p.2.1 p.2.2 with hF
  have hE : nuclearProjectiveEnergy mulZL alpha A B
      = ∑ p : W × I × J, ‖∑ l : Lam, F l p‖ ^ 2 := by
    rw [nuclearProjectiveEnergy]
    exact hconv _
  have hEnn : 0 ≤ nuclearProjectiveEnergy mulZL alpha A B := by
    rw [hE]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the ℓ² norm of each nuclear term
  have hterm : ∀ l : Lam, Real.sqrt (∑ p : W × I × J, ‖F l p‖ ^ 2)
      ≤ Real.sqrt tau * (‖alpha l‖ * (Real.sqrt (SA l) * Real.sqrt (SB l))) := by
    intro l
    have hpe : projectiveEnergy mulZL (A l) (B l) ≤ tau * SA l * SB l :=
      projective_energy_le_of_factorMultiplicity mulZL (A l) (B l) tau htau
    have hfact : (∑ p : W × I × J, ‖F l p‖ ^ 2)
        = ‖alpha l‖ ^ 2 * projectiveEnergy mulZL (A l) (B l) := by
      rw [projectiveEnergy, hconv, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by
        rw [hF]; simp [mul_pow]
    rw [hfact, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have h1 : Real.sqrt (projectiveEnergy mulZL (A l) (B l))
        ≤ Real.sqrt (tau * SA l * SB l) := Real.sqrt_le_sqrt hpe
    have h2 : Real.sqrt (tau * SA l * SB l)
        = Real.sqrt tau * Real.sqrt (SA l) * Real.sqrt (SB l) := by
      rw [Real.sqrt_mul (mul_nonneg htau0 (hSA0 l)), Real.sqrt_mul htau0]
    calc ‖alpha l‖ * Real.sqrt (projectiveEnergy mulZL (A l) (B l))
        ≤ ‖alpha l‖ * (Real.sqrt tau * Real.sqrt (SA l) * Real.sqrt (SB l)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = Real.sqrt tau * (‖alpha l‖ * (Real.sqrt (SA l) * Real.sqrt (SB l))) := by
          ring
  -- Minkowski
  have hmink : Real.sqrt (nuclearProjectiveEnergy mulZL alpha A B)
      ≤ Real.sqrt tau * Real.sqrt Ndiag := by
    rw [hE]
    refine (l2_sum_le F).trans ?_
    refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine le_trans (le_of_eq ?_) hnuc
    exact Finset.sum_congr rfl fun l _ => by ring
  have hfin : nuclearProjectiveEnergy mulZL alpha A B
      ≤ (Real.sqrt tau * Real.sqrt Ndiag) ^ 2 := by
    have := Real.sq_sqrt hEnn
    nlinarith [Real.sqrt_nonneg (nuclearProjectiveEnergy mulZL alpha A B),
      Real.sqrt_nonneg tau, Real.sqrt_nonneg Ndiag, hmink]
  refine hfin.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt htau0, Real.sq_sqrt hNdiag]

end Projective

end NormedTransport

end Gate1A
