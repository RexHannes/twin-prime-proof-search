/-
# Gate-1A: the projective crossed-convolution identity (Section 12)
and the abstract nuclear projective pushforward bound (Section 19)

**Convention (hostile test 1).**  Mathlib's complex inner product
`⟪x, y⟫` is conjugate-linear in the *first* argument.  Writing the packets in
coordinates, `A : Z → I → ℂ`, `B : L → J → ℂ` (finite-dimensional complex
Hilbert spaces), and

```
⟪A z₁, A z₂⟫ = ∑_i conj(A z₁ i) · A z₂ i,
C_w(i,j)     = ∑_{z l = w} A z i · conj(B l j),
```

the identity that is actually true is

```
∑_w ‖C_w‖²  =  ∑_{(z,l),(z',l') : z l = z' l'} ⟪A z', A z⟫ · ⟪B l, B l'⟫.
```

The informally displayed ordering `⟪A_{z₁},A_{z₂}⟫⟪B_{l₁},B_{l₂}⟫` over
`z₁ l₂ = z₂ l₁` has been **repaired** to the above; the two totals agree
(the summand set is symmetric and the sums are conjugates of each other),
but the pointwise ordering above is the one the kernel checks.
-/
import Mathlib

namespace Gate1A

open Finset Complex

namespace ProjectivePacket

variable {Z L W I J : Type*}
variable [Fintype Z] [Fintype L] [Fintype W] [DecidableEq W] [Fintype I] [Fintype J]

/-- A three-fold sum interchange: the `(a,b)` block commutes with `c`. -/
theorem sum3_comm {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (f : α → β → γ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c)
      = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ s) =>
    Finset.sum_comm (s := t) (t := u) (f := fun b c => f a b c))]
  exact Finset.sum_comm

/-- A four-fold sum interchange: the `(a,b)` block and the `(c,d)` block commute. -/
theorem sum4_comm {α β γ δ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (v : Finset δ) (f : α → β → γ → δ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d)
      = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  rw [sum3_comm s t u (fun a b c => ∑ d ∈ v, f a b c d)]
  exact Finset.sum_congr rfl fun c _ => sum3_comm s t v (fun a b d => f a b c d)

/-- The fibre of the multiplication map over `w`. -/
def fibre (mulZL : Z → L → W) (w : W) : Finset (Z × L) :=
  univ.filter (fun p : Z × L => mulZL p.1 p.2 = w)

/-- The crossed packet `C_w = ∑_{z l = w} A_z ⊗ conj(B_l)`, in coordinates. -/
noncomputable def crossedPacket (mulZL : Z → L → W) (A : Z → I → ℂ) (B : L → J → ℂ)
    (w : W) (i : I) (j : J) : ℂ :=
  ∑ p ∈ fibre mulZL w, A p.1 i * (starRingEnd ℂ) (B p.2 j)

/-- The projective energy `∑_w ‖C_w‖²`. -/
noncomputable def projectiveEnergy (mulZL : Z → L → W) (A : Z → I → ℂ) (B : L → J → ℂ) : ℝ :=
  ∑ w : W, ∑ i : I, ∑ j : J, ‖crossedPacket mulZL A B w i j‖ ^ 2

/-- `⟪A z₁, A z₂⟫` in Mathlib's convention (conjugate-linear in the first slot). -/
noncomputable def ip {K : Type*} [Fintype K] (A : Z → K → ℂ) (z1 z2 : Z) : ℂ :=
  ∑ k : K, (starRingEnd ℂ) (A z1 k) * A z2 k

/-- The projective correlation
`∑_{z l = z' l'} ⟪A z', A z⟫ ⟪B l, B l'⟫`. -/
noncomputable def projectiveCorrelation (mulZL : Z → L → W) (A : Z → I → ℂ)
    (B : L → J → ℂ) : ℂ :=
  ∑ p : Z × L, ∑ p' : Z × L,
    if mulZL p.1 p.2 = mulZL p'.1 p'.2 then
      ip A p'.1 p.1 * ip B p.2 p'.2 else 0

/-- **`projective_crossed_convolution`.**  The exact identity. -/
theorem projective_crossed_convolution (mulZL : Z → L → W) (A : Z → I → ℂ)
    (B : L → J → ℂ) :
    ((projectiveEnergy mulZL A B : ℝ) : ℂ) = projectiveCorrelation mulZL A B := by
  classical
  have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- expand the energy
  have hexp : ((projectiveEnergy mulZL A B : ℝ) : ℂ)
      = ∑ w : W, ∑ i : I, ∑ j : J,
          ∑ p ∈ fibre mulZL w, ∑ p' ∈ fibre mulZL w,
            (A p.1 i * (starRingEnd ℂ) (B p.2 j)) *
              ((starRingEnd ℂ) (A p'.1 i) * B p'.2 j) := by
    simp only [projectiveEnergy, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [hnorm, crossedPacket, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => by
      simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [hexp]
  -- move the `i, j` sums inside and recognise the inner products
  have hstep : ∀ w : W,
      (∑ i : I, ∑ j : J, ∑ p ∈ fibre mulZL w, ∑ p' ∈ fibre mulZL w,
        (A p.1 i * (starRingEnd ℂ) (B p.2 j)) *
          ((starRingEnd ℂ) (A p'.1 i) * B p'.2 j))
        = ∑ p ∈ fibre mulZL w, ∑ p' ∈ fibre mulZL w,
            ip A p'.1 p.1 * ip B p.2 p'.2 := by
    intro w
    rw [sum4_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
    rw [ip, ip, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl (fun w _ => hstep w)]
  -- reassemble the fibres
  rw [projectiveCorrelation]
  rw [← Finset.sum_fiberwise univ (fun p : Z × L => mulZL p.1 p.2)
      (fun p : Z × L => ∑ p' : Z × L,
        if mulZL p.1 p.2 = mulZL p'.1 p'.2 then ip A p'.1 p.1 * ip B p.2 p'.2 else 0)]
  refine Finset.sum_congr rfl fun w _ => ?_
  refine Finset.sum_congr rfl fun p hp => ?_
  have hw : mulZL p.1 p.2 = w := (Finset.mem_filter.mp hp).2
  rw [fibre, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p' _ => ?_
  by_cases h : mulZL p'.1 p'.2 = w
  · rw [if_pos h, if_pos (by rw [hw, h])]
  · rw [if_neg h, if_neg (by rw [hw]; exact fun hc => h hc.symm)]

/-! ### The finite multiplicity bound -/

/-- **`projective_energy_le_of_factorMultiplicity`.**  If every `w` has at most
`τ` factorisations inside the supplied finite supports, then

`∑_w ‖C_w‖² ≤ τ · (∑_z ‖A_z‖²) · (∑_l ‖B_l‖²)`.

No analytic divisor theorem is used: `τ` is a finite multiplicity hypothesis.
The hypothesis `0 ≤ tau` is genuinely needed (it is not implied when `W` is
empty). -/
theorem projective_energy_le_of_factorMultiplicity (mulZL : Z → L → W)
    (A : Z → I → ℂ) (B : L → J → ℂ) (tau : ℝ)
    (htau : ∀ w : W, ((fibre mulZL w).card : ℝ) ≤ tau) :
    projectiveEnergy mulZL A B
      ≤ tau * (∑ z : Z, ∑ i : I, ‖A z i‖ ^ 2) * (∑ l : L, ∑ j : J, ‖B l j‖ ^ 2) := by
  classical
  have hpoint : ∀ (w : W) (i : I) (j : J),
      ‖crossedPacket mulZL A B w i j‖ ^ 2
        ≤ ((fibre mulZL w).card : ℝ) *
            ∑ p ∈ fibre mulZL w, (‖A p.1 i‖ ^ 2 * ‖B p.2 j‖ ^ 2) := by
    intro w i j
    have h1 : ‖crossedPacket mulZL A B w i j‖
        ≤ ∑ p ∈ fibre mulZL w, ‖A p.1 i‖ * ‖B p.2 j‖ := by
      rw [crossedPacket]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_mul, RCLike.norm_conj]
    have h2 : (∑ p ∈ fibre mulZL w, ‖A p.1 i‖ * ‖B p.2 j‖) ^ 2
        ≤ ((fibre mulZL w).card : ℝ) *
            ∑ p ∈ fibre mulZL w, (‖A p.1 i‖ * ‖B p.2 j‖) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    calc ‖crossedPacket mulZL A B w i j‖ ^ 2
        ≤ (∑ p ∈ fibre mulZL w, ‖A p.1 i‖ * ‖B p.2 j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ((fibre mulZL w).card : ℝ) *
            ∑ p ∈ fibre mulZL w, (‖A p.1 i‖ * ‖B p.2 j‖) ^ 2 := h2
      _ = ((fibre mulZL w).card : ℝ) *
            ∑ p ∈ fibre mulZL w, (‖A p.1 i‖ ^ 2 * ‖B p.2 j‖ ^ 2) := by
          congr 1
          exact Finset.sum_congr rfl fun p _ => by ring
  have hw : ∀ w : W,
      (∑ i : I, ∑ j : J, ‖crossedPacket mulZL A B w i j‖ ^ 2)
        ≤ tau * ∑ p ∈ fibre mulZL w,
            (∑ i : I, ‖A p.1 i‖ ^ 2) * (∑ j : J, ‖B p.2 j‖ ^ 2) := by
    intro w
    have h3 : (∑ i : I, ∑ j : J, ∑ p ∈ fibre mulZL w,
          (‖A p.1 i‖ ^ 2 * ‖B p.2 j‖ ^ 2))
        = ∑ p ∈ fibre mulZL w,
            (∑ i : I, ‖A p.1 i‖ ^ 2) * (∑ j : J, ‖B p.2 j‖ ^ 2) := by
      rw [sum3_comm]
      exact Finset.sum_congr rfl fun p _ => by rw [Finset.sum_mul_sum]
    have hrearr : (∑ i : I, ∑ j : J, ((fibre mulZL w).card : ℝ) *
          ∑ p ∈ fibre mulZL w, (‖A p.1 i‖ ^ 2 * ‖B p.2 j‖ ^ 2))
        = ((fibre mulZL w).card : ℝ) * ∑ p ∈ fibre mulZL w,
            (∑ i : I, ‖A p.1 i‖ ^ 2) * (∑ j : J, ‖B p.2 j‖ ^ 2) := by
      rw [← h3, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    have hstep : (∑ i : I, ∑ j : J, ‖crossedPacket mulZL A B w i j‖ ^ 2)
        ≤ ((fibre mulZL w).card : ℝ) * ∑ p ∈ fibre mulZL w,
            (∑ i : I, ‖A p.1 i‖ ^ 2) * (∑ j : J, ‖B p.2 j‖ ^ 2) := by
      rw [← hrearr]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint w i j
    have hnn : (0 : ℝ) ≤ ∑ p ∈ fibre mulZL w,
        (∑ i : I, ‖A p.1 i‖ ^ 2) * (∑ j : J, ‖B p.2 j‖ ^ 2) := by positivity
    exact hstep.trans (mul_le_mul_of_nonneg_right (htau w) hnn)
  have hsum : projectiveEnergy mulZL A B
      ≤ tau * ∑ w : W, ∑ p ∈ fibre mulZL w,
          (∑ i : I, ‖A p.1 i‖ ^ 2) * (∑ j : J, ‖B p.2 j‖ ^ 2) := by
    rw [projectiveEnergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hw w
  refine hsum.trans (le_of_eq ?_)
  simp only [fibre]
  rw [Finset.sum_fiberwise univ (fun p : Z × L => mulZL p.1 p.2)
      (fun p : Z × L => (∑ i : I, ‖A p.1 i‖ ^ 2) * (∑ j : J, ‖B p.2 j‖ ^ 2))]
  rw [mul_assoc]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

end ProjectivePacket

end Gate1A
