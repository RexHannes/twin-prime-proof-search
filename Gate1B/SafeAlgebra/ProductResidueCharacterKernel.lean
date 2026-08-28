/-
# Gate 1B v13 — product-residue / character convolution identity and the
centred kernel spectrum

**Status: PROVED_ALGEBRAIC.  FINITE ALGEBRA ONLY — no Weil bound anywhere.**

For a finite abelian unit group `G` with an explicit character system
(`MulCharSystem G Ch`, the repository convention) and weights `u, v : G → ℂ` we
define the weighted product-residue function

    g(r) = ∑_{h k = r} u(h) v(k)

and the product kernel `K(ψ) = U(ψ) V(ψ)` with `U(ψ) = ∑_h u(h) ψ(h)`.

Proved:

* `kernel_eq_sum_productResidue` : `K(ψ) = ∑_r g(r) ψ(r)`;
* `centredKernel` : `K°(1) = 0`, `K°(ψ) = K(ψ)` otherwise;
* `centredKernel_fourier_eq` : `∑_ψ K°(ψ) conj ψ(r) = |G| (g(r) − mean)`,
  where `mean = (∑_h u(h))(∑_k v(k))/|G|` — i.e. the exact eigenvalues of the
  convolution operator with `K°`;
* `centredKernel_convolution_eigen` : the eigenvector identity
  `T_{K°} e_r = λ_r e_r` for `e_r(χ) = χ(r)`;
* `centredSpectralRadius_isGreatest` : the spectral statement
  `max_r |λ_r| = |G| · max_r |g(r) − mean|`, attained.

Nothing analytic is claimed: no bound on `max_r |g(r) − mean|` is proved here.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteMultiplicativeCharacters

namespace Gate1B.SafeAlgebra

open Finset

namespace MulCharSystem

variable {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] (S : MulCharSystem G Ch)

/-- The weighted product-residue function `g(r) = ∑_{h k = r} u(h) v(k)`. -/
noncomputable def productResidueWeight (u v : G → ℂ) (r : G) : ℂ :=
  ∑ h : G, u h * v (h⁻¹ * r)

/-- The character transform `U(ψ) = ∑_h u(h) ψ(h)`. -/
noncomputable def weightTransform (u : G → ℂ) (psi : Ch) : ℂ := ∑ h : G, u h * S.chi psi h

/-- The product kernel `K(ψ) = U(ψ) V(ψ)`. -/
noncomputable def productKernel (u v : G → ℂ) (psi : Ch) : ℂ :=
  S.weightTransform u psi * S.weightTransform v psi

/-- **Convolution identity**: `K(ψ) = ∑_r g(r) ψ(r)`. -/
theorem kernel_eq_sum_productResidue (u v : G → ℂ) (psi : Ch) :
    S.productKernel u v psi = ∑ r : G, productResidueWeight u v r * S.chi psi r := by
  classical
  unfold productKernel weightTransform productResidueWeight
  rw [Finset.sum_mul_sum]
  have hswap : (∑ r : G, (∑ h : G, u h * v (h⁻¹ * r)) * S.chi psi r)
      = ∑ h : G, ∑ r : G, u h * v (h⁻¹ * r) * S.chi psi r := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.sum_mul]
  rw [hswap]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft h) (fun r : G => u h * v (h⁻¹ * r) * S.chi psi r)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hml : (Equiv.mulLeft h) k = h * k := rfl
  rw [hml]
  have hinv : h⁻¹ * (h * k) = k := by group
  rw [hinv, S.map_mul]
  ring

/-- The mean of the product-residue function. -/
noncomputable def productResidueMean (u v : G → ℂ) : ℂ :=
  ((∑ h : G, u h) * (∑ k : G, v k)) / (Fintype.card G : ℂ)

/-- The centred kernel: `K°(1) = 0`, `K°(ψ) = K(ψ)` otherwise. -/
noncomputable def centredKernel [CommGroup Ch] (u v : G → ℂ) (psi : Ch) : ℂ :=
  if psi = 1 then 0 else S.productKernel u v psi

/-- The claimed eigenvalue `λ_r = |G| (g(r) − mean)`. -/
noncomputable def centredEigenvalue (u v : G → ℂ) (r : G) : ℂ :=
  (Fintype.card G : ℂ) * (productResidueWeight u v r - productResidueMean u v)

variable [CommGroup Ch]

/-- The principal-index value of the kernel is `(∑u)(∑v)`. -/
theorem productKernel_one (hprin : ∀ g : G, S.chi (1 : Ch) g = 1) (u v : G → ℂ) :
    S.productKernel u v (1 : Ch) = (∑ h : G, u h) * (∑ k : G, v k) := by
  unfold productKernel weightTransform
  simp [hprin]

/-- **Exact eigenvalues of the centred convolution kernel**, by finite character
Fourier inversion. -/
theorem centredKernel_fourier_eq (hprin : ∀ g : G, S.chi (1 : Ch) g = 1)
    (u v : G → ℂ) (r : G) :
    ∑ psi : Ch, S.centredKernel u v psi * (starRingEnd ℂ) (S.chi psi r)
      = centredEigenvalue u v r := by
  classical
  have hfull : ∑ psi : Ch, S.productKernel u v psi * (starRingEnd ℂ) (S.chi psi r)
      = (Fintype.card G : ℂ) * productResidueWeight u v r := by
    have hstep : ∀ psi : Ch, S.productKernel u v psi * (starRingEnd ℂ) (S.chi psi r)
        = ∑ s : G, productResidueWeight u v s
            * (S.chi psi s * (starRingEnd ℂ) (S.chi psi r)) := by
      intro psi
      rw [S.kernel_eq_sum_productResidue u v psi, Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [Finset.sum_congr rfl fun psi _ => hstep psi, Finset.sum_comm]
    have hinner : ∀ s : G, ∑ psi : Ch, productResidueWeight u v s
        * (S.chi psi s * (starRingEnd ℂ) (S.chi psi r))
        = productResidueWeight u v s * (if s = r then (Fintype.card G : ℂ) else 0) := by
      intro s
      rw [← Finset.mul_sum, S.dual_orthogonality s r]
    rw [Finset.sum_congr rfl fun s _ => hinner s]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ r]
    simp [mul_comm]
  have h1 : S.centredKernel u v (1 : Ch) = 0 := by
    unfold centredKernel
    simp
  have hL : ∑ psi : Ch, S.centredKernel u v psi * (starRingEnd ℂ) (S.chi psi r)
      = ∑ psi ∈ Finset.univ.erase (1 : Ch),
          S.productKernel u v psi * (starRingEnd ℂ) (S.chi psi r) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun psi => S.centredKernel u v psi * (starRingEnd ℂ) (S.chi psi r))
      (Finset.mem_univ (1 : Ch))]
    rw [h1]
    simp only [zero_mul, add_zero]
    refine Finset.sum_congr rfl fun psi hpsi => ?_
    have hne : psi ≠ 1 := (Finset.mem_erase.mp hpsi).1
    unfold centredKernel
    simp [hne]
  have hR : ∑ psi : Ch, S.productKernel u v psi * (starRingEnd ℂ) (S.chi psi r)
      = (∑ psi ∈ Finset.univ.erase (1 : Ch),
          S.productKernel u v psi * (starRingEnd ℂ) (S.chi psi r))
        + S.productKernel u v 1 * (starRingEnd ℂ) (S.chi 1 r) :=
    (Finset.sum_erase_add Finset.univ
      (fun psi => S.productKernel u v psi * (starRingEnd ℂ) (S.chi psi r))
      (Finset.mem_univ (1 : Ch))).symm
  have hsplit : ∑ psi : Ch, S.centredKernel u v psi * (starRingEnd ℂ) (S.chi psi r)
      = (∑ psi : Ch, S.productKernel u v psi * (starRingEnd ℂ) (S.chi psi r))
        - S.productKernel u v (1 : Ch) * (starRingEnd ℂ) (S.chi (1 : Ch) r) := by
    rw [hL, hR]
    ring
  rw [hsplit, hfull, S.productKernel_one hprin, hprin r]
  unfold centredEigenvalue productResidueMean
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast Nat.cast_ne_zero.2 this.ne'
  simp only [map_one, mul_one]
  field_simp

/-- Index-inverse rule for the character system, derived from index
multiplicativity and the principal normalisation. -/
theorem chi_index_inv (hprin : ∀ g : G, S.chi (1 : Ch) g = 1)
    (hindex : ∀ (c d : Ch) (g : G), S.chi (c * d) g = S.chi c g * S.chi d g)
    (psi : Ch) (g : G) : S.chi psi⁻¹ g = (starRingEnd ℂ) (S.chi psi g) := by
  have h1 : S.chi psi g * S.chi psi⁻¹ g = 1 := by
    rw [← hindex, mul_inv_cancel, hprin]
  exact mul_left_cancel₀ (S.chi_ne_zero psi g) (h1.trans (S.chi_mul_conj psi g).symm)

/-- **Eigenvector identity for the centred convolution operator.**  With
`e_r(χ) = χ(r)`,

    ∑_{χ₂} K°(χ₁ χ₂⁻¹) e_r(χ₂) = λ_r · e_r(χ₁).
-/
theorem centredKernel_convolution_eigen (hprin : ∀ g : G, S.chi (1 : Ch) g = 1)
    (hindex : ∀ (c d : Ch) (g : G), S.chi (c * d) g = S.chi c g * S.chi d g)
    (u v : G → ℂ) (r : G) (x1 : Ch) :
    ∑ x2 : Ch, S.centredKernel u v (x1 * x2⁻¹) * S.chi x2 r
      = centredEigenvalue u v r * S.chi x1 r := by
  classical
  rw [← Equiv.sum_comp ((Equiv.inv Ch).trans (Equiv.mulRight x1))
    (fun x2 : Ch => S.centredKernel u v (x1 * x2⁻¹) * S.chi x2 r)]
  have hterm : ∀ psi : Ch,
      S.centredKernel u v (x1 * (((Equiv.inv Ch).trans (Equiv.mulRight x1)) psi)⁻¹)
          * S.chi (((Equiv.inv Ch).trans (Equiv.mulRight x1)) psi) r
        = (S.centredKernel u v psi * (starRingEnd ℂ) (S.chi psi r)) * S.chi x1 r := by
    intro psi
    have he : ((Equiv.inv Ch).trans (Equiv.mulRight x1)) psi = psi⁻¹ * x1 := rfl
    rw [he]
    have harg : x1 * (psi⁻¹ * x1)⁻¹ = psi := by group
    rw [harg, hindex, S.chi_index_inv hprin hindex]
    ring
  rw [Finset.sum_congr rfl fun psi _ => hterm psi, ← Finset.sum_mul,
    S.centredKernel_fourier_eq hprin u v r]

omit [DecidableEq G] in
/-- **Spectral statement.**  The largest eigenvalue modulus of the centred
convolution operator equals `|G| · max_r |g(r) − mean|`, and it is attained.
This replaces an operator-norm statement by the equivalent finite spectral one.
-/
theorem centredSpectralRadius_isGreatest (u v : G → ℂ) :
    IsGreatest {t : ℝ | ∃ r : G, t = ‖centredEigenvalue u v r‖}
      ((Fintype.card G : ℝ)
        * Finset.univ.sup' Finset.univ_nonempty
            (fun r : G => ‖productResidueWeight u v r - productResidueMean u v‖)) := by
  classical
  have hnorm : ∀ r : G, ‖centredEigenvalue u v r‖
      = (Fintype.card G : ℝ)
        * ‖productResidueWeight u v r - productResidueMean u v‖ := by
    intro r
    unfold centredEigenvalue
    rw [norm_mul]
    congr 1
    simp
  obtain ⟨r0, _, hr0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := G))
    (fun r : G => ‖productResidueWeight u v r - productResidueMean u v‖)
  constructor
  · exact ⟨r0, by rw [hnorm r0, ← hr0]⟩
  · rintro t ⟨r, rfl⟩
    rw [hnorm r]
    have hle : ‖productResidueWeight u v r - productResidueMean u v‖
        ≤ Finset.univ.sup' Finset.univ_nonempty
            (fun r : G => ‖productResidueWeight u v r - productResidueMean u v‖) :=
      Finset.le_sup' (fun r : G => ‖productResidueWeight u v r - productResidueMean u v‖)
        (Finset.mem_univ r)
    have hcard : (0 : ℝ) ≤ (Fintype.card G : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hle hcard

end MulCharSystem

end Gate1B.SafeAlgebra
