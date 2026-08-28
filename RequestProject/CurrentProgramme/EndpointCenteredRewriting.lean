import RequestProject.CurrentProgramme.EndpointTwoByTwoSplit
import RequestProject.CurrentProgramme.EndpointCentering

/-!
# Phase B5 · centered `2|2` rewriting (source-neutral finite algebra)

For an **abstract** line coefficient `Z(u, ℓ, k)` and an **abstract** residue
kernel `D ℓ u₁ u₂` (the intended instantiation is the centered kernel
`Centering.centeredKernelInt`, but nothing here uses any property of it), the
centered endpoint form is

  `R_cent = ∑_ℓ ∑_{u₁,u₂} a₄(u₁) conj(a₄(u₂)) D_ℓ(u₁,u₂) Z(u₁,ℓ,k) conj Z(u₂,ℓ,k)`.

`rCent_two_by_two` proves the **exact** finite rewriting obtained by inserting
the `2|2` split `a₄ = α ⋆ γ` of `EndpointTwoByTwoSplit`:

  `R_cent = ∑_ℓ ∑_{m,r,m',s} α(m)γ(r) conj(α(m')γ(s)) D_ℓ(mr, m's)
                Z(mr,ℓ,k) conj Z(m's,ℓ,k)`.

No source is used, no estimate is made, and no property of `D` or `Z` is
assumed.  The only hypothesis is the support-coverage hypothesis inherited from
the split.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace CenteredRewriting

open Finset TwoByTwo

/-- The centered endpoint form, for abstract kernel `D` and abstract line
coefficient `Z`. -/
noncomputable def rCent (Ls : Finset ℕ) (Us : Finset ℤ) (a4 : ℤ → ℂ)
    (D : ℕ → ℤ → ℤ → ℂ) (Z : ℤ → ℕ → ℤ → ℂ) (k : ℤ) : ℂ :=
  ∑ l ∈ Ls, ∑ u₁ ∈ Us, ∑ u₂ ∈ Us,
    a4 u₁ * (starRingEnd ℂ) (a4 u₂) * D l u₁ u₂ * Z u₁ l k *
      (starRingEnd ℂ) (Z u₂ l k)

/-- **Centered `2|2` rewriting.**  Exact finite identity. -/
theorem rCent_two_by_two (Ls : Finset ℕ) (Us Pm Pr : Finset ℤ) (α γ : ℤ → ℂ)
    (D : ℕ → ℤ → ℤ → ℂ) (Z : ℤ → ℕ → ℤ → ℂ) (k : ℤ)
    (hcov : ∀ m ∈ Pm, ∀ r ∈ Pr, m * r ∈ Us) :
    rCent Ls Us (conv2 Pm Pr α γ) D Z k
      = ∑ l ∈ Ls, ∑ m ∈ Pm, ∑ r ∈ Pr, ∑ m' ∈ Pm, ∑ s ∈ Pr,
          α m * γ r * (starRingEnd ℂ) (α m' * γ s) * D l (m * r) (m' * s) *
            Z (m * r) l k * (starRingEnd ℂ) (Z (m' * s) l k) := by
  classical
  refine Finset.sum_congr rfl fun l _ => ?_
  -- inner `u₂`-sum, for each fixed `u₁`
  have inner : ∀ u₁ : ℤ,
      ∑ u₂ ∈ Us, (starRingEnd ℂ) (conv2 Pm Pr α γ u₂) *
          (D l u₁ u₂ * Z u₁ l k * (starRingEnd ℂ) (Z u₂ l k))
        = ∑ m' ∈ Pm, ∑ s ∈ Pr, (starRingEnd ℂ) (α m' * γ s) *
            (D l u₁ (m' * s) * Z u₁ l k *
              (starRingEnd ℂ) (Z (m' * s) l k)) := by
    intro u₁
    exact sum_conv2_conj_weight Pm Pr Us α γ
      (fun u₂ => D l u₁ u₂ * Z u₁ l k * (starRingEnd ℂ) (Z u₂ l k)) hcov
  have step1 : ∀ u₁ : ℤ,
      ∑ u₂ ∈ Us, conv2 Pm Pr α γ u₁ * (starRingEnd ℂ) (conv2 Pm Pr α γ u₂) *
          D l u₁ u₂ * Z u₁ l k * (starRingEnd ℂ) (Z u₂ l k)
        = conv2 Pm Pr α γ u₁ *
            (∑ m' ∈ Pm, ∑ s ∈ Pr, (starRingEnd ℂ) (α m' * γ s) *
              (D l u₁ (m' * s) * Z u₁ l k *
                (starRingEnd ℂ) (Z (m' * s) l k))) := by
    intro u₁
    rw [← inner u₁, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u₂ _ => by ring
  rw [Finset.sum_congr rfl (fun u₁ (_ : u₁ ∈ Us) => step1 u₁)]
  -- outer `u₁`-sum
  rw [sum_conv2_weight Pm Pr Us α γ
    (fun u₁ => ∑ m' ∈ Pm, ∑ s ∈ Pr, (starRingEnd ℂ) (α m' * γ s) *
      (D l u₁ (m' * s) * Z u₁ l k * (starRingEnd ℂ) (Z (m' * s) l k))) hcov]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

end CenteredRewriting
end CurrentProgramme
end TwinPrimeProject
