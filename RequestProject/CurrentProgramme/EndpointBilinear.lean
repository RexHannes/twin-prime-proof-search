import Mathlib.Tactic
import RequestProject.CurrentProgramme.RankOneLineAlgebra

/-!
# Phase A5 / A6 / A8 · exact endpoint bilinear decomposition

**Identities only.**  Nothing in this module is an estimate, and no stratum is
bounded.

## Contents

* `residueSource` — the weighted residue source

    `A_{ℓ,a,k} = ∑_{u ∼ U, u ≡ -2a⁻¹ (mod ℓ)} a₄(u) Z_{u,ℓ}(k)`,

  written with a finite source set plus a residue predicate (exact dyadic
  intervals are inconvenient in Lean, as anticipated by A5).  The weight
  `a₄(u) Z_{u,ℓ}(k)` is **load-bearing** and is never replaced by an
  unweighted average over `a` — see `unweighted_average_is_not_the_source`.

* `endpointBilinearParent` — the exact finite bilinear parent

    `(1/H) ∑_k ∑_ℓ ∑*_{a mod ℓ} A_{ℓ,a,k} conj(E_{ℓ,a,k})`,

  a **source dictionary** statement.

* `residueEnergy_expansion` — expanding `∑_a |A_{ℓ,a,k}|²` produces exactly the
  pair condition `u₁ ≡ u₂ (mod ℓ)`.

* `residueEnergy_split` — the exact split into the two energy children
  `u₁ = u₂` and `u₁ ≠ u₂`.

* `offdiagEnergy` — the exact off-diagonal energy source object, the target of
  the open interface `RankOneEndpointUOffdiagInput`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace EndpointBilinear

open Finset RankOne

variable {ι κ : Type*}

/-! ## 1. Fiberwise energy expansion (source-free finite algebra) -/

/-- **Fiber expansion.**  For a finite source set `U`, a residue map `r` whose
values lie in `Aset`, and any weight `f`,

  `∑_a |∑_{u : r u = a} f u|² = ∑_{(u₁,u₂) : r u₁ = r u₂} f u₁ conj(f u₂)`.

This is the exact mechanism that turns the `a`-average of `|A|²` into the pair
condition. -/
theorem sum_fiber_energy [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (r : ι → κ) (Aset : Finset κ) (f : ι → ℂ)
    (hcov : ∀ u ∈ U, r u ∈ Aset) :
    ∑ a ∈ Aset, (∑ u ∈ U.filter (fun u => r u = a), f u) *
        (starRingEnd ℂ) (∑ u ∈ U.filter (fun u => r u = a), f u)
      = ∑ p ∈ (U ×ˢ U).filter (fun p => r p.1 = r p.2),
          f p.1 * (starRingEnd ℂ) (f p.2) := by
  classical
  have hmaps : ∀ p ∈ (U ×ˢ U).filter (fun p : ι × ι => r p.1 = r p.2), r p.1 ∈ Aset := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact hcov _ hp.1.1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hset :
      ((U ×ˢ U).filter (fun p : ι × ι => r p.1 = r p.2)).filter (fun p => r p.1 = a)
        = (U.filter (fun u => r u = a)) ×ˢ (U.filter (fun u => r u = a)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h1, h4⟩, ⟨h2, by rw [← h3]; exact h4⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨⟨⟨h1, h3⟩, by rw [h2, h4]⟩, h2⟩
  rw [hset, Finset.sum_product, map_sum, Finset.sum_mul_sum]

/-! ## 2. The endpoint residue source -/

section Source

variable (n : ℕ)

/-- The residue map `u ↦ u mod ℓ`, with `ℓ` presented as `n : ℕ`. -/
def resMap (u : ℤ) : ZMod n := (u : ZMod n)

/-- **A5, the weighted residue source.**

  `A_{ℓ,a,k} = ∑_{u ∈ U, u ≡ a (mod ℓ)} a₄(u) · Z_{u,ℓ}(k)`.

Here `a` is the residue representative; at the endpoint it is `-2·(·)⁻¹` of
the `v₀`-residue, by `RankOne.endpoint_residue_zmod`.  The weight
`a₄(u) Z_{u,ℓ}(k)` is carried explicitly and is load-bearing. -/
noncomputable def residueSource (U : Finset ℤ) (a4 : ℤ → ℂ) (Z : ℤ → ℂ)
    (a : ZMod n) : ℂ :=
  ∑ u ∈ U.filter (fun u => resMap n u = a), a4 u * Z u

/-- **A6, the exact finite bilinear parent (SOURCE DICTIONARY).**

  `(1/H) ∑_k ∑_ℓ ∑*_{a mod ℓ} A_{ℓ,a,k} conj(E_{ℓ,a,k})`.

`E` is the abstract residue discrepancy; nothing is assumed about it, and no
bound is asserted.  This is a *definition* recording the shape of the parent. -/
noncomputable def endpointBilinearParent (H : ℝ) (Ks Ls : Finset ℕ)
    (units : ℕ → Finset (ZMod n)) (A E : ℕ → ℕ → ZMod n → ℂ) : ℂ :=
  ((H : ℂ))⁻¹ * ∑ k ∈ Ks, ∑ l ∈ Ls, ∑ a ∈ units l,
    A k l a * (starRingEnd ℂ) (E k l a)

/-! ## 3. Energy expansion and the exact two-child split -/

/-- **A6/A8.**  Expanding `∑_a |A_{ℓ,a,k}|²` yields exactly the congruent pair
condition `u₁ ≡ u₂ (mod ℓ)`. -/
theorem residueEnergy_expansion (U : Finset ℤ) (a4 Z : ℤ → ℂ)
    (Aset : Finset (ZMod n)) (hcov : ∀ u ∈ U, resMap n u ∈ Aset) :
    ∑ a ∈ Aset, residueSource n U a4 Z a *
        (starRingEnd ℂ) (residueSource n U a4 Z a)
      = ∑ p ∈ (U ×ˢ U).filter (fun p => resMap n p.1 = resMap n p.2),
          (a4 p.1 * Z p.1) * (starRingEnd ℂ) (a4 p.2 * Z p.2) :=
  sum_fiber_energy U (resMap n) Aset (fun u => a4 u * Z u) hcov

/-- The full congruent-pair index set. -/
def congruentPairSet (U : Finset ℤ) : Finset (ℤ × ℤ) :=
  (U ×ˢ U).filter (fun p => resMap n p.1 = resMap n p.2)

/-- The `u`-diagonal child (`u₁ = u₂`). -/
noncomputable def diagEnergy (U : Finset ℤ) (a4 Z : ℤ → ℂ) : ℂ :=
  ∑ p ∈ (congruentPairSet n U).filter (fun p => p.1 = p.2),
    (a4 p.1 * Z p.1) * (starRingEnd ℂ) (a4 p.2 * Z p.2)

/-- **A8, the exact off-diagonal energy source object.**  This is the object
that `Interfaces.RankOneEndpointUOffdiagInput` must bound; it is *not* estimated
here. -/
noncomputable def offdiagEnergy (U : Finset ℤ) (a4 Z : ℤ → ℂ) : ℂ :=
  ∑ p ∈ (congruentPairSet n U).filter (fun p => ¬ p.1 = p.2),
    (a4 p.1 * Z p.1) * (starRingEnd ℂ) (a4 p.2 * Z p.2)

/-- **A6, the exact two-child split.**  Disjoint and exhaustive; an identity. -/
theorem residueEnergy_split (U : Finset ℤ) (a4 Z : ℤ → ℂ)
    (Aset : Finset (ZMod n)) (hcov : ∀ u ∈ U, resMap n u ∈ Aset) :
    ∑ a ∈ Aset, residueSource n U a4 Z a *
        (starRingEnd ℂ) (residueSource n U a4 Z a)
      = diagEnergy n U a4 Z + offdiagEnergy n U a4 Z := by
  rw [residueEnergy_expansion n U a4 Z Aset hcov, diagEnergy, offdiagEnergy,
    congruentPairSet]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The diagonal child is a sum of squared moduli. -/
theorem diagEnergy_eq_sum_sq (U : Finset ℤ) (a4 Z : ℤ → ℂ) :
    diagEnergy n U a4 Z = ∑ u ∈ U, ((‖a4 u * Z u‖ : ℝ) : ℂ) ^ 2 := by
  classical
  have hset : (congruentPairSet n U).filter (fun p => p.1 = p.2)
      = U.image (fun u => (u, u)) := by
    ext p
    simp only [congruentPairSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, _⟩, h4⟩
      refine ⟨p.1, h1, ?_⟩
      rcases p with ⟨x, y⟩
      simp only at h4
      simp [h4]
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨⟨hu, hu⟩, rfl⟩, rfl⟩
  rw [diagEnergy, hset, Finset.sum_image (by intro x _ y _ h; simpa using h)]
  exact Finset.sum_congr rfl fun u _ => Complex.mul_conj' _

end Source

/-! ## 4. Counterguards -/

/-- **A5 COUNTERGUARD.**  The physical source must never be replaced by an
unweighted average.  The weight `a₄` is load-bearing: dropping it changes the
value.  Witness: `U = {0}`, `a₄ ≡ 0`, `Z ≡ 1`, residue class `0` mod `2`. -/
theorem unweighted_average_is_not_the_source :
    ∃ (U : Finset ℤ) (a4 Z : ℤ → ℂ) (a : ZMod 2),
      residueSource 2 U a4 Z a ≠
        ∑ u ∈ U.filter (fun u => resMap 2 u = a), Z u := by
  classical
  refine ⟨{0}, fun _ => 0, fun _ => 1, 0, ?_⟩
  have hfil : (({0} : Finset ℤ)).filter (fun u => resMap 2 u = (0 : ZMod 2))
      = {0} := by decide
  simp [residueSource, hfil]

/-- **A8/A6 firewall.**  The off-diagonal child may not be dropped by fiat: its
index set is nonempty already for a two-element source in a single residue
class. -/
theorem offdiag_index_set_nonempty :
    (congruentPairSet 1 ({0, 1} : Finset ℤ)).filter (fun p => ¬ p.1 = p.2)
      ≠ (∅ : Finset (ℤ × ℤ)) := by
  decide

end EndpointBilinear
end CurrentProgramme
end TwinPrimeProject
