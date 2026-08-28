import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# Phase C · the mixed additive/multiplicative index (`ENDPOINT-MIXED-ADDMULT-SEQUENCE45`)

**Exact finite algebra over `ℤ`.**  Every subtraction in this module is integer
subtraction; the truncating-`ℕ` firewall is recorded explicitly in
`nat_sub_is_not_int_sub`, and no statement here is ever transported to `ℕ`.

## Contents

* `nu` — the mixed index `ν = m's − mr`;
* `nonzero_congruence_iff_unique_j` — on the nonzero congruence child,
  `mr ≡ m's (mod ℓ)` and `mr ≠ m's` hold **iff** there is a *unique* nonzero
  integer `j` with `ν = jℓ`;
* `bMix` — the mixed coefficient at a fixed value of `ν`;
* `mixed_regroup` / `nonzeroCongruence_regroup` — the exact finite regrouping of
  the nonzero centered congruence contribution as
  `∑_ℓ ∑_{r,s} γ(r) conj γ(s) ∑_{j ≠ 0} bMix(jℓ, r, s; ℓ, k)`.

Nothing is estimated, and no source is used: `α`, `γ` and `Z` are abstract.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace MixedAddMult

open Finset

/-! ## 0. Natural/integer subtraction firewall -/

/-- **Firewall.**  `ℕ`-subtraction truncates, so the mixed index `ν` is defined
over `ℤ` and never over `ℕ`.  This is a literal witness of the difference. -/
theorem nat_sub_is_not_int_sub : ((3 : ℕ) - 5 = 0) ∧ ((3 : ℤ) - 5 = -2) := by
  constructor <;> decide

/-! ## 1. The mixed index -/

/-- The mixed additive/multiplicative index `ν = m's − mr`, over `ℤ`. -/
def nu (m m' r s : ℤ) : ℤ := m' * s - m * r

theorem nu_eq_zero_iff (m m' r s : ℤ) : nu m m' r s = 0 ↔ m * r = m' * s := by
  unfold nu
  constructor
  · intro h; linarith [sub_eq_zero.1 h]
  · intro h; rw [h]; ring

/-- **Nonzero congruence child.**  For a nonzero modulus `ℓ`, the pair of
conditions

  `mr ≡ m's (mod ℓ)`  and  `mr ≠ m's`

is equivalent to the existence of a **unique** nonzero integer `j` with
`ν = jℓ`. -/
theorem nonzero_congruence_iff_unique_j (l : ℕ) (hl : l ≠ 0) (m m' r s : ℤ) :
    ((((m * r : ℤ)) : ZMod l) = (((m' * s : ℤ)) : ZMod l) ∧ m * r ≠ m' * s)
      ↔ ∃! j : ℤ, j ≠ 0 ∧ nu m m' r s = j * (l : ℤ) := by
  have hlz : ((l : ℤ)) ≠ 0 := Int.natCast_ne_zero.2 hl
  constructor
  · rintro ⟨hcong, hne⟩
    have hmod : (m * r) ≡ (m' * s) [ZMOD (l : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff (m * r) (m' * s) l).1 hcong
    have hdvd : ((l : ℤ)) ∣ nu m m' r s := Int.ModEq.dvd hmod
    obtain ⟨j, hj⟩ := hdvd
    have hnu : nu m m' r s ≠ 0 := fun h => hne ((nu_eq_zero_iff m m' r s).1 h)
    refine ⟨j, ⟨?_, by rw [hj]; ring⟩, ?_⟩
    · rintro rfl; exact hnu (by rw [hj]; ring)
    · rintro j' ⟨-, hj'⟩
      have : j' * (l : ℤ) = j * (l : ℤ) := by rw [← hj', hj]; ring
      exact mul_right_cancel₀ hlz this
  · rintro ⟨j, ⟨hj0, hjeq⟩, -⟩
    have hdvd : ((l : ℤ)) ∣ nu m m' r s := ⟨j, by rw [hjeq]; ring⟩
    have hne : nu m m' r s ≠ 0 := by
      rw [hjeq]
      exact mul_ne_zero hj0 hlz
    refine ⟨?_, fun h => hne ((nu_eq_zero_iff m m' r s).2 h)⟩
    have hmod : (m * r) ≡ (m' * s) [ZMOD (l : ℤ)] := Int.modEq_iff_dvd.2 hdvd
    exact (ZMod.intCast_eq_intCast_iff (m * r) (m' * s) l).2 hmod

/-! ## 2. The mixed coefficient -/

variable (Pm : Finset ℤ) (α : ℤ → ℂ) (Z : ℤ → ℕ → ℤ → ℂ)

/-- **The mixed coefficient.**  For fixed `ℓ, k, r, s`,

  `bMix(ν) = ∑_{m,m' : m's − mr = ν} α(m) conj α(m') Z(mr,ℓ,k) conj Z(m's,ℓ,k)`.
-/
noncomputable def bMix (l : ℕ) (k : ℤ) (r s : ℤ) (v : ℤ) : ℂ :=
  ∑ p ∈ (Pm ×ˢ Pm).filter (fun p => nu p.1 p.2 r s = v),
    α p.1 * (starRingEnd ℂ) (α p.2) * Z (p.1 * r) l k *
      (starRingEnd ℂ) (Z (p.2 * s) l k)

/-- **Exact regrouping at fixed `(ℓ, r, s)`.**  The nonzero congruence child is
exactly the sum of the mixed coefficients along the arithmetic progression
`ν = jℓ`, `j ≠ 0`.

`hJ` is the exact finite support condition: `Js` must contain every `j` that is
actually realised by the finite model. -/
theorem mixed_regroup (l : ℕ) (hl : l ≠ 0) (k : ℤ) (r s : ℤ) (Js : Finset ℤ)
    (hJ : ∀ p ∈ Pm ×ˢ Pm, ∀ j : ℤ, j ≠ 0 → nu p.1 p.2 r s = j * (l : ℤ) →
      j ∈ Js.filter (fun j => j ≠ 0)) :
    ∑ p ∈ (Pm ×ˢ Pm).filter (fun p =>
        (((p.1 * r : ℤ)) : ZMod l) = (((p.2 * s : ℤ)) : ZMod l) ∧
          p.1 * r ≠ p.2 * s),
        α p.1 * (starRingEnd ℂ) (α p.2) * Z (p.1 * r) l k *
          (starRingEnd ℂ) (Z (p.2 * s) l k)
      = ∑ j ∈ Js.filter (fun j => j ≠ 0), bMix Pm α Z l k r s (j * (l : ℤ)) := by
  classical
  have hlz : ((l : ℤ)) ≠ 0 := Int.natCast_ne_zero.2 hl
  set S := (Pm ×ˢ Pm).filter (fun p =>
      (((p.1 * r : ℤ)) : ZMod l) = (((p.2 * s : ℤ)) : ZMod l) ∧
        p.1 * r ≠ p.2 * s) with hS
  set w : ℤ × ℤ → ℂ := fun p =>
    α p.1 * (starRingEnd ℂ) (α p.2) * Z (p.1 * r) l k *
      (starRingEnd ℂ) (Z (p.2 * s) l k) with hw
  have hmaps : ∀ p ∈ S, nu p.1 p.2 r s / (l : ℤ) ∈ Js.filter (fun j => j ≠ 0) := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    obtain ⟨j, ⟨hj0, hjeq⟩, -⟩ :=
      (nonzero_congruence_iff_unique_j l hl p.1 p.2 r s).1 hp.2
    rw [hjeq, Int.mul_ediv_cancel _ hlz]
    exact hJ p hp.1 j hj0 hjeq
  have hfib : ∀ j ∈ Js.filter (fun j => j ≠ 0),
      S.filter (fun p => nu p.1 p.2 r s / (l : ℤ) = j)
        = (Pm ×ˢ Pm).filter (fun p => nu p.1 p.2 r s = j * (l : ℤ)) := by
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_filter.1 hj).2
    ext p
    simp only [hS, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, hcong⟩, hdiv⟩
      refine ⟨hp, ?_⟩
      obtain ⟨j', ⟨hj'0, hj'eq⟩, -⟩ :=
        (nonzero_congruence_iff_unique_j l hl p.1 p.2 r s).1 hcong
      have hdd : nu p.1 p.2 r s / (l : ℤ) = j' := by
        rw [hj'eq, Int.mul_ediv_cancel _ hlz]
      rw [hj'eq, ← hdiv, hdd]
    · rintro ⟨hp, hval⟩
      have hcong := (nonzero_congruence_iff_unique_j l hl p.1 p.2 r s).2
        ⟨j, ⟨hj0, hval⟩, by
          rintro j'' ⟨-, hj''⟩
          have : j'' * (l : ℤ) = j * (l : ℤ) := by rw [← hj'', hval]
          exact mul_right_cancel₀ hlz this⟩
      exact ⟨⟨hp, hcong⟩, by rw [hval, Int.mul_ediv_cancel _ hlz]⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hfib j hj, bMix]

/-! ## 3. The full nonzero centered congruence contribution -/

/-- The nonzero centered congruence contribution, in the `(ℓ, r, s)`-organised
form produced by the centered `2|2` rewriting. -/
noncomputable def nonzeroCongruenceContribution (Ls : Finset ℕ) (Pr : Finset ℤ)
    (γ : ℤ → ℂ) (k : ℤ) : ℂ :=
  ∑ l ∈ Ls, ∑ r ∈ Pr, ∑ s ∈ Pr, γ r * (starRingEnd ℂ) (γ s) *
    ∑ p ∈ (Pm ×ˢ Pm).filter (fun p =>
        (((p.1 * r : ℤ)) : ZMod l) = (((p.2 * s : ℤ)) : ZMod l) ∧
          p.1 * r ≠ p.2 * s),
      α p.1 * (starRingEnd ℂ) (α p.2) * Z (p.1 * r) l k *
        (starRingEnd ℂ) (Z (p.2 * s) l k)

/-- **`ENDPOINT-MIXED-ADDMULT-SEQUENCE45`.**  The exact finite regrouping of the
nonzero centered congruence contribution into the mixed additive/multiplicative
sequence `∑_{j ≠ 0} bMix(jℓ, r, s; ℓ, k)`. -/
theorem nonzeroCongruence_regroup (Ls : Finset ℕ) (Pr : Finset ℤ) (γ : ℤ → ℂ)
    (k : ℤ) (Js : ℕ → ℤ → ℤ → Finset ℤ)
    (hLs : ∀ l ∈ Ls, l ≠ 0)
    (hJ : ∀ l ∈ Ls, ∀ r ∈ Pr, ∀ s ∈ Pr, ∀ p ∈ Pm ×ˢ Pm, ∀ j : ℤ, j ≠ 0 →
      nu p.1 p.2 r s = j * (l : ℤ) → j ∈ (Js l r s).filter (fun j => j ≠ 0)) :
    nonzeroCongruenceContribution Pm α Z Ls Pr γ k
      = ∑ l ∈ Ls, ∑ r ∈ Pr, ∑ s ∈ Pr, γ r * (starRingEnd ℂ) (γ s) *
          ∑ j ∈ (Js l r s).filter (fun j => j ≠ 0),
            bMix Pm α Z l k r s (j * (l : ℤ)) := by
  classical
  refine Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun r hr =>
    Finset.sum_congr rfl fun s hs => ?_
  rw [mixed_regroup Pm α Z l (hLs l hl) k r s (Js l r s)
    (fun p hp j hj0 hjeq => hJ l hl r hr s hs p hp j hj0 hjeq)]

end MixedAddMult
end CurrentProgramme
end TwinPrimeProject
