import RequestProject.NANC.Gate1BDet2.CompositeViewDet2

/-!
# Gate 1B / determinant-2 bank, Module 35: composite-view multiplicity

The clean **finite multiplicity** statement implied by Module 34:

* for a fixed `(q, u, s)` and an admissible `l`-set of diameter `< u s`, there
  is at most one admissible `l` (`composite_view_at_most_one_l`), hence at most
  one pair `(l, ρ)` (`composite_view_at_most_one_l_rho`);
* allowing an *abstract* finite multiplicity factor `Mfact` for the `q = d p`
  representations, the number of `(l, ρ, d, p)` representations is at most
  `Mfact` (`composite_view_multiplicity_le`).

`Mfact` is a genuine natural number parameter: **it is deliberately not replaced
by `X^{o(1)}`**, since that asymptotic interpretation lives outside Lean.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Composite

open Finset

/-! ## 1. At most one admissible `l`, hence at most one `(l, ρ)` -/

open scoped Classical in
/-- **At most one admissible `l`.**  For fixed `(q, u, s)` with `q` invertible
modulo `u s > 0`, an `l`-set of diameter `< u s` contains at most one `l` for
which the composite relation is solvable. -/
theorem composite_view_at_most_one_l {q u s : ℤ} (hus : 0 < u * s)
    (hcop : IsCoprime q (u * s)) (hcopus : IsCoprime u s) (Lset : Finset ℤ)
    (hdiam : ∀ l₁ ∈ Lset, ∀ l₂ ∈ Lset, |l₁ - l₂| < u * s) :
    (Lset.filter (fun l => ∃ rho : ℤ, CompositeDet2 q l u rho s)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 (fun a ha b hb => ?_)
  rw [Finset.mem_filter] at ha hb
  obtain ⟨haL, rhoa, hda⟩ := ha
  obtain ⟨hbL, rhob, hdb⟩ := hb
  exact composite_det2_l_unique_in_short_interval hus hcop hcopus hda hdb (hdiam a haL b hbL)

/-- **At most one admissible `(l, ρ)`.** -/
theorem composite_view_at_most_one_l_rho {q u s : ℤ} (hus : 0 < u * s)
    (hcop : IsCoprime q (u * s)) (hcopus : IsCoprime u s) (S : Finset (ℤ × ℤ))
    (hS : ∀ x ∈ S, CompositeDet2 q x.1 u x.2 s)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x.1 - y.1| < u * s) :
    S.card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 (fun a ha b hb => ?_)
  have hl : a.1 = b.1 :=
    composite_det2_l_unique_in_short_interval hus hcop hcopus (hS a ha) (hS b hb)
      (hdiam a ha b hb)
  have hda := hS a ha
  have hdb := hS b hb
  rw [hl] at hda
  have hrho : a.2 = b.2 := composite_view_rho_unique (ne_of_gt hus) hda hdb
  exact Prod.ext hl hrho

/-! ## 2. Multiplicity with an abstract `(d, p)`-representation factor -/

/-- **`composite_view_multiplicity_le`.**  Fix `(q, u, s)` with `q` invertible
modulo `u s > 0`.  Suppose every recorded representation carries a `(d, p)`
label lying in a finite set `DP` of size at most `Mfact`, and all recorded
`l`-values lie within an interval of diameter `< u s`.  Then the number of
`(l, ρ, d, p)` representations is at most `Mfact`.

`Mfact` is abstract: no asymptotic interpretation is made. -/
theorem composite_view_multiplicity_le {q u s : ℤ} (hus : 0 < u * s)
    (hcop : IsCoprime q (u * s)) (hcopus : IsCoprime u s)
    (T : Finset (ℤ × ℤ × ℕ × ℕ)) (DP : Finset (ℕ × ℕ)) (Mfact : ℕ)
    (hDP : DP.card ≤ Mfact)
    (hrep : ∀ t ∈ T, CompositeDet2 q t.1 u t.2.1 s ∧ t.2.2 ∈ DP)
    (hdiam : ∀ t ∈ T, ∀ t' ∈ T, |t.1 - t'.1| < u * s) :
    T.card ≤ Mfact := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (fun t => t.2.2)
    (fun t ht => (hrep t ht).2) ?_) hDP
  intro t ht t' ht' hlabel
  simp only [Finset.mem_coe] at ht ht'
  have hl : t.1 = t'.1 :=
    composite_det2_l_unique_in_short_interval hus hcop hcopus (hrep t ht).1 (hrep t' ht').1
      (hdiam t ht t' ht')
  have hda := (hrep t ht).1
  have hdb := (hrep t' ht').1
  rw [hl] at hda
  have hrho : t.2.1 = t'.2.1 := composite_view_rho_unique (ne_of_gt hus) hda hdb
  exact Prod.ext hl (Prod.ext hrho hlabel)

/-- Specialisation: with a single admissible `(d, p)` representation
(`Mfact = 1`) there is at most one full representation. -/
theorem composite_view_multiplicity_one {q u s : ℤ} (hus : 0 < u * s)
    (hcop : IsCoprime q (u * s)) (hcopus : IsCoprime u s)
    (T : Finset (ℤ × ℤ × ℕ × ℕ)) (DP : Finset (ℕ × ℕ)) (hDP : DP.card ≤ 1)
    (hrep : ∀ t ∈ T, CompositeDet2 q t.1 u t.2.1 s ∧ t.2.2 ∈ DP)
    (hdiam : ∀ t ∈ T, ∀ t' ∈ T, |t.1 - t'.1| < u * s) :
    T.card ≤ 1 :=
  composite_view_multiplicity_le hus hcop hcopus T DP 1 hDP hrep hdiam

end Composite
end Gate1BDet2
end TwinPrimeProject
