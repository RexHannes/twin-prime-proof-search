/-
# Gate 1B v8.3 — H9 exact nonprincipal character packet

**Status: PROVED_ALGEBRAIC (Tier 2: the character system is supplied).**

For a supplied complete multiplicative character system on a finite abelian
group `G` with principal character `c₀`, the unit-residue indicator splits
exactly into its main term and a nonprincipal packet:

    1_{y = t} - 1/|G| = |G|⁻¹ ∑_{χ ≠ χ₀} conj χ(t) · χ(y).

Specialising `y = q ℓ` and `t = 2` (the fixed shift, in the unit group modulo
`C₉`) gives the H9 pure-defect packet; under a supplied factorisation of the
`y`-transforms it reassembles into

    ∑ Γ₉ / φ · ∑_{χ ≠ χ₀} conj χ(2) · B(χ) · L(χ).

**No analytic estimate.**  Nothing here says the packet is small; the H9
analytic estimate remains OPEN.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteMultiplicativeCharacters
import Gate1B.SafeAlgebra.H9PureDefect

namespace Gate1B.SafeAlgebra

open Finset

namespace MulCharSystem

variable {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] (S : MulCharSystem G Ch)

/-- **Unit-residue indicator expansion.**  The conjugation on `χ(t)` is derived
from the supplied dual orthogonality, not postulated. -/
theorem unit_residue_indicator_character_expand {c0 : Ch} (hc0 : S.IsPrincipal c0) (t y : G) :
    (if y = t then (1 : ℂ) else 0) - 1 / (Fintype.card G : ℂ)
      = (1 / (Fintype.card G : ℂ)) *
          ∑ c ∈ (univ : Finset Ch).erase c0, (starRingEnd ℂ) (S.chi c t) * S.chi c y := by
  classical
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    have hp : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast Nat.cast_ne_zero.2 hp.ne'
  have hsplit : ∑ c : Ch, S.chi c y * (starRingEnd ℂ) (S.chi c t)
      = S.chi c0 y * (starRingEnd ℂ) (S.chi c0 t)
        + ∑ c ∈ (univ : Finset Ch).erase c0, S.chi c y * (starRingEnd ℂ) (S.chi c t) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ c0)).symm
  have hprinc : S.chi c0 y * (starRingEnd ℂ) (S.chi c0 t) = 1 := by
    rw [hc0 y, hc0 t]; simp
  have hdual := S.dual_orthogonality y t
  rw [hsplit, hprinc] at hdual
  have hnon : ∑ c ∈ (univ : Finset Ch).erase c0, (starRingEnd ℂ) (S.chi c t) * S.chi c y
      = (if y = t then (Fintype.card G : ℂ) else 0) - 1 := by
    rw [← hdual]
    ring_nf
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hnon]
  by_cases h : y = t
  · simp [h]
    field_simp
  · simp [h]

/-- **H9 nonprincipal packet (single modulus).**  Selecting the residue `t`
inside a weighted `y`-sum splits exactly into a main term and a nonprincipal
character packet. -/
theorem h9_nonprincipal_character_packet {c0 : Ch} (hc0 : S.IsPrincipal c0)
    (W : G → ℂ) (t : G) :
    ∑ y : G, W y * (if y = t then (1 : ℂ) else 0)
      = (1 / (Fintype.card G : ℂ)) * ∑ y : G, W y
        + (1 / (Fintype.card G : ℂ)) *
            ∑ c ∈ (univ : Finset Ch).erase c0,
              (starRingEnd ℂ) (S.chi c t) * ∑ y : G, W y * S.chi c y := by
  classical
  have hpoint : ∀ y : G, W y * (if y = t then (1 : ℂ) else 0)
      = W y * (1 / (Fintype.card G : ℂ))
        + W y * ((1 / (Fintype.card G : ℂ)) *
            ∑ c ∈ (univ : Finset Ch).erase c0, (starRingEnd ℂ) (S.chi c t) * S.chi c y) := by
    intro y
    rw [← S.unit_residue_indicator_character_expand hc0 t y]
    ring
  rw [Finset.sum_congr rfl fun y _ => hpoint y, Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_mul]; ring
  · rw [Finset.mul_sum]
    have : ∀ y : G, W y * ((1 / (Fintype.card G : ℂ)) *
        ∑ c ∈ (univ : Finset Ch).erase c0, (starRingEnd ℂ) (S.chi c t) * S.chi c y)
        = ∑ c ∈ (univ : Finset Ch).erase c0,
            (1 / (Fintype.card G : ℂ)) * ((starRingEnd ℂ) (S.chi c t) * (W y * S.chi c y)) := by
      intro y
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- **Abstract packet reassembly.**  If the `y`-transforms factor as
`∑_y W(y) χ(y) = B(χ) · L(χ)`, the nonprincipal packet is the corresponding
character sum.  The factorisation is an explicit hypothesis. -/
theorem h9_packet_of_factorisation {c0 : Ch} (hc0 : S.IsPrincipal c0)
    (W : G → ℂ) (t : G) (Bc Lc : Ch → ℂ)
    (hfac : ∀ c : Ch, ∑ y : G, W y * S.chi c y = Bc c * Lc c) :
    ∑ y : G, W y * (if y = t then (1 : ℂ) else 0)
      = (1 / (Fintype.card G : ℂ)) * ∑ y : G, W y
        + (1 / (Fintype.card G : ℂ)) *
            ∑ c ∈ (univ : Finset Ch).erase c0,
              (starRingEnd ℂ) (S.chi c t) * (Bc c * Lc c) := by
  rw [S.h9_nonprincipal_character_packet hc0 W t]
  congr 2
  exact Finset.sum_congr rfl fun c _ => by rw [hfac c]

end MulCharSystem

end Gate1B.SafeAlgebra
