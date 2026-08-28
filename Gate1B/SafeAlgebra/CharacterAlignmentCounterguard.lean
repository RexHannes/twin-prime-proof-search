/-
# Gate 1B v12 — character-saturation firewall (generic countermodel)

**Status: PROVED_ALGEBRAIC (generic countermodel only).**

In an abstract finite multiplicative character basis (`MulCharSystem`) we
construct the coefficient vector aligned with a single common character mode,

    A = χ_d,

and prove that its character transform is a *single spike of full natural
scale*:

    Â(c) = |G| · [c = d],      ‖Â(d)‖² = |G| · ∑_g ‖A g‖².

So the character-side second moment is entirely carried by one mode and there
is no cancellation whatever.

**This is only a generic countermodel.**  Nothing here says that the actual
Full-Nine / QK source admits such an alignment; it only forbids a proof step
that would rule out alignment on generic grounds.

Contents:

* `hat_chi_eq` — the aligned transform is a spike;
* `commonCharacterAlignment_saturates_genericMoment`;
* `alignedMode_carries_all_parseval_mass`.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteMultiplicativeCharacters

namespace Gate1B.SafeAlgebra

open Finset

namespace MulCharSystem

variable {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] (S : MulCharSystem G Ch)

/-- The transform of a single character coefficient vector is a spike. -/
theorem hat_chi_eq (d c : Ch) :
    S.hat (S.chi d) c = if d = c then (Fintype.card G : ℂ) else 0 := by
  unfold hat
  exact S.orthogonality d c

/-- **Generic character-alignment saturation.**  For the aligned coefficient
vector `A = χ_d` the transform at the common mode attains the full natural
scale: `‖Â(d)‖² = |G| · ∑_g ‖A g‖²`, i.e. no cancellation at all. -/
theorem commonCharacterAlignment_saturates_genericMoment (d : Ch) :
    ‖S.hat (S.chi d) d‖ ^ 2 = (Fintype.card G : ℝ) * ∑ g : G, ‖S.chi d g‖ ^ 2 := by
  have h1 : ‖S.hat (S.chi d) d‖ ^ 2 = ((Fintype.card G : ℝ)) ^ 2 := by
    rw [S.hat_chi_eq d d]
    simp
  have h2 : ∑ g : G, ‖S.chi d g‖ ^ 2 = (Fintype.card G : ℝ) := by
    simp [S.norm_one d]
  rw [h1, h2]
  ring

/-- **All the Parseval mass sits on the aligned mode.** -/
theorem alignedMode_carries_all_parseval_mass (d : Ch) :
    ∑ c : Ch, ‖S.hat (S.chi d) c‖ ^ 2 = ‖S.hat (S.chi d) d‖ ^ 2 := by
  classical
  have hterm : ∀ c : Ch, ‖S.hat (S.chi d) c‖ ^ 2
      = if c = d then ((Fintype.card G : ℝ)) ^ 2 else 0 := by
    intro c
    rw [S.hat_chi_eq d c]
    by_cases h : d = c <;> simp [h, eq_comm]
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_ite_eq' Finset.univ d]
  rw [S.hat_chi_eq d d]
  simp

end MulCharSystem

end Gate1B.SafeAlgebra
