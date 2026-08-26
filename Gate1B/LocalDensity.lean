/-
# Gate 1B safe algebra bank — §9: the local density count.

This is a **finite counting fact** about `𝔽_s × 𝔽_s` and nothing else.  It is
*not* an analytic saving: no sum over moduli, no large sieve, no averaging and
no error term is asserted anywhere in this file.  The normalised conditional
density `s / s² = 1/s` is recorded as a rational identity.
-/
import Mathlib

namespace Gate1B

open Finset

/-- **Local density count.**  The diagonal of `𝔽_s × 𝔽_s` has exactly `s`
points. -/
theorem card_local_diagonal (s : ℕ) [NeZero s] :
    (Finset.univ.filter (fun p : ZMod s × ZMod s => p.1 = p.2)).card = s := by
  have himg : (Finset.univ.filter (fun p : ZMod s × ZMod s => p.1 = p.2))
      = Finset.univ.image (fun x : ZMod s => (x, x)) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h; exact ⟨p.1, by simp [Prod.ext_iff, h]⟩
    · rintro ⟨x, -, rfl⟩; rfl
  rw [himg, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq _ _ _ _ ▸ h).1),
    Finset.card_univ, ZMod.card]

/-- The ambient count: `#(𝔽_s × 𝔽_s) = s²`. -/
theorem card_local_square (s : ℕ) [NeZero s] :
    (Finset.univ : Finset (ZMod s × ZMod s)).card = s ^ 2 := by
  rw [Finset.card_univ, Fintype.card_prod, ZMod.card, sq]

/-- **Normalised conditional density** `s / s² = 1 / s`.  A rational identity,
not an estimate. -/
theorem local_density_eq (s : ℕ) (hs : s ≠ 0) : (s : ℚ) / (s : ℚ) ^ 2 = 1 / (s : ℚ) := by
  field_simp

/-- The count in its density form, assembled from the two cardinalities. -/
theorem local_diagonal_density (s : ℕ) [NeZero s] (hs : s ≠ 0) :
    ((Finset.univ.filter (fun p : ZMod s × ZMod s => p.1 = p.2)).card : ℚ)
      / ((Finset.univ : Finset (ZMod s × ZMod s)).card : ℚ) = 1 / (s : ℚ) := by
  rw [card_local_diagonal, card_local_square]
  push_cast
  exact local_density_eq s hs

/-- Guard: at `s = 1` the "density" is `1`.  The count carries no saving by
itself; any saving would have to come from a genuine sum over `s`, which is not
formalised here. -/
theorem local_density_trivial_at_one :
    ((Finset.univ.filter (fun p : ZMod 1 × ZMod 1 => p.1 = p.2)).card : ℚ)
      / ((Finset.univ : Finset (ZMod 1 × ZMod 1)).card : ℚ) = 1 := by
  rw [card_local_diagonal, card_local_square]
  norm_num

end Gate1B
