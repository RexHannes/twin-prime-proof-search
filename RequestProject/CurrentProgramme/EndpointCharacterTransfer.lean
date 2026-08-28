import Mathlib
import RequestProject.CurrentProgramme.EndpointShiftedDeterminant
import RequestProject.CurrentProgramme.EndpointCharacterCentering

/-!
# Determinant character transfer (Phase C of the high-`k` bank, Phase A of the
operator bank)

From the shift-independent congruence `u·v ≡ -2 (mod ℓ)` we transfer the
character twist from the `u`-side to the `v`-side:

```
χ(u)·χ(v) = χ(-2),        χ(u) = χ(-2)·conj(χ(v))
```

on the proper unit sector, **uniformly in the determinant shift `hSh`**.

Also banked:

* the residue form `a = -2·u⁻¹ (mod ℓ)` and
  `conj(χ(a)) = conj(χ(-2))·χ(u)` (`determinantResidue_character_transfer`);
* the `2|2` version, where `u = m·r` splits into the *model* factor `r`
  (`twoByTwo_character_transfer`).

**Variable-name firewall.**  `r` is always the model factor of the `2|2` split
`u = m·r`; the determinant shift is always `hSh`.  The two are never identified,
and no theorem below has a hypothesis relating them.

No estimate, no smoothness, no analytic input.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace CharTransfer

open CharacterCentering ShiftedDet

/-! ## 1. The character product identity -/

/-- **`shiftedDet_character_product`.**  If `u·v = -2` in `ZMod n` then for every
character `χ` modulo `n`, `χ(u)·χ(v) = χ(-2)`. -/
theorem shiftedDet_character_product {n : ℕ} (χ : DirichletCharacter ℂ n) (u v : ZMod n)
    (huv : u * v = -2) : χ u * χ v = χ (-2) := by
  rw [← map_mul, huv]

/-- **`shiftedDet_character_transfer`.**  On the unit sector the twist moves from
the `u`-side to the `v`-side: `χ(u) = χ(-2)·conj(χ(v))`. -/
theorem shiftedDet_character_transfer {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n)
    (u : ZMod n) (v : (ZMod n)ˣ) (huv : u * (v : ZMod n) = -2) :
    χ u = χ (-2) * (starRingEnd ℂ) (χ (v : ZMod n)) := by
  have hprod : χ u * χ (v : ZMod n) = χ (-2) :=
    shiftedDet_character_product χ u (v : ZMod n) huv
  have hconj : (starRingEnd ℂ) (χ (v : ZMod n)) = χ ((v⁻¹ : (ZMod n)ˣ) : ZMod n) :=
    conj_apply_unit n χ v
  have hinv : χ (v : ZMod n) * χ ((v⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
    rw [← map_mul]; norm_cast; simp
  rw [hconj, ← hprod, mul_assoc, hinv, mul_one]

/-! ## 2. Uniformity in the determinant shift -/

/-- **`shiftedMAM_character_transfer_uniform`.**  Starting from the *integer*
shifted shell `d p ℓ - u v = 2 + u ℓ hSh` with `ℓ = n`, the character identity
`χ(u)·χ(v) = χ(-2)` holds; its statement does not mention `hSh` at all. -/
theorem shiftedMAM_character_transfer_uniform {n : ℕ} (χ : DirichletCharacter ℂ n)
    (u v d p hSh : ℤ)
    (hshell : d * p * (n : ℤ) - u * v = 2 + u * (n : ℤ) * hSh) :
    χ (u : ZMod n) * χ (v : ZMod n) = χ (-2) :=
  shiftedDet_character_product χ _ _ (shiftedDet_zmod n u v d p hSh hshell)

/-- Explicit shift-independence: two different shifts, with possibly different
`d,p` slots, give literally the same character identity. -/
theorem character_transfer_shift_independent {n : ℕ} (χ : DirichletCharacter ℂ n)
    (u v d₁ p₁ d₂ p₂ hSh₁ hSh₂ : ℤ)
    (h₁ : d₁ * p₁ * (n : ℤ) - u * v = 2 + u * (n : ℤ) * hSh₁)
    (h₂ : d₂ * p₂ * (n : ℤ) - u * v = 2 + u * (n : ℤ) * hSh₂) :
    χ (u : ZMod n) * χ (v : ZMod n) = χ (-2) ∧
      (χ (u : ZMod n) * χ (v : ZMod n) = χ (-2)) := by
  exact ⟨shiftedMAM_character_transfer_uniform χ u v d₁ p₁ hSh₁ h₁,
    shiftedMAM_character_transfer_uniform χ u v d₂ p₂ hSh₂ h₂⟩

/-! ## 3. The `2|2` version: `u = m·r` with `r` the model factor -/

/-- **`twoByTwo_character_transfer`.**  With the model factorisation `u = m·r`
(the letter `r` is the *model* factor, never the determinant shift `hSh`), the
transfer identity reads `χ(m)·χ(r)·χ(v) = χ(-2)`. -/
theorem twoByTwo_character_transfer {n : ℕ} (χ : DirichletCharacter ℂ n) (m r v : ZMod n)
    (hu : m * r * v = -2) : χ m * χ r * χ v = χ (-2) := by
  rw [← map_mul, ← map_mul, hu]

/-- The same, moving the whole `2|2` twist to the `v`-side. -/
theorem twoByTwo_character_transfer_toV {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n)
    (m r : ZMod n) (v : (ZMod n)ˣ) (hu : m * r * (v : ZMod n) = -2) :
    χ m * χ r = χ (-2) * (starRingEnd ℂ) (χ (v : ZMod n)) := by
  have h := shiftedDet_character_transfer χ (m * r) v hu
  rwa [map_mul] at h

/-! ## 4. The `A`-side residue form -/

/-- **`determinantResidue_character_transfer`.**  If the residue `a` is the
determinant residue `a = -2·u⁻¹` in `ZMod n` (units `a,u`), then
`conj(χ(a)) = conj(χ(-2))·χ(u)`. -/
theorem determinantResidue_character_transfer {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n) (u a : (ZMod n)ˣ)
    (ha : (a : ZMod n) = -2 * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) :
    (starRingEnd ℂ) (χ (a : ZMod n))
      = (starRingEnd ℂ) (χ (-2)) * χ (u : ZMod n) := by
  have hsplit : χ (a : ZMod n) = χ (-2) * χ ((u⁻¹ : (ZMod n)ˣ) : ZMod n) := by
    rw [ha, map_mul]
  have hconj : (starRingEnd ℂ) (χ ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) = χ (u : ZMod n) := by
    rw [conj_apply_unit n χ u⁻¹]
    simp
  rw [hsplit, map_mul, hconj]

/-- The residue characterisation itself: on units, `u·v = -2` is the same as
`v = -2·u⁻¹`. -/
theorem determinantResidue_iff {n : ℕ} (u v : (ZMod n)ˣ) :
    (u : ZMod n) * (v : ZMod n) = -2 ↔
      (v : ZMod n) = -2 * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) := by
  have hu : ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (u : ZMod n) = 1 := by
    norm_cast; simp
  have hu' : (u : ZMod n) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
    norm_cast; simp
  constructor
  · intro h
    calc (v : ZMod n) = ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * ((u : ZMod n) * (v : ZMod n)) := by
          rw [← mul_assoc, hu, one_mul]
      _ = -2 * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) := by rw [h]; ring
  · intro h
    rw [h]
    calc (u : ZMod n) * (-2 * ((u⁻¹ : (ZMod n)ˣ) : ZMod n))
        = -2 * ((u : ZMod n) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)) := by ring
      _ = -2 := by rw [hu', mul_one]

end CharTransfer
end CurrentProgramme
end TwinPrimeProject
