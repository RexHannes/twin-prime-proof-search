import Mathlib
import RequestProject.CurrentProgramme.EndpointCentering

/-!
# Phase A · centered **character** identity (`ENDPOINT-CENTERED-CHAR-SEPARATION45`)

**Exact finite algebra.  No estimate, no asymptotics, no source.**

This module upgrades the finite centered residue kernel of
`RequestProject.CurrentProgramme.EndpointCentering`,

  `Δ_ℓ(u₁,u₂) = 1_{u₁ ≡ u₂ (ℓ)} − 1_{(u₁u₂,ℓ)=1} / φ(ℓ)`,

into its **non-principal Dirichlet-character expansion**

  `Δ_ℓ(u₁,u₂) = (1/φ(ℓ)) ∑_{χ mod ℓ, χ ≠ χ₀} χ(u₁) conj(χ(u₂))`,

valid **on the proper unit sector only**, and then into the square bundle

  `∑_{i,j} c_i conj(c_j) Δ_ℓ(u_i,u_j) = (1/φ(ℓ)) ∑_{χ ≠ χ₀} |∑_i c_i χ(u_i)|²`.

## Infrastructure reuse

No ad-hoc character theory is introduced.  The characters are Mathlib's
`DirichletCharacter ℂ ℓ` and the orthogonality input is Mathlib's
`DirichletCharacter.sum_characters_eq`, so the identification with the standard
Dirichlet-character group is *literal* and no `SOURCE/ADAPTER` obligation for it
is needed.

## Unit hypotheses are explicit and load-bearing

Every statement quantifies over `(ZMod ℓ)ˣ`, never over `ZMod ℓ`.  The
counterguard `centeredKernel_nonunit_counterexample` exhibits an explicit
non-unit pair where the identity **fails**, so the identity is never silently
applied off the unit sector.

## What is NOT here

No analytic estimate on any character sum; no physical source; no claim about
`GATE1B`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace CharacterCentering

open Finset Centering

variable (l : ℕ) [NeZero l]

/-! ## 1. The non-principal character family -/

/-- The non-principal Dirichlet characters mod `ℓ` with values in `ℂ`:
literally `univ.erase χ₀`, where the principal character is `χ₀ = 1`. -/
noncomputable def nonprincipalChars (n : ℕ) [NeZero n] : Finset (DirichletCharacter ℂ n) :=
  Finset.univ.erase 1

theorem mem_nonprincipalChars {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} :
    χ ∈ nonprincipalChars n ↔ χ ≠ 1 := by
  simp [nonprincipalChars]

omit [NeZero l] in
/-- The principal character is `1` on the unit sector. -/
theorem principal_apply_unit (u : (ZMod l)ˣ) :
    (1 : DirichletCharacter ℂ l) (u : ZMod l) = 1 :=
  MulChar.one_apply_coe u

omit [NeZero l] in
/-- On the unit sector complex conjugation of a Dirichlet character is
evaluation at the inverse unit. -/
theorem conj_apply_unit (χ : DirichletCharacter ℂ l) (u : (ZMod l)ˣ) :
    (starRingEnd ℂ) (χ (u : ZMod l)) = χ ((u⁻¹ : (ZMod l)ˣ) : ZMod l) := by
  have h1 : ‖χ (u : ZMod l)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
  have h2 : χ (u : ZMod l) * χ ((u⁻¹ : (ZMod l)ˣ) : ZMod l) = 1 := by
    rw [← map_mul]; norm_cast; simp
  have h3 : χ (u : ZMod l) * (starRingEnd ℂ) (χ (u : ZMod l)) = 1 := by
    rw [Complex.mul_conj]; norm_cast; simp [Complex.normSq_eq_norm_sq, h1]
  have hne : χ (u : ZMod l) ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  exact mul_left_cancel₀ hne (h3.trans h2.symm)

/-- `φ(ℓ) ≠ 0` as a complex number. -/
theorem totient_ne_zero_cast : ((l.totient : ℂ)) ≠ 0 := by
  have hpos : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  have : 0 < l.totient := Nat.totient_pos.2 hpos
  exact_mod_cast this.ne'

/-! ## 2. Full and non-principal orthogonality on the unit sector -/

/-- **Orthogonality, unit sector.**  For units `u₁,u₂`,

  `∑_{χ mod ℓ} χ(u₁) conj(χ(u₂)) = φ(ℓ) · 1_{u₁ = u₂}`.

This is Mathlib's `DirichletCharacter.sum_characters_eq` transported to the
unit group. -/
theorem sum_all_characters_unit_pair (u₁ u₂ : (ZMod l)ˣ) :
    ∑ χ : DirichletCharacter ℂ l, χ (u₁ : ZMod l) * (starRingEnd ℂ) (χ (u₂ : ZMod l))
      = if (u₁ : ZMod l) = (u₂ : ZMod l) then (l.totient : ℂ) else 0 := by
  have hstep : ∀ χ : DirichletCharacter ℂ l,
      χ (u₁ : ZMod l) * (starRingEnd ℂ) (χ (u₂ : ZMod l))
        = χ (((u₁ * u₂⁻¹ : (ZMod l)ˣ) : ZMod l)) := by
    intro χ
    rw [conj_apply_unit l χ u₂, ← map_mul]
    norm_cast
  rw [Finset.sum_congr rfl fun χ _ => hstep χ,
    DirichletCharacter.sum_characters_eq ℂ (((u₁ * u₂⁻¹ : (ZMod l)ˣ) : ZMod l))]
  congr 1
  by_cases h : (u₁ : ZMod l) = (u₂ : ZMod l)
  · have : u₁ = u₂ := Units.ext h
    simp [this]
  · have hne : ((u₁ * u₂⁻¹ : (ZMod l)ˣ) : ZMod l) ≠ 1 := by
      intro hone
      have : u₁ * u₂⁻¹ = 1 := Units.ext (by simpa using hone)
      exact h (by rw [mul_inv_eq_one] at this; rw [this])
    simp [h]

/-- **Non-principal orthogonality, unit sector.**  Removing the principal
character removes exactly `1`. -/
theorem sum_nonprincipal_unit_pair (u₁ u₂ : (ZMod l)ˣ) :
    ∑ χ ∈ nonprincipalChars l,
        χ (u₁ : ZMod l) * (starRingEnd ℂ) (χ (u₂ : ZMod l))
      = (if (u₁ : ZMod l) = (u₂ : ZMod l) then (l.totient : ℂ) else 0) - 1 := by
  have hone : (1 : DirichletCharacter ℂ l) (u₁ : ZMod l) *
      (starRingEnd ℂ) ((1 : DirichletCharacter ℂ l) (u₂ : ZMod l)) = 1 := by
    rw [principal_apply_unit l u₁, principal_apply_unit l u₂]; simp
  rw [nonprincipalChars, Finset.sum_erase_eq_sub (Finset.mem_univ _), hone,
    sum_all_characters_unit_pair l u₁ u₂]

/-! ## 3. The centered kernel is the non-principal character sum -/

/-- **`ENDPOINT-CENTERED-CHAR-SEPARATION45`.**  On the proper unit sector,

  `Δ_ℓ(u₁,u₂) = (1/φ(ℓ)) ∑_{χ ≠ χ₀} χ(u₁) conj(χ(u₂))`.

Both unit hypotheses are explicit (`u₁ u₂ : (ZMod ℓ)ˣ`); see
`centeredKernel_nonunit_counterexample` for why they may not be dropped. -/
theorem centeredKernel_eq_nonprincipalCharacterSum (u₁ u₂ : (ZMod l)ˣ) :
    centeredKernel l (u₁ : ZMod l) (u₂ : ZMod l)
      = (l.totient : ℂ)⁻¹ * ∑ χ ∈ nonprincipalChars l,
          χ (u₁ : ZMod l) * (starRingEnd ℂ) (χ (u₂ : ZMod l)) := by
  rw [sum_nonprincipal_unit_pair l u₁ u₂, centeredKernel_units l u₁ u₂]
  have h := totient_ne_zero_cast l
  by_cases hu : (u₁ : ZMod l) = (u₂ : ZMod l)
  · rw [if_pos hu, if_pos hu]; field_simp
  · rw [if_neg hu, if_neg hu]; field_simp; ring

/-- **The principal character carries exactly the subtracted main term.**
Adding back the principal term turns the centered kernel into the plain
congruence indicator. -/
theorem centeredKernel_principal_removed (u₁ u₂ : (ZMod l)ˣ) :
    centeredKernel l (u₁ : ZMod l) (u₂ : ZMod l)
        + (l.totient : ℂ)⁻¹ * ((1 : DirichletCharacter ℂ l) (u₁ : ZMod l) *
            (starRingEnd ℂ) ((1 : DirichletCharacter ℂ l) (u₂ : ZMod l)))
      = (l.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ l,
          χ (u₁ : ZMod l) * (starRingEnd ℂ) (χ (u₂ : ZMod l)) := by
  have hone : (1 : DirichletCharacter ℂ l) (u₁ : ZMod l) *
      (starRingEnd ℂ) ((1 : DirichletCharacter ℂ l) (u₂ : ZMod l)) = 1 := by
    rw [principal_apply_unit l u₁, principal_apply_unit l u₂]; simp
  rw [hone, centeredKernel_eq_nonprincipalCharacterSum l u₁ u₂,
    sum_nonprincipal_unit_pair l u₁ u₂, sum_all_characters_unit_pair l u₁ u₂]
  ring

/-- **The centered projection annihilates the principal character.**
Testing a row of the centered kernel against `χ₀` gives `0`. -/
theorem centeredCharacterProjection_zeroPrincipal (u₁ : (ZMod l)ˣ) :
    ∑ u₂ : (ZMod l)ˣ,
        centeredKernel l (u₁ : ZMod l) (u₂ : ZMod l) *
          (1 : DirichletCharacter ℂ l) (u₂ : ZMod l) = 0 := by
  rw [Finset.sum_congr rfl fun u₂ _ => by rw [principal_apply_unit l u₂, mul_one]]
  exact centeredKernel_row_sum_units l u₁

/-! ## 4. Counterguard: the unit hypotheses are load-bearing -/

/-- **Counterguard.**  Off the unit sector the identity is false: for `ℓ = 4`
and `u₁ = u₂ = 2` (a non-unit) the kernel equals `1`, while every character
vanishes there, so the right-hand side is `0`. -/
theorem centeredKernel_nonunit_counterexample :
    centeredKernel 4 (2 : ZMod 4) (2 : ZMod 4)
      ≠ ((4:ℕ).totient : ℂ)⁻¹ * ∑ χ ∈ nonprincipalChars 4,
          χ (2 : ZMod 4) * (starRingEnd ℂ) (χ (2 : ZMod 4)) := by
  have hnu : ¬ IsUnit ((2 : ZMod 4) * (2 : ZMod 4)) := by decide
  have hker : centeredKernel 4 (2 : ZMod 4) (2 : ZMod 4) = 1 := by
    simp [centeredKernel, hnu]
  have hzero : ∀ χ : DirichletCharacter ℂ 4,
      χ (2 : ZMod 4) * (starRingEnd ℂ) (χ (2 : ZMod 4)) = 0 := by
    intro χ
    have : χ (2 : ZMod 4) = 0 := χ.map_nonunit (by decide)
    simp [this]
  rw [hker, Finset.sum_congr rfl fun χ _ => hzero χ]
  simp

/-! ## 5. The square bundle -/

variable {ι : Type*}

/-- The character-twisted linear form `S(χ) = ∑_i c_i χ(u_i)`. -/
noncomputable def charForm (n : ℕ) [NeZero n] (I : Finset ι) (v : ι → (ZMod n)ˣ) (c : ι → ℂ)
    (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ i ∈ I, c i * χ ((v i : ZMod n))

/-- **`centeredEnergy_eq_nonprincipalCharacterSquareBundle`.**

For arbitrary complex coefficients `c` attached to units `u_i`,

  `∑_{i,j} c_i conj(c_j) Δ_ℓ(u_i,u_j) = (1/φ(ℓ)) ∑_{χ ≠ χ₀} |S(χ)|²`.

A pure finite identity: no estimate, no positivity assumption, no support
assumption beyond the (explicit) unit sector. -/
theorem centeredEnergy_eq_nonprincipalCharacterSquareBundle
    (I : Finset ι) (v : ι → (ZMod l)ˣ) (c : ι → ℂ) :
    ∑ i ∈ I, ∑ j ∈ I,
        c i * (starRingEnd ℂ) (c j) * centeredKernel l (v i : ZMod l) (v j : ZMod l)
      = (l.totient : ℂ)⁻¹ * ∑ χ ∈ nonprincipalChars l,
          (Complex.normSq (charForm l I v c χ) : ℂ) := by
  classical
  have hsq : ∀ χ : DirichletCharacter ℂ l,
      (Complex.normSq (charForm l I v c χ) : ℂ)
        = ∑ i ∈ I, ∑ j ∈ I,
            (c i * χ ((v i : ZMod l))) * (starRingEnd ℂ) (c j * χ ((v j : ZMod l))) := by
    intro χ
    rw [← Complex.mul_conj, charForm, map_sum, Finset.sum_mul_sum]
  calc ∑ i ∈ I, ∑ j ∈ I,
        c i * (starRingEnd ℂ) (c j) * centeredKernel l (v i : ZMod l) (v j : ZMod l)
      = ∑ i ∈ I, ∑ j ∈ I, ∑ χ ∈ nonprincipalChars l,
          (l.totient : ℂ)⁻¹ *
            ((c i * χ ((v i : ZMod l))) * (starRingEnd ℂ) (c j * χ ((v j : ZMod l)))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [centeredKernel_eq_nonprincipalCharacterSum l (v i) (v j), Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_mul]; ring
    _ = ∑ χ ∈ nonprincipalChars l, ∑ i ∈ I, ∑ j ∈ I,
          (l.totient : ℂ)⁻¹ *
            ((c i * χ ((v i : ZMod l))) * (starRingEnd ℂ) (c j * χ ((v j : ZMod l)))) := by
        rw [Finset.sum_congr rfl fun i (_ : i ∈ I) => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = (l.totient : ℂ)⁻¹ * ∑ χ ∈ nonprincipalChars l,
          (Complex.normSq (charForm l I v c χ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [hsq χ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]

/-- **Summed over the modulus family.**  The bundle identity is additive in
`ℓ`, so it holds verbatim for a finite family of moduli (written with moduli
`m+1` so that `NeZero` is automatic). -/
theorem centeredEnergy_sum_over_moduli (L : Finset ℕ)
    (I : Finset ι) (v : ∀ m : ℕ, ι → (ZMod (m+1))ˣ) (c : ℕ → ι → ℂ) :
    ∑ m ∈ L, ∑ i ∈ I, ∑ j ∈ I,
        c m i * (starRingEnd ℂ) (c m j) *
          centeredKernel (m+1) (v m i : ZMod (m+1)) (v m j : ZMod (m+1))
      = ∑ m ∈ L, ((m+1).totient : ℂ)⁻¹ *
          ∑ χ ∈ nonprincipalChars (m+1),
            (Complex.normSq (charForm (m+1) I (v m) (c m) χ) : ℂ) :=
  Finset.sum_congr rfl fun m _ =>
    centeredEnergy_eq_nonprincipalCharacterSquareBundle (m+1) I (v m) (c m)

/-! ## 6. Parseval on the unit sector (Phase E, item 10) -/

/-- **Character Parseval / isometry.**  Over the *full* character family,

  `(1/φ(ℓ)) ∑_χ |S(χ)|² = ∑_{i,j : u_i ≡ u_j (ℓ)} c_i conj(c_j)`.

Exact; the unit sector is again explicit. -/
theorem characterParseval_unitSector (I : Finset ι) (v : ι → (ZMod l)ˣ) (c : ι → ℂ) :
    (l.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ l,
        (Complex.normSq (charForm l I v c χ) : ℂ)
      = ∑ i ∈ I, ∑ j ∈ I,
          (if (v i : ZMod l) = (v j : ZMod l) then c i * (starRingEnd ℂ) (c j) else 0) := by
  classical
  have hsq : ∀ χ : DirichletCharacter ℂ l,
      (Complex.normSq (charForm l I v c χ) : ℂ)
        = ∑ i ∈ I, ∑ j ∈ I,
            (c i * χ ((v i : ZMod l))) * (starRingEnd ℂ) (c j * χ ((v j : ZMod l))) := by
    intro χ
    rw [← Complex.mul_conj, charForm, map_sum, Finset.sum_mul_sum]
  have hstep : ∀ (i j : ι) (χ : DirichletCharacter ℂ l),
      (c i * χ ((v i : ZMod l))) * (starRingEnd ℂ) (c j * χ ((v j : ZMod l)))
        = (c i * (starRingEnd ℂ) (c j)) *
            (χ ((v i : ZMod l)) * (starRingEnd ℂ) (χ ((v j : ZMod l)))) := by
    intro i j χ; rw [map_mul]; ring
  have hpt : ∀ i j : ι,
      (l.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ l,
          (c i * χ ((v i : ZMod l))) * (starRingEnd ℂ) (c j * χ ((v j : ZMod l)))
        = if (v i : ZMod l) = (v j : ZMod l) then c i * (starRingEnd ℂ) (c j) else 0 := by
    intro i j
    rw [Finset.sum_congr rfl fun χ _ => hstep i j χ, ← Finset.mul_sum,
      sum_all_characters_unit_pair l (v i) (v j)]
    have h := totient_ne_zero_cast l
    by_cases hv : (v i : ZMod l) = (v j : ZMod l)
    · rw [if_pos hv, if_pos hv]; field_simp
    · rw [if_neg hv, if_neg hv]; simp
  calc (l.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ l,
        (Complex.normSq (charForm l I v c χ) : ℂ)
      = ∑ i ∈ I, ∑ j ∈ I, (l.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ l,
          (c i * χ ((v i : ZMod l))) * (starRingEnd ℂ) (c j * χ ((v j : ZMod l))) := by
        rw [Finset.sum_congr rfl fun χ (_ : χ ∈ Finset.univ) => hsq χ]
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
    _ = ∑ i ∈ I, ∑ j ∈ I,
          (if (v i : ZMod l) = (v j : ZMod l) then c i * (starRingEnd ℂ) (c j) else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j

end CharacterCentering
end CurrentProgramme
end TwinPrimeProject
