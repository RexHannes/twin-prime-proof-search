import Mathlib
import RequestProject.CurrentProgramme.EndpointCharacterCentering
import RequestProject.CurrentProgramme.EndpointCharacterTransfer

/-!
# Source-minimal character pairing (operator bank, Phase A)

The source-minimal object is a **bilinear pairing**, not a square:

```
∑_a A(ℓ,a,k) conj(E(ℓ,a,k))  =  (1/φ(ℓ)) ∑_{χ ≠ χ₀} Â(ℓ,χ,k) conj(Ê(ℓ,χ,k)),
```

valid on the unit sector once the `E`-side has canonical zero mean.  Squaring
via Cauchy–Schwarz produces the previously banked character *square* bundle:
that step is a **sufficient strengthening**, recorded here as
`characterSquare_is_Cauchy_strengthening`, and the square socket is *not* marked
false.

Also banked:

* the `A`-side residue source `A(a) = ∑_{u : -2 u⁻¹ = a} c(u)` and its exact
  character transform `AHat_eq`;
* the canonical zero-mean `E`-source and the *uninhabited*
  `FiveDefectResidueSourceAdapter` identifying it with the physical five-defect
  residue discrepancy.

No analytic estimate anywhere.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace CharPairing

open Finset CharacterCentering

variable {n : ℕ} [NeZero n]

/-! ## 1. The `A`-side residue source -/

/-- The residue source `A(a) = ∑_{u : w·u⁻¹ = a} c(u)`, where `w` is the unit
representing `-2`. -/
noncomputable def residueSource (w : (ZMod n)ˣ) (c : (ZMod n)ˣ → ℂ)
    (a : (ZMod n)ˣ) : ℂ :=
  ∑ u ∈ Finset.univ.filter (fun u : (ZMod n)ˣ => w * u⁻¹ = a), c u

/-- The residue fibre is a singleton. -/
theorem residue_fibre (w a : (ZMod n)ˣ) :
    Finset.univ.filter (fun u : (ZMod n)ˣ => w * u⁻¹ = a) = {w * a⁻¹} := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    rw [← h, mul_inv_rev, inv_inv, mul_comm u w⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  · intro h
    rw [h, mul_inv_rev, inv_inv, mul_comm a w⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Hence the residue source is just a relabelling of the coefficient. -/
theorem residueSource_eq (w : (ZMod n)ˣ) (c : (ZMod n)ˣ → ℂ) (a : (ZMod n)ˣ) :
    residueSource w c a = c (w * a⁻¹) := by
  rw [residueSource, residue_fibre, Finset.sum_singleton]

/-! ## 2. Character transforms -/

/-- The character transform on the unit sector,
`ĉ(χ) = ∑_a c(a) conj(χ(a))`. -/
noncomputable def charTransform (c : (ZMod n)ˣ → ℂ) (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ a : (ZMod n)ˣ, c a * (starRingEnd ℂ) (χ (a : ZMod n))

/-- **`AHat_eq`.**  The transform of the residue source is the plain character
sum of the coefficient, twisted by `conj(χ(-2))`. -/
theorem AHat_eq (w : (ZMod n)ˣ) (hw : (w : ZMod n) = -2) (c : (ZMod n)ˣ → ℂ)
    (χ : DirichletCharacter ℂ n) :
    charTransform (residueSource w c) χ
      = (starRingEnd ℂ) (χ (-2)) * ∑ u : (ZMod n)ˣ, c u * χ (u : ZMod n) := by
  have hconjw : (starRingEnd ℂ) (χ (w : ZMod n)) = χ ((w⁻¹ : (ZMod n)ˣ) : ZMod n) :=
    conj_apply_unit n χ w
  have hwinv : χ (w : ZMod n) * χ ((w⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
    rw [← map_mul]; norm_cast; simp
  -- the reindexing `a ↦ w * a⁻¹`
  let E : (ZMod n)ˣ ≃ (ZMod n)ˣ := (Equiv.inv _).trans (Equiv.mulLeft w)
  have hterm : ∀ a : (ZMod n)ˣ,
      residueSource w c a * (starRingEnd ℂ) (χ (a : ZMod n))
        = c (E a) * χ ((E a : (ZMod n)ˣ) : ZMod n) *
            (starRingEnd ℂ) (χ (w : ZMod n)) := by
    intro a
    have hEa : E a = w * a⁻¹ := rfl
    have hchi : χ ((w * a⁻¹ : (ZMod n)ˣ) : ZMod n)
        = χ (w : ZMod n) * χ ((a⁻¹ : (ZMod n)ˣ) : ZMod n) := by
      rw [Units.val_mul, map_mul]
    have hainv : χ ((a⁻¹ : (ZMod n)ˣ) : ZMod n) = (starRingEnd ℂ) (χ (a : ZMod n)) :=
      (conj_apply_unit n χ a).symm
    rw [hEa, residueSource_eq, hchi, hainv]
    calc c (w * a⁻¹) * (starRingEnd ℂ) (χ (a : ZMod n))
        = c (w * a⁻¹) * (starRingEnd ℂ) (χ (a : ZMod n)) *
            (χ (w : ZMod n) * (starRingEnd ℂ) (χ (w : ZMod n))) := by
          rw [hconjw, hwinv, mul_one]
      _ = c (w * a⁻¹) * (χ (w : ZMod n) * (starRingEnd ℂ) (χ (a : ZMod n))) *
            (starRingEnd ℂ) (χ (w : ZMod n)) := by ring
  have hreindex : ∑ a : (ZMod n)ˣ, c (E a) * χ ((E a : (ZMod n)ˣ) : ZMod n) *
        (starRingEnd ℂ) (χ (w : ZMod n))
      = ∑ u : (ZMod n)ˣ, c u * χ (u : ZMod n) * (starRingEnd ℂ) (χ (w : ZMod n)) :=
    Fintype.sum_equiv E _ _ (fun a => rfl)
  rw [charTransform,
    Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hterm a, hreindex,
    ← Finset.sum_mul, hw]
  ring

/-! ## 3. The canonical zero-mean `E`-source -/

/-- A canonical residue source with zero mean over the unit sector. -/
structure CanonicalZeroMeanSource (n : ℕ) [NeZero n] where
  /-- The residue values. -/
  E : (ZMod n)ˣ → ℂ
  /-- The canonical centering condition. -/
  zero_mean : ∑ a : (ZMod n)ˣ, E a = 0

/-- **`FiveDefectResidueSourceAdapter`.**  Identification of the *physical*
five-defect residue discrepancy with a canonical zero-mean source.

`SOURCE_OPEN / UNINHABITED`: the physical historical / local-density
discrepancy is not available in this repository, so this adapter is never
constructed. -/
structure FiveDefectResidueSourceAdapter (n : ℕ) [NeZero n]
    (physical : (ZMod n)ˣ → ℂ) (canonical : CanonicalZeroMeanSource n) where
  /-- The identification.  NOT SUPPLIED. -/
  identified : ∀ a, physical a = canonical.E a

/-- **`fiveDefectAdapter_not_automatic`.**  A physical source without zero mean
cannot be adapted: the interface is then empty. -/
theorem fiveDefectAdapter_not_automatic (canonical : CanonicalZeroMeanSource n)
    (physical : (ZMod n)ˣ → ℂ) (hsum : ∑ a : (ZMod n)ˣ, physical a ≠ 0) :
    IsEmpty (FiveDefectResidueSourceAdapter n physical canonical) := by
  constructor
  rintro ⟨h⟩
  exact hsum ((Finset.sum_congr rfl fun a _ => h a).trans canonical.zero_mean)

/-! ## 4. The exact pairing identity -/

/-- Full orthogonality pairing: summing over **all** characters. -/
theorem fullCharacterPairing (c e : (ZMod n)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ n, charTransform c χ * (starRingEnd ℂ) (charTransform e χ)
      = (n.totient : ℂ) * ∑ a : (ZMod n)ˣ, c a * (starRingEnd ℂ) (e a) := by
  have hexpand : ∀ χ : DirichletCharacter ℂ n,
      charTransform c χ * (starRingEnd ℂ) (charTransform e χ)
        = ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ,
            c a * (starRingEnd ℂ) (e b) *
              (χ (b : ZMod n) * (starRingEnd ℂ) (χ (a : ZMod n))) := by
    intro χ
    rw [charTransform, charTransform, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    ring
  rw [Finset.sum_congr rfl fun χ (_ : χ ∈ Finset.univ) => hexpand χ]
  rw [Finset.sum_comm]
  have hswap : ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ,
      ∑ χ : DirichletCharacter ℂ n, c a * (starRingEnd ℂ) (e b) *
          (χ (b : ZMod n) * (starRingEnd ℂ) (χ (a : ZMod n)))
      = ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ,
          c a * (starRingEnd ℂ) (e b) *
            (if (b : ZMod n) = (a : ZMod n) then (n.totient : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, sum_all_characters_unit_pair n b a]
  rw [show (∑ a : (ZMod n)ˣ, ∑ χ : DirichletCharacter ℂ n, ∑ b : (ZMod n)ˣ,
        c a * (starRingEnd ℂ) (e b) *
          (χ (b : ZMod n) * (starRingEnd ℂ) (χ (a : ZMod n))))
      = ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ, ∑ χ : DirichletCharacter ℂ n,
          c a * (starRingEnd ℂ) (e b) *
            (χ (b : ZMod n) * (starRingEnd ℂ) (χ (a : ZMod n))) from
    Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [hswap]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hunit : ∀ b : (ZMod n)ˣ,
      (if (b : ZMod n) = (a : ZMod n) then (n.totient : ℂ) else 0)
        = (if b = a then (n.totient : ℂ) else 0) := by
    intro b
    by_cases hb : b = a
    · simp [hb]
    · have : (b : ZMod n) ≠ (a : ZMod n) := fun hc => hb (Units.ext hc)
      simp [hb, this]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => by rw [hunit b]]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ a
    (fun b => c a * (starRingEnd ℂ) (e b) * (n.totient : ℂ))]
  simp only [Finset.mem_univ, if_true]
  ring

/-- **`centeredPairing_eq_nonprincipalCharacterPairing`.**  On the unit sector,
with the `E`-side canonically centered, the physical pairing equals the
non-principal character pairing. -/
theorem centeredPairing_eq_nonprincipalCharacterPairing (c : (ZMod n)ˣ → ℂ)
    (S : CanonicalZeroMeanSource n) :
    ((n.totient : ℂ))⁻¹ * ∑ χ ∈ nonprincipalChars n,
        charTransform c χ * (starRingEnd ℂ) (charTransform S.E χ)
      = ∑ a : (ZMod n)ˣ, c a * (starRingEnd ℂ) (S.E a) := by
  have hprincipal : charTransform S.E (1 : DirichletCharacter ℂ n) = 0 := by
    rw [charTransform]
    have : ∀ a : (ZMod n)ˣ,
        S.E a * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ n) (a : ZMod n)) = S.E a := by
      intro a; rw [principal_apply_unit n a]; simp
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => this a, S.zero_mean]
  have hsplit : ∑ χ : DirichletCharacter ℂ n,
      charTransform c χ * (starRingEnd ℂ) (charTransform S.E χ)
      = charTransform c 1 * (starRingEnd ℂ) (charTransform S.E 1)
        + ∑ χ ∈ nonprincipalChars n,
            charTransform c χ * (starRingEnd ℂ) (charTransform S.E χ) := by
    rw [nonprincipalChars, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ n))]
  have hfull := fullCharacterPairing c S.E
  rw [hsplit, hprincipal] at hfull
  simp only [map_zero, mul_zero, zero_add] at hfull
  rw [hfull, ← mul_assoc, inv_mul_cancel₀ (totient_ne_zero_cast n), one_mul]

/-! ## 5. Cauchy strengthening firewall -/

/-- The non-principal square bundle of a coefficient family. -/
noncomputable def squareBundle (c : (ZMod n)ˣ → ℂ) : ℝ :=
  ((n.totient : ℝ))⁻¹ * ∑ χ ∈ nonprincipalChars n, ‖charTransform c χ‖ ^ 2

theorem squareBundle_nonneg (c : (ZMod n)ˣ → ℂ) : 0 ≤ squareBundle c := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun χ _ => by positivity)

/-- **`characterSquare_is_Cauchy_strengthening`.**  Cauchy–Schwarz applied to the
source-minimal pairing produces the character *square* bundles.  The square
object is therefore a **sufficient strengthening**, not the source-minimal
target itself. -/
theorem characterSquare_is_Cauchy_strengthening (c : (ZMod n)ˣ → ℂ)
    (S : CanonicalZeroMeanSource n) :
    ‖∑ a : (ZMod n)ˣ, c a * (starRingEnd ℂ) (S.E a)‖
      ≤ Real.sqrt (squareBundle c) * Real.sqrt (squareBundle S.E) := by
  classical
  set t : ℝ := ((n.totient : ℝ))⁻¹ with ht
  have htpos : 0 < (n.totient : ℝ) := by
    have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast Nat.totient_pos.2 hpos
  have ht0 : 0 ≤ t := by positivity
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0
  -- Step 1: the pairing is the non-principal character pairing
  have hpair := centeredPairing_eq_nonprincipalCharacterPairing c S
  have hnorm : ‖∑ a : (ZMod n)ˣ, c a * (starRingEnd ℂ) (S.E a)‖
      ≤ t * ∑ χ ∈ nonprincipalChars n,
          ‖charTransform c χ‖ * ‖charTransform S.E χ‖ := by
    rw [← hpair]
    have hnormcast : ‖(((n.totient : ℂ)))⁻¹‖ = t := by
      rw [norm_inv, ht]
      congr 1
      simp
    calc ‖((n.totient : ℂ))⁻¹ * ∑ χ ∈ nonprincipalChars n,
            charTransform c χ * (starRingEnd ℂ) (charTransform S.E χ)‖
        = t * ‖∑ χ ∈ nonprincipalChars n,
            charTransform c χ * (starRingEnd ℂ) (charTransform S.E χ)‖ := by
          rw [norm_mul, hnormcast]
      _ ≤ t * ∑ χ ∈ nonprincipalChars n,
            ‖charTransform c χ * (starRingEnd ℂ) (charTransform S.E χ)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) ht0
      _ = t * ∑ χ ∈ nonprincipalChars n,
            ‖charTransform c χ‖ * ‖charTransform S.E χ‖ := by
          congr 1
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [norm_mul, RCLike.norm_conj]
  -- Step 2: weighted Cauchy–Schwarz
  set f : DirichletCharacter ℂ n → ℝ :=
    fun χ => Real.sqrt t * ‖charTransform c χ‖ with hf
  set g : DirichletCharacter ℂ n → ℝ :=
    fun χ => Real.sqrt t * ‖charTransform S.E χ‖ with hg
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (nonprincipalChars n) f g
  have hfg : ∑ χ ∈ nonprincipalChars n, f χ * g χ
      = t * ∑ χ ∈ nonprincipalChars n,
          ‖charTransform c χ‖ * ‖charTransform S.E χ‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hf, hg]
    calc Real.sqrt t * ‖charTransform c χ‖ * (Real.sqrt t * ‖charTransform S.E χ‖)
        = (Real.sqrt t * Real.sqrt t) *
            (‖charTransform c χ‖ * ‖charTransform S.E χ‖) := by ring
      _ = t * (‖charTransform c χ‖ * ‖charTransform S.E χ‖) := by rw [hs]
  have hf2 : ∑ χ ∈ nonprincipalChars n, f χ ^ 2 = squareBundle c := by
    rw [squareBundle, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hf]
    calc (Real.sqrt t * ‖charTransform c χ‖) ^ 2
        = (Real.sqrt t * Real.sqrt t) * ‖charTransform c χ‖ ^ 2 := by ring
      _ = t * ‖charTransform c χ‖ ^ 2 := by rw [hs]
  have hg2 : ∑ χ ∈ nonprincipalChars n, g χ ^ 2 = squareBundle S.E := by
    rw [squareBundle, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hg]
    calc (Real.sqrt t * ‖charTransform S.E χ‖) ^ 2
        = (Real.sqrt t * Real.sqrt t) * ‖charTransform S.E χ‖ ^ 2 := by ring
      _ = t * ‖charTransform S.E χ‖ ^ 2 := by rw [hs]
  rw [hfg, hf2, hg2] at hcauchy
  -- Step 3: conclude
  have hnn : 0 ≤ t * ∑ χ ∈ nonprincipalChars n,
      ‖charTransform c χ‖ * ‖charTransform S.E χ‖ :=
    mul_nonneg ht0 (Finset.sum_nonneg fun χ _ => by positivity)
  have hBnn : 0 ≤ squareBundle c * squareBundle S.E :=
    mul_nonneg (squareBundle_nonneg c) (squareBundle_nonneg S.E)
  have hsq : (t * ∑ χ ∈ nonprincipalChars n,
      ‖charTransform c χ‖ * ‖charTransform S.E χ‖)
      ≤ Real.sqrt (squareBundle c * squareBundle S.E) :=
    (Real.le_sqrt hnn hBnn).2 hcauchy
  have hsplit : Real.sqrt (squareBundle c * squareBundle S.E)
      = Real.sqrt (squareBundle c) * Real.sqrt (squareBundle S.E) :=
    Real.sqrt_mul (squareBundle_nonneg c) _
  exact le_trans hnorm (le_trans hsq (le_of_eq hsplit))

end CharPairing
end CurrentProgramme
end TwinPrimeProject
