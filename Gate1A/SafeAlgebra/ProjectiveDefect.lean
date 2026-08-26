/-
# Gate 1A safe algebra bank — the outer projective defect.

This is the Gate-1A counterpart of the Gate-1B `C45` layer.  The Gate-1A outer
state is the pair `(Z, L)` with `Z = Q a + P₀ n` (the corrected PB coordinate of
`Gate1A/Delta4/PBAxis.lean`), and the collision relation of the generic sector
is `Z₁ L₂ = Z₂ L₁` (`Gate1A/Delta4/Projective.lean`).  Its **defect** is

  `Dproj = Z₁ L₂ − Z₂ L₁`.

Banked here, all exact and finite:

* the PB expansion of the defect;
* projective rigidity: `Dproj = 0` with primitive positive representatives
  forces `(Z₁, L₁) = (Z₂, L₂)`, with a countermodel showing primitivity is
  load-bearing;
* the additive projective coordinate `Z L⁻¹ (mod R)`, in unit form and in
  explicit-integer-inverse form;
* the local prime-square lift and the CRT product over four labelled primes;
* the anti-Cartesian guard for the collision relation.

Nothing analytic is asserted: no Plancherel, no large sieve, no equidistribution
of the projective coordinate, no bound on any sector mass.

Generic finite lemmas are reused from the Gate-1B bank rather than duplicated
(`Gate1B.dvd_mul_left_iff_of_inv`, `Gate1B.prod_sq_dvd_iff`,
`Gate1B.card_local_diagonal`, `Gate1B.shell_sum_ne_cartesian_sum`).
-/
import Mathlib
import Gate1A.Delta4.PBAxis
import Gate1A.Delta4.Projective
import Gate1B.AdditiveCoordinate
import Gate1B.CRTProduct
import Gate1B.LocalDensity
import Gate1B.AntiCartesian

namespace Gate1A

namespace SafeAlgebra

open Finset

/-- The outer projective defect `Dproj = Z₁ L₂ − Z₂ L₁`. -/
def projDefect (Z1 L1 Z2 L2 : ℤ) : ℤ := Z1 * L2 - Z2 * L1

/-! ## Exact identities -/

/-- The defect vanishes exactly on the collision relation. -/
theorem projDefect_eq_zero_iff {Z1 L1 Z2 L2 : ℤ} :
    projDefect Z1 L1 Z2 L2 = 0 ↔ Z1 * L2 = Z2 * L1 := by
  unfold projDefect
  constructor <;> intro h <;> linarith

/-- On the generic sector (`L ≠ 0`) the defect vanishes exactly when the two
states have the same projective class, in the sense of
`Gate1A.Delta4.ratioClass`. -/
theorem projDefect_eq_zero_iff_ratioClass {Z1 L1 Z2 L2 : ℤ} (h1 : L1 ≠ 0) (h2 : L2 ≠ 0) :
    projDefect Z1 L1 Z2 L2 = 0 ↔
      Delta4.ratioClass Z1 L1 = Delta4.ratioClass Z2 L2 := by
  rw [projDefect_eq_zero_iff, Delta4.ratioClass_eq_iff_cross h1 h2]

/-- **PB expansion of the defect.**  With `Zᵢ = Q aᵢ + P₀ nᵢ`,
`Dproj = Q (a₁L₂ − a₂L₁) + P₀ (n₁L₂ − n₂L₁)`, exactly. -/
theorem projDefect_pb_expansion (P0 Q a1 n1 a2 n2 L1 L2 : ℤ) :
    projDefect (Delta4.pbZ P0 Q a1 n1) L1 (Delta4.pbZ P0 Q a2 n2) L2
      = Q * (a1 * L2 - a2 * L1) + P0 * (n1 * L2 - n2 * L1) := by
  unfold projDefect Delta4.pbZ
  ring

/-- A common divisor of the two PB moduli divides the defect. -/
theorem dvd_projDefect_of_dvd_moduli {d P0 Q : ℤ} (hQ : d ∣ Q) (hP : d ∣ P0)
    (a1 n1 a2 n2 L1 L2 : ℤ) :
    d ∣ projDefect (Delta4.pbZ P0 Q a1 n1) L1 (Delta4.pbZ P0 Q a2 n2) L2 := by
  rw [projDefect_pb_expansion]
  exact dvd_add (Dvd.dvd.mul_right hQ _) (Dvd.dvd.mul_right hP _)

/-! ## Projective rigidity (the Gate-1A zero-defect lemma) -/

/-- **Projective rigidity.**  For positive `L₁, L₂` and *primitive*
representatives (`gcd(Zᵢ, Lᵢ) = 1`), a vanishing defect forces the two states to
be literally equal. -/
theorem projective_zero_defect_rigidity {Z1 L1 Z2 L2 : ℤ} (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hp1 : IsCoprime Z1 L1) (hp2 : IsCoprime Z2 L2)
    (hD : projDefect Z1 L1 Z2 L2 = 0) : Z1 = Z2 ∧ L1 = L2 := by
  rw [projDefect_eq_zero_iff] at hD
  have h12 : L1 ∣ L2 := by
    have hdvd : L1 ∣ Z1 * L2 := ⟨Z2, by rw [hD]; ring⟩
    exact hp1.symm.dvd_of_dvd_mul_left hdvd
  have h21 : L2 ∣ L1 := by
    have hdvd : L2 ∣ Z2 * L1 := ⟨Z1, by rw [← hD]; ring⟩
    exact hp2.symm.dvd_of_dvd_mul_left hdvd
  have hL : L1 = L2 := Int.dvd_antisymm hL1.le hL2.le h12 h21
  subst hL
  refine ⟨?_, rfl⟩
  have hne : L1 ≠ 0 := ne_of_gt hL1
  exact mul_right_cancel₀ hne hD

/-- Guard: primitivity is load-bearing.  `(Z, L) = (1, 2)` and `(2, 4)` have
vanishing defect and positive `L`'s, but are different states. -/
theorem projective_rigidity_needs_primitivity :
    projDefect 1 2 2 4 = 0 ∧ (0 : ℤ) < 2 ∧ (0 : ℤ) < 4 ∧ ((1 : ℤ), (2 : ℤ)) ≠ (2, 4) := by
  refine ⟨by norm_num [projDefect], by norm_num, by norm_num, by simp⟩

/-! ## The additive projective coordinate `Z L⁻¹ (mod R)` -/

/-- **Additive projective coordinate, integer form.**  With explicit inverses
`Lᵢ'` modulo `R`, `R ∣ Dproj ↔ Z₁L₁' ≡ Z₂L₂' (mod R)`. -/
theorem proj_coordinate_int {R Z1 L1 Z2 L2 L1' L2' : ℤ}
    (h1 : R ∣ (L1 * L1' - 1)) (h2 : R ∣ (L2 * L2' - 1)) :
    R ∣ projDefect Z1 L1 Z2 L2 ↔ R ∣ (Z1 * L1' - Z2 * L2') := by
  have key : L1 * L2 * (Z1 * L1' - Z2 * L2') - projDefect Z1 L1 Z2 L2
      = (Z1 * L2) * (L1 * L1' - 1) - (Z2 * L1) * (L2 * L2' - 1) := by
    unfold projDefect; ring
  have hdiff : R ∣ (L1 * L2 * (Z1 * L1' - Z2 * L2') - projDefect Z1 L1 Z2 L2) := by
    rw [key]
    exact dvd_sub (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)
  have hunit : R ∣ (L1 * L2) * (L1' * L2') - 1 := by
    have hrw : (L1 * L2) * (L1' * L2') - 1
        = (L1 * L1' - 1) * (L2 * L2') + (L2 * L2' - 1) := by ring
    rw [hrw]
    exact dvd_add (Dvd.dvd.mul_right h1 _) h2
  constructor
  · intro hD
    have hsum := dvd_add hD hdiff
    simp only [add_sub_cancel] at hsum
    exact (Gate1B.dvd_mul_left_iff_of_inv hunit).mp (by simpa using hsum)
  · intro hE
    have h3 : R ∣ L1 * L2 * (Z1 * L1' - Z2 * L2') := Dvd.dvd.mul_left hE _
    simpa using dvd_sub h3 hdiff

/-- **Additive projective coordinate, unit form in `ZMod R`.** -/
theorem proj_coordinate_zmod {R : ℕ} {Z1 L1 Z2 L2 : ℤ} (L1u L2u : (ZMod R)ˣ)
    (h1 : ((L1u : ZMod R)) = (L1 : ZMod R)) (h2 : ((L2u : ZMod R)) = (L2 : ZMod R)) :
    ((R : ℤ) ∣ projDefect Z1 L1 Z2 L2) ↔
      ((Z1 : ZMod R) * ((L1u⁻¹ : (ZMod R)ˣ) : ZMod R)
        = (Z2 : ZMod R) * ((L2u⁻¹ : (ZMod R)ˣ) : ZMod R)) := by
  have hinv1 : (L1 : ZMod R) * ((L1u⁻¹ : (ZMod R)ˣ) : ZMod R) = 1 := by
    rw [← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv2 : (L2 : ZMod R) * ((L2u⁻¹ : (ZMod R)ˣ) : ZMod R) = 1 := by
    rw [← h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hu : IsUnit ((L1 : ZMod R) * (L2 : ZMod R)) := by
    rw [← h1, ← h2, ← Units.val_mul]; exact Units.isUnit _
  have hcast : ((projDefect Z1 L1 Z2 L2 : ℤ) : ZMod R)
      = (L1 : ZMod R) * (L2 : ZMod R) *
        ((Z1 : ZMod R) * ((L1u⁻¹ : (ZMod R)ˣ) : ZMod R)
          - (Z2 : ZMod R) * ((L2u⁻¹ : (ZMod R)ˣ) : ZMod R)) := by
    unfold projDefect
    push_cast
    linear_combination (-(Z1 : ZMod R) * (L2 : ZMod R)) * hinv1
      + ((Z2 : ZMod R) * (L1 : ZMod R)) * hinv2
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast, hu.mul_right_eq_zero, sub_eq_zero]

/-! ## Local prime-square lift for the projective coordinate -/

/-- **Local prime-square lift (Gate-1A form).**  If both projective coordinates
have the same leading residue `c` at `s` and local jets `xᵢ`, then
`s² ∣ Dproj ↔ x₁ ≡ x₂ (mod s)`. -/
theorem proj_local_prime_square_lift {s Z1 L1 Z2 L2 L1' L2' c x1 x2 : ℤ} (hs : s ≠ 0)
    (hinv1 : s ^ 2 ∣ (L1 * L1' - 1)) (hinv2 : s ^ 2 ∣ (L2 * L2' - 1))
    (hz1 : s ^ 2 ∣ (Z1 * L1' - (c + s * x1)))
    (hz2 : s ^ 2 ∣ (Z2 * L2' - (c + s * x2))) :
    s ^ 2 ∣ projDefect Z1 L1 Z2 L2 ↔ s ∣ (x1 - x2) := by
  rw [proj_coordinate_int hinv1 hinv2]
  have hsplit : Z1 * L1' - Z2 * L2'
      = s * (x1 - x2) + ((Z1 * L1' - (c + s * x1)) - (Z2 * L2' - (c + s * x2))) := by
    ring
  rw [hsplit]
  constructor
  · intro h
    have h2 : s ^ 2 ∣ s * (x1 - x2) := by
      have := dvd_sub h (dvd_sub hz1 hz2)
      simpa using this
    exact (Gate1B.sq_dvd_mul_iff hs).mp h2
  · intro h
    exact dvd_add ((Gate1B.sq_dvd_mul_iff hs).mpr h) (dvd_sub hz1 hz2)

/-! ## CRT product over four labelled primes -/

/-- **Four labelled primes.**  For pairwise distinct primes `sᵢ` and
`u = s₀s₁s₂s₃`, `u² ∣ Dproj ↔ sᵢ² ∣ Dproj` for every `i`. -/
theorem four_prime_projDefect_iff (s : Fin 4 → ℕ) (hp : ∀ i, (s i).Prime)
    (hinj : Function.Injective s) (Z1 L1 Z2 L2 : ℤ) :
    ((∏ i, (s i : ℤ)) ^ 2 ∣ projDefect Z1 L1 Z2 L2) ↔
      ∀ i, ((s i : ℤ)) ^ 2 ∣ projDefect Z1 L1 Z2 L2 :=
  Gate1B.four_prime_sq_dvd_iff s hp hinj _

/-- **Exact four-local projective collision.**  Combining the two previous
theorems: with local inverses and local jets at each place,
`u² ∣ Dproj ↔ ∀ i, x₁ᵢ ≡ x₂ᵢ (mod sᵢ)`.  No independence between the four
conditions is inferred (see `Gate1B.local_conditions_not_independent`). -/
theorem four_local_projective_collision {Z1 L1 Z2 L2 : ℤ} (s : Fin 4 → ℕ)
    (hp : ∀ i, (s i).Prime) (hinj : Function.Injective s)
    (L1' L2' c x1 x2 : Fin 4 → ℤ)
    (hinv1 : ∀ i, ((s i : ℤ)) ^ 2 ∣ (L1 * L1' i - 1))
    (hinv2 : ∀ i, ((s i : ℤ)) ^ 2 ∣ (L2 * L2' i - 1))
    (hz1 : ∀ i, ((s i : ℤ)) ^ 2 ∣ (Z1 * L1' i - (c i + (s i : ℤ) * x1 i)))
    (hz2 : ∀ i, ((s i : ℤ)) ^ 2 ∣ (Z2 * L2' i - (c i + (s i : ℤ) * x2 i))) :
    ((∏ i, (s i : ℤ)) ^ 2 ∣ projDefect Z1 L1 Z2 L2) ↔ ∀ i, ((s i : ℤ)) ∣ (x1 i - x2 i) := by
  rw [four_prime_projDefect_iff s hp hinj]
  constructor
  · intro h i
    have hs : ((s i : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr (hp i).ne_zero
    exact (proj_local_prime_square_lift hs (hinv1 i) (hinv2 i) (hz1 i) (hz2 i)).mp (h i)
  · intro h i
    have hs : ((s i : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr (hp i).ne_zero
    exact (proj_local_prime_square_lift hs (hinv1 i) (hinv2 i) (hz1 i) (hz2 i)).mpr (h i)

/-! ## Local counting facts (finite, not analytic) -/

/-- For a fixed unit `L` modulo `s`, each value of the projective coordinate
`Z ↦ Z L⁻¹` is attained by exactly one `Z`. -/
theorem card_projective_fibre (s : ℕ) [NeZero s] (L : (ZMod s)ˣ) (c : ZMod s) :
    (Finset.univ.filter (fun Z : ZMod s => Z * ((L⁻¹ : (ZMod s)ˣ) : ZMod s) = c)).card = 1 := by
  refine Finset.card_eq_one.mpr ⟨c * (L : ZMod s), ?_⟩
  ext Z
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    rw [← h, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  · rintro rfl
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

/-- The diagonal of the pair of projective coordinates over `𝔽_s` has exactly
`s` points (reused from the Gate-1B bank), i.e. normalised density `1/s`.
A counting fact only. -/
theorem card_projective_diagonal (s : ℕ) [NeZero s] :
    (Finset.univ.filter (fun p : ZMod s × ZMod s => p.1 = p.2)).card = s :=
  Gate1B.card_local_diagonal s

/-! ## Anti-Cartesian guard for the collision relation -/

/-- The collision relation is **not** the Cartesian product of its projections:
the states `(Z, L) = (1, 1)` and `(2, 2)` collide, yet the mixed pair
`(Z, L) = (1, 2)` taken from the same projections does not collide with
`(2, 2)`. -/
theorem collision_relation_not_cartesian :
    projDefect 1 1 2 2 = 0 ∧ projDefect 1 2 2 2 ≠ 0 := by
  refine ⟨by norm_num [projDefect], by norm_num [projDefect]⟩

/-- Summation form of the same guard, specialised from the Gate-1B
anti-Cartesian lemma to Gate-1A outer data: summing a weight over the two-state
collision set is not summing it over the product of the `Z`-set and the
`L`-set. -/
theorem projective_sum_ne_cartesian_sum :
    ∃ F : ℤ → ℤ → ℤ,
      ∑ p ∈ ({((1 : ℤ), (1 : ℤ)), ((2 : ℤ), (2 : ℤ))} : Finset (ℤ × ℤ)), F p.1 p.2
        ≠ ∑ Z ∈ ({(1 : ℤ), 2} : Finset ℤ), ∑ L ∈ ({(1 : ℤ), 2} : Finset ℤ), F Z L :=
  Gate1B.shell_sum_ne_cartesian_sum 1 2 1 2 (by norm_num) (by norm_num)

end SafeAlgebra

end Gate1A
