/-
# Gate 1A safe algebra bank — on-coordinate saturation (the anti-loop layer).

Gate-1A phases are *additive* characters of `ZMod m`, so the Gate-1A analogue of
the Gate-1B character-saturation certificate is stated for an arbitrary additive
homomorphism `χ : ZMod m →+ G` into an arbitrary additive commutative group.

The content is again a **tautology certificate**: once two outer states share
the projective coordinate `Z L⁻¹ (mod R)`, every character of that coordinate
takes the same value, at every tensor power and for arbitrary integer
coefficients.  No iteration of the phase identity can therefore create new
information, and in particular no saving.
-/
import Gate1A.SafeAlgebra.ProjectiveDefect

namespace Gate1A

namespace SafeAlgebra

open Finset

/-- **Saturation at one factor.**  Equal projective coordinates give equal
character values. -/
theorem coordinate_saturation {m : ℕ} {G : Type*} [AddCommGroup G]
    (chi : ZMod m →+ G) (c1 c2 : ZMod m) (h : c1 = c2) : chi c1 - chi c2 = 0 := by
  rw [h, sub_self]

/-- **On-shell saturation.**  If the modulus divides the projective defect then
the two characters of the projective coordinate agree. -/
theorem projective_coordinate_saturation {R : ℕ} {Z1 L1 Z2 L2 : ℤ} {G : Type*}
    [AddCommGroup G] (chi : ZMod R →+ G) (L1u L2u : (ZMod R)ˣ)
    (h1 : ((L1u : ZMod R)) = (L1 : ZMod R)) (h2 : ((L2u : ZMod R)) = (L2 : ZMod R))
    (hdvd : (R : ℤ) ∣ projDefect Z1 L1 Z2 L2) :
    chi ((Z1 : ZMod R) * ((L1u⁻¹ : (ZMod R)ˣ) : ZMod R))
      - chi ((Z2 : ZMod R) * ((L2u⁻¹ : (ZMod R)ˣ) : ZMod R)) = 0 :=
  coordinate_saturation chi _ _ ((proj_coordinate_zmod L1u L2u h1 h2).mp hdvd)

/-- **Saturation at every tensor power.**  Arbitrary finite index set, arbitrary
moduli, arbitrary homomorphisms, arbitrary integer coefficients (in particular
signs `±1`). -/
theorem coordinate_saturation_tensor {ι : Type*} (s : Finset ι) {G : Type*}
    [AddCommGroup G] {m : ι → ℕ} (chi : ∀ j, ZMod (m j) →+ G)
    (c1 c2 : ∀ j, ZMod (m j)) (eps : ι → ℤ) (h : ∀ j ∈ s, c1 j = c2 j) :
    ∑ j ∈ s, eps j • (chi j (c1 j) - chi j (c2 j)) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro j hj
  rw [coordinate_saturation (chi j) (c1 j) (c2 j) (h j hj), smul_zero]

/-- **On-shell saturation at every tensor power.**  Each factor comes from its
own divisibility `Rⱼ ∣ Dprojⱼ`. -/
theorem projective_saturation_tensor {ι : Type*} (s : Finset ι) {G : Type*}
    [AddCommGroup G] {R : ι → ℕ} (chi : ∀ j, ZMod (R j) →+ G)
    (Z1 L1 Z2 L2 : ι → ℤ) (L1u L2u : ∀ j, (ZMod (R j))ˣ) (eps : ι → ℤ)
    (h1 : ∀ j ∈ s, ((L1u j : ZMod (R j))) = ((L1 j : ZMod (R j))))
    (h2 : ∀ j ∈ s, ((L2u j : ZMod (R j))) = ((L2 j : ZMod (R j))))
    (hdvd : ∀ j ∈ s, ((R j : ℤ)) ∣ projDefect (Z1 j) (L1 j) (Z2 j) (L2 j)) :
    ∑ j ∈ s, eps j •
        (chi j ((Z1 j : ZMod (R j)) * (((L1u j)⁻¹ : (ZMod (R j))ˣ) : ZMod (R j)))
          - chi j ((Z2 j : ZMod (R j)) * (((L2u j)⁻¹ : (ZMod (R j))ˣ) : ZMod (R j)))) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro j hj
  rw [projective_coordinate_saturation (chi j) (L1u j) (L2u j) (h1 j hj) (h2 j hj)
    (hdvd j hj), smul_zero]

/-- Guard: saturation asserts *equality of values*, never triviality of a
value.  There are characters with nonzero value, so no saving can be read off
from the certificate alone. -/
theorem saturation_gives_no_value_information :
    ∃ (chi : ZMod 5 →+ ZMod 5) (c : ZMod 5), chi c ≠ 0 :=
  ⟨AddMonoidHom.id (ZMod 5), 1, by decide⟩

end SafeAlgebra

end Gate1A
