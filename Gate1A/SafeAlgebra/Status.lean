/-
# Gate 1A safe algebra bank — status and axiom audit.

Every principal theorem of the Gate-1A bank is listed here with
`#print axioms`; all depend on at most `propext`, `Classical.choice`,
`Quot.sound`.  No `sorry`, no user axiom, no analytic claim.
-/
import Gate1A.SafeAlgebra.ProjectiveDefect
import Gate1A.SafeAlgebra.Saturation
import Gate1A.SafeAlgebra.Interfaces

namespace Gate1A

namespace SafeAlgebra

-- exact identities for the outer projective defect
#print axioms projDefect_eq_zero_iff
#print axioms projDefect_eq_zero_iff_ratioClass
#print axioms projDefect_pb_expansion
#print axioms dvd_projDefect_of_dvd_moduli

-- projective rigidity (zero-defect lemma) and its guard
#print axioms projective_zero_defect_rigidity
#print axioms projective_rigidity_needs_primitivity

-- additive projective coordinate
#print axioms proj_coordinate_int
#print axioms proj_coordinate_zmod

-- local prime-square lift and CRT product
#print axioms proj_local_prime_square_lift
#print axioms four_prime_projDefect_iff
#print axioms four_local_projective_collision

-- finite counting facts
#print axioms card_projective_fibre
#print axioms card_projective_diagonal

-- anti-Cartesian guards
#print axioms collision_relation_not_cartesian
#print axioms projective_sum_ne_cartesian_sum

-- saturation (anti-loop certificate)
#print axioms coordinate_saturation
#print axioms projective_coordinate_saturation
#print axioms coordinate_saturation_tensor
#print axioms projective_saturation_tensor
#print axioms saturation_gives_no_value_information

end SafeAlgebra

end Gate1A
