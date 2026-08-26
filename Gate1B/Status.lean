/-
# Gate 1B safe algebra bank — status and axiom audit.

Every principal theorem of the bank is listed here with `#print axioms`.  All of
them depend on at most `propext`, `Classical.choice`, `Quot.sound`; several
depend on no axioms at all.  There are no `sorry`s, no user axioms, no
`opaque`s, and no analytic claims in the whole `Gate1B` library.
-/
import Gate1B.Shell
import Gate1B.CharacterSaturation
import Gate1B.C45
import Gate1B.AdditiveCoordinate
import Gate1B.PrimeSquareLift
import Gate1B.LocalDensity
import Gate1B.CRTProduct
import Gate1B.AntiCartesian
import Gate1B.Interfaces

namespace Gate1B

-- §1 integer shell
#print axioms shell_sub
#print axioms shell_eq_iff_shell_sub

-- §2 mod-r² shell congruence (S1)
#print axioms isUnit_intCast_of_isCoprime
#print axioms shell_unit_form
#print axioms shell_mod_rsq

-- §3 character saturation (SAT1, SAT-k)
#print axioms on_shell_character_saturation
#print axioms shell_character_saturation
#print axioms on_shell_character_saturation_tensor
#print axioms on_shell_character_saturation_signs
#print axioms shell_character_saturation_tensor
#print axioms saturation_gives_no_value_information

-- §4–§5 C45 identity and divisibility equivalence
#print axioms c45_identity
#print axioms c45_sq_dvd_of_dvd
#print axioms dvd_of_c45_sq_dvd
#print axioms c45_dvd_iff
#print axioms c45_converse_needs_u_ne_zero

-- §6 zero-defect diagonal lemma
#print axioms q_eq_of_defect_zero_of_l_eq
#print axioms zero_defect_diagonal
#print axioms zero_defect_needs_size_hypothesis

-- §7 additive square-modulus coordinate
#print axioms add_c45_int
#print axioms add_c45_zmod
#print axioms add_c45_rsq
#print axioms exists_inv_mod_sq

-- §8 local prime-square lift
#print axioms local_prime_square_lift
#print axioms exists_local_lift_coordinate
#print axioms local_lift_of_shell

-- §9 local density count
#print axioms card_local_diagonal
#print axioms card_local_square
#print axioms local_density_eq
#print axioms local_diagonal_density

-- §10 CRT product over four labelled primes
#print axioms prod_sq_dvd_iff
#print axioms four_prime_sq_dvd_iff
#print axioms four_local_collision
#print axioms local_conditions_not_independent

-- §11 anti-Cartesian guard
#print axioms shell_sum_ne_cartesian_sum
#print axioms shell_sum_ne_cartesian_sum_explicit
#print axioms shell_sum_explicit_values

end Gate1B
