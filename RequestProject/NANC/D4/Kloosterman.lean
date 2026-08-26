import Mathlib

namespace TwinPrimeProject.NANC.D4

/-- Symbolic Kloosterman phase pair. -/
def kloostermanPair {G : Type*} [CommGroup G] (A B x : G) : G × G :=
  (A * x, B * x⁻¹)

/-- Fixed-modulus scaling is the permutation `x = p*y`. -/
theorem kloosterman_fixed_modulus_scaling
    {G : Type*} [CommGroup G] (A B p y : G) :
    kloostermanPair (A * p⁻¹) B (p * y) =
      kloostermanPair A (B * p⁻¹) y := by
  apply Prod.ext
  · simp [kloostermanPair]
    group
  · simp [kloostermanPair, mul_inv_rev]
    ac_rfl

/-- Finite residue-multiset certificate refuting the false shift. -/
theorem false_shift_residue_multiset_counterexample :
    (([4, 1, 1, 4] : List (ZMod 5)) : Multiset (ZMod 5)) ≠
      (([3, 2, 2, 3] : List (ZMod 5)) : Multiset (ZMod 5)) := by
  decide

theorem false_shift_left_residues :
    ([(3 * 1 + 1 * 1 : ZMod 5), 3 * 2 + 1 * 3,
      3 * 3 + 1 * 2, 3 * 4 + 1 * 4] : List (ZMod 5)) = [4, 4, 1, 1] := by
  decide

theorem false_shift_right_residues :
    ([(1 * 1 + 2 * 1 : ZMod 5), 1 * 2 + 2 * 3,
      1 * 3 + 2 * 2, 1 * 4 + 2 * 4] : List (ZMod 5)) = [3, 3, 2, 2] := by
  decide

/-- Lossless assembly of twisted multiplicativity and the Ramanujan factor. -/
theorem kloosterman_modulus_lift
    {R : Type*} [CommRing R] (lifted localFactor base mu : R)
    (htwist : lifted = localFactor * base) (hramanujan : localFactor = mu) :
    lifted = mu * base := by
  rw [htwist, hramanujan]

end TwinPrimeProject.NANC.D4
