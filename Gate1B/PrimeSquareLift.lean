/-
# Gate 1B safe algebra bank — §8: the local prime-square lift.

For a prime `s`, with `ℓ₁, ℓ₂` invertible mod `s²` and the local coordinates

  `qᵢ ≡ 2 ℓᵢ⁻¹ + s xᵢ  (mod s²)`,

the C45 defect satisfies

  `s² ∣ D  ↔  x₁ ≡ x₂ (mod s)`.

This is the finite algebraic form of the local projective collision; it is a
statement about residues only, and no counting or analytic gain is claimed.
-/
import Gate1B.AdditiveCoordinate

namespace Gate1B

/-- `s² ∣ s y ↔ s ∣ y` for `s ≠ 0`. -/
theorem sq_dvd_mul_iff {s y : ℤ} (hs : s ≠ 0) : s ^ 2 ∣ s * y ↔ s ∣ y := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : s * y = s * (s * k) := by rw [hk]; ring
    exact mul_left_cancel₀ hs this
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩

/-- **(LOCAL-LIFT)** The exact local equivalence at a prime-square modulus.
`s` need only be nonzero; primality is what guarantees that the inverses and
the coordinates exist (see `exists_local_lift_coordinate`). -/
theorem local_prime_square_lift {s q1 q2 l1 l2 l1' l2' x1 x2 : ℤ} (hs : s ≠ 0)
    (hinv1 : s ^ 2 ∣ (l1 * l1' - 1)) (hinv2 : s ^ 2 ∣ (l2 * l2' - 1))
    (hq1 : s ^ 2 ∣ (q1 - (2 * l1' + s * x1)))
    (hq2 : s ^ 2 ∣ (q2 - (2 * l2' + s * x2))) :
    s ^ 2 ∣ C45defect q1 q2 l1 l2 ↔ s ∣ (x1 - x2) := by
  rw [add_c45_int hinv1 hinv2]
  have hsplit : (q1 - 2 * l1') - (q2 - 2 * l2')
      = s * (x1 - x2) + ((q1 - (2 * l1' + s * x1)) - (q2 - (2 * l2' + s * x2))) := by
    ring
  rw [hsplit]
  constructor
  · intro h
    have h2 : s ^ 2 ∣ s * (x1 - x2) := by
      have := dvd_sub h (dvd_sub hq1 hq2)
      simpa using this
    exact (sq_dvd_mul_iff hs).mp h2
  · intro h
    exact dvd_add ((sq_dvd_mul_iff hs).mpr h) (dvd_sub hq1 hq2)

/-- The local coordinate `x` exists exactly on the shell modulo `s`: if
`s ∣ q ℓ − 2` and `ℓ'` is an inverse of `ℓ` mod `s²`, then
`q ≡ 2 ℓ' + s x (mod s²)` for some integer `x`. -/
theorem exists_local_lift_coordinate {s q l l' : ℤ} (hinv : s ^ 2 ∣ (l * l' - 1))
    (hshell : s ∣ (q * l - 2)) :
    ∃ x : ℤ, s ^ 2 ∣ (q - (2 * l' + s * x)) := by
  have hs1 : s ∣ (l * l' - 1) := dvd_trans (dvd_pow_self s (by norm_num)) hinv
  have hco : IsCoprime s l := by
    obtain ⟨k, hk⟩ := hs1
    exact ⟨-k, l', by linarith⟩
  have hmul : s ∣ l * (q - 2 * l') := by
    have hrw : l * (q - 2 * l') = (q * l - 2) - 2 * (l * l' - 1) := by ring
    rw [hrw]
    exact dvd_sub hshell (Dvd.dvd.mul_left hs1 2)
  obtain ⟨y, hy⟩ := hco.dvd_of_dvd_mul_left hmul
  refine ⟨y, ?_⟩
  rw [show q - (2 * l' + s * y) = (q - 2 * l') - s * y by ring, hy, sub_self]
  exact dvd_zero _

/-- Package: on the shell mod `s` at both places, the local coordinates exist
and the local prime-square equivalence holds for them. -/
theorem local_lift_of_shell {s q1 q2 l1 l2 l1' l2' : ℤ} (hs : s ≠ 0)
    (hinv1 : s ^ 2 ∣ (l1 * l1' - 1)) (hinv2 : s ^ 2 ∣ (l2 * l2' - 1))
    (hsh1 : s ∣ (q1 * l1 - 2)) (hsh2 : s ∣ (q2 * l2 - 2)) :
    ∃ x1 x2 : ℤ, s ^ 2 ∣ (q1 - (2 * l1' + s * x1)) ∧ s ^ 2 ∣ (q2 - (2 * l2' + s * x2)) ∧
      (s ^ 2 ∣ C45defect q1 q2 l1 l2 ↔ s ∣ (x1 - x2)) := by
  obtain ⟨x1, hx1⟩ := exists_local_lift_coordinate hinv1 hsh1
  obtain ⟨x2, hx2⟩ := exists_local_lift_coordinate hinv2 hsh2
  exact ⟨x1, x2, hx1, hx2, local_prime_square_lift hs hinv1 hinv2 hx1 hx2⟩

end Gate1B
