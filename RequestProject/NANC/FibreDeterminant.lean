import RequestProject.NANC.FibreModel

/-!
# Route-A fibre frame: the row determinant identity

The exact identity (RD)

`m_{j'} A_j(t) - m_j A_{j'}(t) = 2 (j' - j)`

holds for all integers `j, j', t` (no ordering assumption on `j, j'`), and gives
the divisibility corollary (RD-div): a common prime divisor of `A_j(t)` and
`A_{j'}(t)` divides `2 (j' - j)`.  Under the separation hypotheses
`p` odd, `0 < |j' - j|` and `2 |j' - j| < p`, no such prime exists.
-/

namespace RouteAFibreFrame

namespace Fibre

variable (F : Fibre)

/-- **(RD)** The row determinant identity
`m_{j'} A_j(t) - m_j A_{j'}(t) = 2 (j' - j)`.
No ordering of `j` and `j'` is assumed. -/
theorem row_determinant_identity (j j' t : ℤ) :
    F.m j' * F.A j t - F.m j * F.A j' t = 2 * (j' - j) := by
  simp only [A, alpha, m]
  linear_combination (j - j') * F.root

/-- **(RD-div)** A common divisor of two row entries divides `2 (j' - j)`. -/
theorem common_divisor_divides_two_jdiff {j j' t d : ℤ}
    (h1 : d ∣ F.A j t) (h2 : d ∣ F.A j' t) : d ∣ 2 * (j' - j) := by
  rw [← F.row_determinant_identity j j' t]
  exact dvd_sub (h1.mul_left _) (h2.mul_left _)

/-- **(RD-div)** A common prime divisor of two row entries divides
`2 (j' - j)`. -/
theorem common_prime_divides_two_jdiff {p : ℕ} {j j' t : ℤ} (_hp : p.Prime)
    (h1 : (p : ℤ) ∣ F.A j t) (h2 : (p : ℤ) ∣ F.A j' t) : (p : ℤ) ∣ 2 * (j' - j) :=
  F.common_divisor_divides_two_jdiff h1 h2

/-- **Same-prime double hit is impossible.**  An odd prime `p` cannot divide two
distinct row entries `A_j(t)`, `A_{j'}(t)` of the same row when the indices are
separated by less than `p / 2`. -/
theorem same_prime_double_hit_impossible {p : ℕ} {j j' t : ℤ} (hp : p.Prime)
    (hodd : Odd p) (hne : j ≠ j') (hsep : 2 * |j' - j| < (p : ℤ))
    (h1 : (p : ℤ) ∣ F.A j t) (h2 : (p : ℤ) ∣ F.A j' t) : False := by
  have hdvd : (p : ℤ) ∣ 2 * (j' - j) := F.common_prime_divides_two_jdiff hp h1 h2
  have hp2 : ¬ ((p : ℤ) ∣ 2) := by
    intro h
    have h' : (p : ℕ) ∣ 2 := by exact_mod_cast h
    have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'
    subst hp_eq
    simp [Nat.odd_iff] at hodd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdj : (p : ℤ) ∣ (j' - j) := by
    rcases hpz.dvd_mul.mp hdvd with h | h
    · exact absurd h hp2
    · exact h
  have hnz : j' - j ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hle : (p : ℤ) ≤ |j' - j| := Int.le_of_dvd (abs_pos.mpr hnz) ((dvd_abs _ _).mpr hdj)
  have habs : 0 < |j' - j| := abs_pos.mpr hnz
  omega

end Fibre

end RouteAFibreFrame
