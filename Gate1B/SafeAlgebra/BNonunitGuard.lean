/-
# Gate 1B v8.2 — the `B`-non-unit guard

Elementary divisibility: on the shell `B ≡ −2 (mod q)`, no odd prime divisor of
`q` can divide `B`.  Hence `B` is automatically a unit modulo every odd prime
dividing `q`, which is exactly the hypothesis the finite Kloosterman
factorisations need.

This is a *finite arithmetic guard*: it asserts no analytic bound whatsoever.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- **The `B`-non-unit guard.**  If `p` is an odd prime dividing `q` and the
shell relation `q ∣ B + 2` holds, then `p ∤ B`. -/
theorem not_dvd_of_shell_congr {B q : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : (p : ℤ) ∣ q) (hshell : q ∣ B + 2) : ¬ (p : ℤ) ∣ B := by
  intro hB
  have hpB2 : (p : ℤ) ∣ B + 2 := hpq.trans hshell
  have h2 : (p : ℤ) ∣ (2 : ℤ) := by simpa using dvd_sub hpB2 hB
  have h2' : p ∣ 2 := by exact_mod_cast h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')

/-- Congruence form of the same guard. -/
theorem not_dvd_of_shell_modEq {B q : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : (p : ℤ) ∣ q) (hshell : B ≡ -2 [ZMOD q]) : ¬ (p : ℤ) ∣ B := by
  refine not_dvd_of_shell_congr hp hp2 hpq ?_
  simpa [sub_neg_eq_add] using (Int.ModEq.dvd hshell.symm)

/-- **The `B` unit-ness consequence.**  Under the guard, `B` is nonzero modulo
every odd prime dividing `q`. -/
theorem shell_B_ne_zero_mod {B q : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : (p : ℤ) ∣ q) (hshell : q ∣ B + 2) : ¬ (B % (p : ℤ) = 0) := by
  intro h
  exact not_dvd_of_shell_congr hp hp2 hpq hshell (Int.dvd_of_emod_eq_zero h)

end Gate1B.SafeAlgebra
