/-
# Gate-1A Δv4 §22 — outer nonzero curvature and the `R^{-1}` family saving

`Δ_out = Z₁ L₂ − Z₂ L₁` is the outer projective curvature.  Proved here:

* `deltaOut_indep_of_moving_prime` — once all non-`r` source coordinates are
  fixed, `Δ_out` is an integer that does not depend on the moving prime `r`
  (formalised by making `r` an explicit spectator field of the state);
* `outer_collision_forces_r_dvd_deltaOut` — an outer *local* collision
  (`Z₁ L₂ ≡ Z₂ L₁ mod r`) together with `Δ_out ≠ 0` forces `r ∣ Δ_out`;
* `curvature_divisor_multiplicity` — for fixed `Δ_out ≠ 0` the number of
  distinct primes `r` that can collide is at most `log₂ |Δ_out|`
  (`2^ω ≤ |Δ_out|`), which is the finite content of the family bound
  `T_nonzero ≤ R^{-1+o(1)} T_natural`;
* `family_saving_from_multiplicity` — the abstract transfer: if each nonzero
  class of the moving family is hit at most `mult` times out of `R`
  candidates, the family energy is at most `(mult / R) ·` the natural energy.
-/
import Mathlib
import Gate1A.Delta4.OuterAxis

namespace Gate1A

namespace Delta4

open Finset

/-- A generic outer state: the projective pair `(Z, L)` together with the
moving prime `r` recorded as an explicit spectator coordinate. -/
structure OuterState where
  /-- the PB row coordinate. -/
  Z : ℤ
  /-- the graph coordinate. -/
  L : ℤ
  /-- the moving prime (a spectator for the curvature). -/
  r : ℕ

/-- The outer curvature `Δ_out = Z₁L₂ − Z₂L₁`. -/
def deltaOut (s1 s2 : OuterState) : ℤ := s1.Z * s2.L - s2.Z * s1.L

/-- **§22 (`deltaOut_indep_of_moving_prime`).**  `Δ_out` does not depend on
the moving prime: changing only the `r`-coordinates leaves it unchanged. -/
theorem deltaOut_indep_of_moving_prime (s1 s2 : OuterState) (r1 r2 : ℕ) :
    deltaOut { s1 with r := r1 } { s2 with r := r2 } = deltaOut s1 s2 := rfl

/-- **§22 (`outer_collision_forces_r_dvd_deltaOut`).**  If two generic states
collide in the outer local factor modulo `r` and the curvature is nonzero,
then `r` divides the curvature. -/
theorem outer_collision_forces_r_dvd_deltaOut (s1 s2 : OuterState) {r : ℕ}
    (hcol : (s1.Z * s2.L : ℤ) ≡ s2.Z * s1.L [ZMOD (r : ℤ)]) :
    (r : ℤ) ∣ deltaOut s1 s2 := by
  have h := (Int.ModEq.dvd hcol)
  simpa [deltaOut, dvd_neg, neg_sub] using (dvd_neg.mpr h)

/-- **§22 (`curvature_divisor_multiplicity`).**  For fixed nonzero curvature
the colliding primes are sparse: at most `log₂ |Δ_out|` of them, i.e.
`2 ^ ω(|Δ_out|) ≤ |Δ_out|`. -/
theorem curvature_divisor_multiplicity {s1 s2 : OuterState}
    (hne : deltaOut s1 s2 ≠ 0) :
    2 ^ ((deltaOut s1 s2).natAbs.primeFactors.card) ≤ (deltaOut s1 s2).natAbs :=
  outer_true_zero_divisor_bound hne

/-- **§22 family transfer.**  If, in a family of `R` candidate primes, each
state's collisions occupy at most `mult` of them, then the collision energy
is at most `(mult / R)` times the natural energy `R · e`.  This is the finite
form of `T_nonzero ≤ R^{-1+o(1)} T_natural`; the `X^{o(1)}` is exactly the
divisor multiplicity of `curvature_divisor_multiplicity`. -/
theorem family_saving_from_multiplicity {R mult e Tcol Tnat : ℝ} (hR : 0 < R)
    (hcol : Tcol ≤ mult * e) (hnat : R * e = Tnat) :
    Tcol ≤ (mult / R) * Tnat := by
  have hEq : (mult / R) * Tnat = mult * e := by
    rw [← hnat]; field_simp
  rw [hEq]
  exact hcol

end Delta4

end Gate1A
