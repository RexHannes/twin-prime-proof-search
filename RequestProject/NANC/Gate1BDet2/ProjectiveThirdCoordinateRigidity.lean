import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 36: projective third-coordinate rigidity

A minimal projective-equivalence predicate on triples over `ZMod p` is defined
(no projective-geometry infrastructure is imported), and the following exact
collision-rigidity statement is proved: for an odd prime `p`, if

  `[A : B : −2]  =  [A' : B' : −2]`  in `ZMod p`,

then the projective scalar is forced to be `1`, hence `A = A'` and `B = B'`.

The determinant-2 specialisation takes `A = pSource · l` and `B = −u`.

**This is only a collision-rigidity theorem.**  It does *not* imply any
spectator/operator gain; the guard
`projective_collision_rigidity_does_not_imply_operator_saving` records the
separation, and `SpectatorOperatorSaving` is left as an ordinary uninhabited
interface Prop.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Projective

/-- Minimal projective equivalence of triples over `ZMod p`. -/
def ProjectivelyEq3 {p : ℕ} (x y : ZMod p × ZMod p × ZMod p) : Prop :=
  ∃ a : ZMod p, a ≠ 0 ∧ (a * x.1, a * x.2.1, a * x.2.2) = y

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- For an odd prime `p`, `2 ≠ 0` in `ZMod p`. -/
theorem two_ne_zero_of_odd (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have hprime : Nat.Prime p := (Fact.out : Nat.Prime p)
  haveI : NeZero p := ⟨hprime.ne_zero⟩
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
  exact hp ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 hdvd)

/-- **Third-coordinate scalar rigidity.**  If two triples with equal, nonzero
third coordinate `−2` are projectively equal over an odd prime field, the
scalar is `1`.  (Nonvanishing of the scalar is not needed: it is forced.) -/
theorem projective_scalar_eq_one (hp : p ≠ 2) {A B A' B' : ZMod p} {a : ZMod p}
    (heq : (a * A, a * B, a * (-2 : ZMod p)) = (A', B', (-2 : ZMod p))) :
    a = 1 := by
  have h3 : a * (-2 : ZMod p) = (-2 : ZMod p) := congrArg (fun t => t.2.2) heq
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_odd hp
  have hne : (-2 : ZMod p) ≠ 0 := neg_ne_zero.2 h2
  have : (a - 1) * (-2 : ZMod p) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne

/-- **Projective collision rigidity.**  Over an odd prime field, projective
equality of `[A : B : −2]` and `[A' : B' : −2]` forces `A = A'` and `B = B'`. -/
theorem projective_third_coordinate_rigidity (hp : p ≠ 2) {A B A' B' : ZMod p}
    (h : ProjectivelyEq3 (A, B, (-2 : ZMod p)) (A', B', (-2 : ZMod p))) :
    A = A' ∧ B = B' := by
  obtain ⟨a, -, heq⟩ := h
  have ha1 : a = 1 := projective_scalar_eq_one hp heq
  subst ha1
  refine ⟨?_, ?_⟩
  · simpa using congrArg (fun t => t.1) heq
  · simpa using congrArg (fun t => t.2.1) heq

/-- **Determinant-2 specialisation.**  With `A = pSource · l` and `B = −u`,
projective collision forces the two labels to agree. -/
theorem det2_projective_collision_rigidity (hp : p ≠ 2)
    {pSource l pSource' l' u u' : ZMod p}
    (h : ProjectivelyEq3 (pSource * l, -u, (-2 : ZMod p)) (pSource' * l', -u', (-2 : ZMod p))) :
    pSource * l = pSource' * l' ∧ u = u' := by
  obtain ⟨h1, h2⟩ := projective_third_coordinate_rigidity hp h
  exact ⟨h1, by linear_combination -h2⟩

/-! ## Guard: rigidity is not an operator saving -/

/-- **OPEN INTERFACE.**  A spectator operator-norm saving.  Never inhabited. -/
def SpectatorOperatorSaving (opNorm bound : ℝ) : Prop := opNorm ≤ bound

/-- **GUARD.**  Projective collision rigidity is an unconditional statement about
coordinates; it cannot imply an operator saving, since the saving proposition
has false instances while the rigidity statement is simply true. -/
theorem projective_collision_rigidity_does_not_imply_operator_saving :
    ∃ opNorm bound : ℝ,
      (∀ (q : ℕ) (_ : Fact (Nat.Prime q)), q ≠ 2 → ∀ A B A' B' : ZMod q,
        ProjectivelyEq3 (A, B, (-2 : ZMod q)) (A', B', (-2 : ZMod q)) → A = A' ∧ B = B')
      ∧ ¬ SpectatorOperatorSaving opNorm bound := by
  refine ⟨1, 0, ?_, by norm_num [SpectatorOperatorSaving]⟩
  intro q hq hq2 A B A' B' h
  exact projective_third_coordinate_rigidity hq2 h

end Projective
end Gate1BDet2
end TwinPrimeProject
