/-
# Universal safe algebra — the constrained unit hyperbola

For a finite commutative group `G` and `B c : G`, the constrained hyperbola

    H(B,c) = { (a,b) : G × G | B * a * b = c }

is parametrized by its first coordinate.  This file banks the explicit
parametrization, the equivalence with `G`, and the exact finite-sum reindexing

    ∑_{(a,b) ∈ H(B,c)} F a b = ∑_{a ∈ G} F a (B⁻¹ * c * a⁻¹).

**FIREWALL.**  This is exact finite algebra beneath a two-model completion step.
No Poisson summation, and no analytic statement of any kind, is claimed.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The explicit parametrization of the constrained hyperbola by its first
coordinate. -/
def unitHyperbolaParam (B c : G) (a : G) : G × G := (a, B⁻¹ * c * a⁻¹)

omit [Fintype G] [DecidableEq G] in
/-- The second coordinate on the hyperbola is determined by the first. -/
theorem unitHyperbola_snd_eq {B c a b : G} (h : B * a * b = c) : b = B⁻¹ * c * a⁻¹ := by
  have h2 : b = (B * a)⁻¹ * c := eq_inv_mul_of_mul_eq h
  rw [h2, mul_inv]
  simp [mul_comm, mul_assoc]

omit [Fintype G] [DecidableEq G] in
/-- The parametrization lands on the hyperbola. -/
theorem unitHyperbolaParam_mem (B c a : G) :
    B * (unitHyperbolaParam B c a).1 * (unitHyperbolaParam B c a).2 = c := by
  unfold unitHyperbolaParam
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- The hyperbola, as a `Finset` of pairs. -/
def unitHyperbola (B c : G) : Finset (G × G) :=
  Finset.univ.filter fun p : G × G => B * p.1 * p.2 = c

theorem mem_unitHyperbola {B c : G} {p : G × G} :
    p ∈ unitHyperbola B c ↔ B * p.1 * p.2 = c := by
  simp [unitHyperbola]

/-- **The hyperbola is in explicit bijection with `G`.** -/
def unitHyperbolaEquiv (B c : G) : G ≃ {p : G × G // B * p.1 * p.2 = c} where
  toFun a := ⟨unitHyperbolaParam B c a, unitHyperbolaParam_mem B c a⟩
  invFun p := p.1.1
  left_inv a := rfl
  right_inv := by
    rintro ⟨⟨a, b⟩, hb⟩
    have : b = B⁻¹ * c * a⁻¹ := unitHyperbola_snd_eq hb
    simp [unitHyperbolaParam, this]

/-- **Exact hyperbola reindexing.**  Summing a function over the constrained
hyperbola is the same as summing its parametrized form over the whole group. -/
theorem sum_unitHyperbola_eq_sum_units {M : Type*} [AddCommMonoid M] (B c : G)
    (F : G → G → M) :
    ∑ p ∈ unitHyperbola B c, F p.1 p.2 = ∑ a : G, F a (B⁻¹ * c * a⁻¹) := by
  refine Finset.sum_nbij' (fun p => p.1) (fun a => (a, B⁻¹ * c * a⁻¹)) ?_ ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · intro a _
    refine mem_unitHyperbola.mpr ?_
    simpa using unitHyperbolaParam_mem B c a
  · intro p hp
    rw [mem_unitHyperbola] at hp
    have : p.2 = B⁻¹ * c * p.1⁻¹ := unitHyperbola_snd_eq hp
    exact Prod.ext rfl this.symm
  · intro a _; rfl
  · intro p hp
    rw [mem_unitHyperbola] at hp
    have : p.2 = B⁻¹ * c * p.1⁻¹ := unitHyperbola_snd_eq hp
    rw [this]

end Universal.SafeAlgebra
