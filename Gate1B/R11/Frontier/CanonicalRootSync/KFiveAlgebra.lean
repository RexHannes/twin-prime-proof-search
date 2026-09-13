/-
# Gate1B / R11 / Frontier / CanonicalRootSync : exact K = 5 Möbius rank algebra  (P3)

Append-only module.  Exact algebra only; no analytic estimate is asserted anywhere.

Contents:

* §1 the Heath–Brown rank coefficients `hbCoeff K j = (−1)^{j−1} C(K,j)` and the literal
  `K = 5` row `5, −10, 10, −5, 1` (so the brief's `−10, 10, −5, 1` are the `j = 2, 3, 4, 5`
  coefficients, kernel-checked);
* §2 the **exact K = 5 identity** `1 − (1−x)^5 = 5x − 10x² + 10x³ − 5x⁴ + x⁵` in an arbitrary
  commutative ring, its `∑_{j=1}^{5}` form, and its instantiation in the Dirichlet convolution
  ring at a truncated Möbius block (so the identity is available exactly where the rank
  decomposition uses it);
* §3 the **j = 2 branch**, isolated as its own object with the exact complement identity;
* §4 the **physical K = 5 packet**: exponents `(η, a, b)` with the retained constraints
  `0 ≤ η < 99/200`, `η + 5a ≤ 1`, `η + 5b ≤ 1`.  The previously revoked global `e ≤ x^σ`
  assumption is **not** imported, and a firewall theorem records the exact ceiling
  `θ < 697/1000` that the retained constraints alone impose.
-/
import Mathlib

namespace Gate1B.R11.Frontier.CanonicalRootSync

open Finset

/-! ## 1. The Heath–Brown rank coefficients -/

/-- The rank-`j` coefficient of the Heath–Brown / Möbius rank decomposition of depth `K`:
`(−1)^{j−1} C(K, j)`. -/
def hbCoeff (K j : ℕ) : ℤ := (-1) ^ (j - 1) * (K.choose j : ℤ)

/-- **The literal `K = 5` row**: `5, −10, 10, −5, 1`.  The brief's coefficients `−10, 10, −5, 1`
are the `j = 2, 3, 4, 5` entries. -/
theorem hbCoeff_five :
    (hbCoeff 5 1, hbCoeff 5 2, hbCoeff 5 3, hbCoeff 5 4, hbCoeff 5 5) = (5, -10, 10, -5, 1) := by
  decide

/-- The `j = 2` coefficient is exactly `−10`. -/
theorem hbCoeff_five_two : hbCoeff 5 2 = -10 := by decide

/-! ## 2. The exact K = 5 identity -/

variable {R : Type*} [CommRing R]

/-- **The exact K = 5 Möbius rank identity** in any commutative ring. -/
theorem k5_identity (x : R) :
    1 - (1 - x) ^ 5 = 5 * x - 10 * x ^ 2 + 10 * x ^ 3 - 5 * x ^ 4 + x ^ 5 := by ring

/-- The same identity written with the Heath–Brown coefficients, as a sum over the ranks
`j = 1, …, 5`. -/
theorem k5_identity_sum (x : R) :
    1 - (1 - x) ^ 5 = ∑ j ∈ Finset.Icc 1 5, (hbCoeff 5 j : R) * x ^ j := by
  have h : Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [hbCoeff, Nat.choose]
  ring

/-- The truncated Möbius block of length `U`: `μ(n)` for `n ≤ U`, zero beyond.  This is the
`μ`-block whose Dirichlet powers the rank decomposition uses. -/
def muTrunc (U : ℕ) : ArithmeticFunction ℚ where
  toFun n := if n ≤ U then (ArithmeticFunction.moebius n : ℚ) else 0
  map_zero' := by simp

@[simp] theorem muTrunc_apply (U n : ℕ) :
    muTrunc U n = if n ≤ U then (ArithmeticFunction.moebius n : ℚ) else 0 := rfl

/-- **The K = 5 identity in the Dirichlet convolution ring**, at the truncated Möbius block:
the rank decomposition really is the ring identity above, with Dirichlet powers. -/
theorem k5_identity_dirichlet (U : ℕ) :
    1 - (1 - muTrunc U) ^ 5
      = 5 * muTrunc U - 10 * muTrunc U ^ 2 + 10 * muTrunc U ^ 3
        - 5 * muTrunc U ^ 4 + muTrunc U ^ 5 :=
  k5_identity (muTrunc U)

/-! ## 3. The j = 2 branch, isolated -/

/-- The rank-`j` branch of the K = 5 decomposition. -/
def k5Branch (x : R) (j : ℕ) : R := (hbCoeff 5 j : R) * x ^ j

/-- The `j = 2` branch is `−10 x²`. -/
theorem k5Branch_two (x : R) : k5Branch x 2 = -10 * x ^ 2 := by
  norm_num [k5Branch, hbCoeff, Nat.choose]

/-- **Exact isolation of the j = 2 branch**: the decomposition is the `j = 2` branch plus the
complementary ranks, with nothing lost and nothing double-charged. -/
theorem k5_j2_isolation (x : R) :
    1 - (1 - x) ^ 5 = k5Branch x 2 + (k5Branch x 1 + k5Branch x 3 + k5Branch x 4 + k5Branch x 5) := by
  norm_num [k5Branch, hbCoeff, Nat.choose]
  ring

/-! ## 4. The physical K = 5 packet -/

/-- A K = 5, `j = 2` exponent packet: the block exponent `η` and the two atom exponents `a, b`.
All exponents are rationals, so every constraint below is decidable exact arithmetic. -/
structure K5Packet where
  /-- the `μ`-block exponent -/
  eta : ℚ
  /-- the first atom exponent -/
  a : ℚ
  /-- the second atom exponent -/
  b : ℚ
  deriving DecidableEq, Repr

namespace K5Packet

/-- The total exponent `θ = η + a + b`. -/
def theta (p : K5Packet) : ℚ := p.eta + p.a + p.b

end K5Packet

/-- **The retained physical constraints** for a K = 5, `j = 2` packet.  Exactly the constraints
the brief retains: `0 ≤ η < 99/200` and `η + 5a ≤ 1`, `η + 5b ≤ 1` (plus nonnegativity of the
atoms).  The revoked global `e ≤ x^σ` assumption is deliberately absent. -/
def PhysicalK5 (p : K5Packet) : Prop :=
  0 ≤ p.eta ∧ p.eta < 99/200 ∧ 0 ≤ p.a ∧ 0 ≤ p.b ∧ p.eta + 5 * p.a ≤ 1 ∧ p.eta + 5 * p.b ≤ 1

instance (p : K5Packet) : Decidable (PhysicalK5 p) := by
  unfold PhysicalK5; infer_instance

/-- Physicality is exactly the statement that both atoms are at most `(1 − η)/5`. -/
theorem physical_iff (p : K5Packet) :
    PhysicalK5 p ↔ 0 ≤ p.eta ∧ p.eta < 99/200 ∧ 0 ≤ p.a ∧ 0 ≤ p.b
      ∧ p.a ≤ (1 - p.eta)/5 ∧ p.b ≤ (1 - p.eta)/5 := by
  unfold PhysicalK5
  constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;> exact ⟨h1, h2, h3, h4, by linarith, by linarith⟩

/-- **Nonphysicality test**: an atom exceeding `(1 − η)/5` is not physical. -/
theorem not_physical_of_atom_large {p : K5Packet} (h : (1 - p.eta)/5 < p.a) : ¬ PhysicalK5 p := by
  intro hp
  rw [physical_iff] at hp
  linarith [hp.2.2.2.2.1]

/-- **The physical exponent ceiling** imposed by the retained constraints alone:
`θ = η + a + b < 697/1000`.  (`η < 99/200` and `a, b ≤ (1−η)/5` give `θ ≤ 2/5 + 3η/5`.) -/
theorem physical_theta_lt {p : K5Packet} (hp : PhysicalK5 p) : p.theta < 697/1000 := by
  rw [physical_iff] at hp
  obtain ⟨h0, h1, _, _, ha, hb⟩ := hp
  unfold K5Packet.theta
  linarith

/-- The physical ceiling is attained only through the maximal atoms: for a physical packet,
`θ ≤ 2/5 + 3η/5`. -/
theorem physical_theta_le_eta_form {p : K5Packet} (hp : PhysicalK5 p) :
    p.theta ≤ 2/5 + 3 * p.eta / 5 := by
  rw [physical_iff] at hp
  obtain ⟨_, _, _, _, ha, hb⟩ := hp
  unfold K5Packet.theta
  linarith

/-- The **maximal physical packet** at block exponent `η`: both atoms at the physical ceiling
`(1 − η)/5`. -/
def maximalPacket (eta : ℚ) : K5Packet := ⟨eta, (1 - eta)/5, (1 - eta)/5⟩

/-- The maximal packet is physical exactly in the retained `η`-range. -/
theorem maximalPacket_physical {eta : ℚ} (h0 : 0 ≤ eta) (h1 : eta < 99/200) :
    PhysicalK5 (maximalPacket eta) := by
  refine ⟨h0, h1, by simp [maximalPacket]; linarith, by simp [maximalPacket]; linarith, ?_, ?_⟩ <;>
    · simp [maximalPacket]; linarith

/-- The maximal packet dominates every physical packet with the same block exponent. -/
theorem theta_le_maximal {p : K5Packet} (hp : PhysicalK5 p) :
    p.theta ≤ (maximalPacket p.eta).theta := by
  rw [physical_iff] at hp
  obtain ⟨_, _, _, _, ha, hb⟩ := hp
  unfold K5Packet.theta maximalPacket
  simp only
  linarith

/-- The maximal packet's total exponent in closed form. -/
theorem maximalPacket_theta (eta : ℚ) : (maximalPacket eta).theta = 2/5 + 3 * eta / 5 := by
  unfold K5Packet.theta maximalPacket
  simp only
  ring

end Gate1B.R11.Frontier.CanonicalRootSync
