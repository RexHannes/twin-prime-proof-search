import RequestProject.Main

/-!
# Abstract collision-sector interface

This file proves only a conditional finite-sum implication.  It does not
instantiate the hypotheses for a concrete clean high-`P₃` packet.  The time
diagonal and the all-distinct off-diagonal are not included.
-/

namespace TwinPrimeProject

open scoped BigOperators

/-- Finite data for a four-prime collision sector.  `primeSize` is the
positive real size attached to an abstract prime label. -/
structure CollisionSectorData where
  Edge : Type
  Time : Type
  Prime : Type
  [edgeFintype : Fintype Edge]
  [timeFintype : Fintype Time]
  [primeFintype : Fintype Prime]
  [edgeDecidableEq : DecidableEq Edge]
  [timeDecidableEq : DecidableEq Time]
  [primeDecidableEq : DecidableEq Prime]
  M : ℝ
  D : ℝ
  L : ℝ
  H : ℝ
  X : ℝ
  Xi : ℝ
  primeSize : Prime → ℝ
  W : Edge → Time → ℂ
  b : Prime → ℂ
  d : Prime → ℂ
  rhoA : Prime → Edge → Time → ℂ
  rhoB : Prime → Edge → Time → ℂ

attribute [instance] CollisionSectorData.edgeFintype
  CollisionSectorData.timeFintype CollisionSectorData.primeFintype
  CollisionSectorData.edgeDecidableEq CollisionSectorData.timeDecidableEq
  CollisionSectorData.primeDecidableEq

namespace CollisionSectorData

variable (𝒟 : CollisionSectorData)

/-- The centered `A`-prime sum at an edge and time. -/
noncomputable def Pb (e : 𝒟.Edge) (t : 𝒟.Time) : ℂ :=
  ∑ p, 𝒟.b p * 𝒟.rhoA p e t

/-- The centered `B`-prime sum at an edge and time. -/
noncomputable def Qd (e : 𝒟.Edge) (t : 𝒟.Time) : ℂ :=
  ∑ p, 𝒟.d p * 𝒟.rhoB p e t

/-- Union of the six repeated-prime strata. -/
def IsCollision (p q p' q' : 𝒟.Prime) : Prop :=
  p = p' ∨ q = q' ∨ p = q ∨ p' = q' ∨ p = q' ∨ q = p'

instance collisionDecidable (p q p' q' : 𝒟.Prime) :
    Decidable (𝒟.IsCollision p q p' q') := by
  unfold IsCollision
  infer_instance

/-- A term of the four-prime quadratic form. -/
noncomputable def fourPrimeTerm (e : 𝒟.Edge) (t : 𝒟.Time) (p q p' q' : 𝒟.Prime) : ℂ :=
  𝒟.W e t * (𝒟.b p * 𝒟.rhoA p e t) * (𝒟.d q * 𝒟.rhoB q e t) *
    star (𝒟.b p' * 𝒟.rhoA p' e t) *
      star (𝒟.d q' * 𝒟.rhoB q' e t)

inductive CollisionStratum where
  | pp | qq | pq | pPrimeQPrime | pQPrime | qPPrime
  deriving DecidableEq, Fintype, Repr

@[simp] theorem card_collisionStratum : Fintype.card CollisionStratum = 6 := by
  decide

/-- One of the six repeated-prime equalities. -/
def InStratum : CollisionStratum → 𝒟.Prime → 𝒟.Prime → 𝒟.Prime → 𝒟.Prime → Prop
  | .pp, p, _, p', _ => p = p'
  | .qq, _, q, _, q' => q = q'
  | .pq, p, q, _, _ => p = q
  | .pPrimeQPrime, _, _, p', q' => p' = q'
  | .pQPrime, p, _, _, q' => p = q'
  | .qPPrime, _, q, p', _ => q = p'

instance stratumDecidable (s : CollisionStratum) (p q p' q' : 𝒟.Prime) :
    Decidable (𝒟.InStratum s p q p' q') := by
  cases s <;> simp [InStratum] <;> infer_instance

/-- The contribution of one collision stratum. -/
noncomputable def stratumSum (s : CollisionStratum) : ℂ :=
  ∑ e, ∑ t, ∑ p, ∑ q, ∑ p', ∑ q' with 𝒟.InStratum s p q p' q',
    𝒟.fourPrimeTerm e t p q p' q'

/-- Finite-union majorant for the collision part.  Intersections can occur in
more than one summand, exactly as in a union bound; no `L⁻²` gain is taken. -/
noncomputable def collisionSum : ℂ :=
  ∑ s : CollisionStratum, 𝒟.stratumSum s

end CollisionSectorData

/-- Explicit finite hypotheses used by the abstract collision estimate.
The prime-weight assumptions are normalized forms of boundedness tailored to
the one-prime `L¹` estimates; no primality theorem is hidden here. -/
structure CollisionSectorHypotheses (𝒟 : CollisionSectorData) where
  pos_M : 0 < 𝒟.M
  one_le_D : 1 ≤ 𝒟.D
  pos_L : 0 < 𝒟.L
  pos_H : 0 < 𝒟.H
  pos_X : 0 < 𝒟.X
  one_le_Xi : 1 ≤ 𝒟.Xi
  prime_one_le : ∀ p, 1 ≤ 𝒟.primeSize p
  C_E : ℝ
  C_W : ℝ
  C_b : ℝ
  C_d : ℝ
  C_bd : ℝ
  C_P : ℝ
  C_Q : ℝ
  C_A : ℝ
  C_B : ℝ
  C_AB : ℝ
  C_L : ℝ
  C_scale : ℝ
  R_A : ℝ
  R_B : ℝ
  constants_nonneg :
    0 ≤ C_E ∧ 0 ≤ C_W ∧ 0 ≤ C_b ∧ 0 ≤ C_d ∧ 0 ≤ C_bd ∧
    0 ≤ C_P ∧ 0 ≤ C_Q ∧ 0 ≤ C_A ∧ 0 ≤ C_B ∧ 0 ≤ C_AB ∧
    0 ≤ C_L ∧ 0 ≤ C_scale ∧ 0 ≤ R_A ∧ 0 ≤ R_B
  edge_count : (Fintype.card 𝒟.Edge : ℝ) ≤ C_E * 𝒟.M ^ 2 * 𝒟.Xi
  W_pointwise : ∀ e t, ‖𝒟.W e t‖ ≤ C_W
  W_time_mass : ∀ e, (∑ t, ‖𝒟.W e t‖) ≤ C_W * 𝒟.Xi * 𝒟.D
  rhoA_pointwise : ∀ p e t, ‖𝒟.rhoA p e t‖ ≤ R_A
  rhoB_pointwise : ∀ p e t, ‖𝒟.rhoB p e t‖ ≤ R_B
  b_square : ∀ p, ‖𝒟.b p‖ ^ 2 ≤ C_b / 𝒟.primeSize p
  d_square : ∀ p, ‖𝒟.d p‖ ^ 2 ≤ C_d / 𝒟.primeSize p
  bd_product : ∀ p, ‖𝒟.b p‖ * ‖𝒟.d p‖ ≤ C_bd / 𝒟.primeSize p
  Pb_bound : ∀ e t, ‖𝒟.Pb e t‖ ≤ C_P * 𝒟.Xi
  Qd_bound : ∀ e t, ‖𝒟.Qd e t‖ ≤ C_Q * 𝒟.Xi
  rhoA_L1 : ∀ e p,
    (∑ t, ‖𝒟.W e t * 𝒟.rhoA p e t‖) ≤
      C_A * 𝒟.Xi * 𝒟.D / 𝒟.primeSize p
  rhoB_L1 : ∀ e p,
    (∑ t, ‖𝒟.W e t * 𝒟.rhoB p e t‖) ≤
      C_B * 𝒟.Xi * 𝒟.D / 𝒟.primeSize p
  crossRoot_L1 : ∀ e p,
    (∑ t, ‖𝒟.W e t * 𝒟.rhoA p e t * 𝒟.rhoB p e t‖) ≤
      C_AB * 𝒟.Xi * 𝒟.D / (𝒟.primeSize p) ^ 2
  inverseSquareMass :
    (∑ p, 1 / (𝒟.primeSize p) ^ 2) ≤ C_L * 𝒟.Xi / 𝒟.L
  /-- Explicit aggregate form of the six one-collision estimates.  In a
  concrete packet this is the remaining finite bookkeeping consequence of
  the preceding H1--H6 bounds; it is not instantiated in this module. -/
  stratum_estimates : ∀ s,
    ‖𝒟.stratumSum s‖ ≤
      (C_E * C_L *
        (C_b * C_A * R_A * C_Q ^ 2 +
         C_d * C_B * R_B * C_P ^ 2 +
         2 * C_bd * C_AB * C_P * C_Q +
         2 * C_bd * C_A * R_B * C_P * C_Q)) /
        6 * 𝒟.Xi ^ 5 * (𝒟.M ^ 2 * 𝒟.D ^ 2 / 𝒟.L)
  target_scaling :
    𝒟.M ^ 2 * 𝒟.D ^ 2 / 𝒟.L ≤
      C_scale * 𝒟.X ^ (-(1 : ℝ) / 9) * (𝒟.M * 𝒟.L ^ 4 / 𝒟.H)

namespace CollisionSectorHypotheses

variable {𝒟 : CollisionSectorData} (h : CollisionSectorHypotheses 𝒟)

/-- Explicit sum of the six collision-stratum constants. -/
def collisionConstant : ℝ :=
  h.C_E * h.C_L *
    (h.C_b * h.C_A * h.R_A * h.C_Q ^ 2 +
     h.C_d * h.C_B * h.R_B * h.C_P ^ 2 +
     2 * h.C_bd * h.C_AB * h.C_P * h.C_Q +
     2 * h.C_bd * h.C_A * h.R_B * h.C_P * h.C_Q)

end CollisionSectorHypotheses

/-- **ABSTRACT_COLLISION_IMPLICATION (raw form).**  Under the explicit finite
hypotheses, the union of all six repeated-prime strata has the required
`M²D²/L` bound.  A union bound is used, so no extra saving is asserted on
intersections of collision strata. -/
theorem collision_sector_raw_bound (𝒟 : CollisionSectorData)
    (h : CollisionSectorHypotheses 𝒟) :
    ‖𝒟.collisionSum‖ ≤
      h.collisionConstant * 𝒟.Xi ^ 5 * (𝒟.M ^ 2 * 𝒟.D ^ 2 / 𝒟.L) := by
  rw [CollisionSectorData.collisionSum]
  calc
    ‖∑ s : CollisionSectorData.CollisionStratum, 𝒟.stratumSum s‖ ≤
        ∑ s : CollisionSectorData.CollisionStratum, ‖𝒟.stratumSum s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _s : CollisionSectorData.CollisionStratum,
        h.collisionConstant / 6 * 𝒟.Xi ^ 5 *
          (𝒟.M ^ 2 * 𝒟.D ^ 2 / 𝒟.L) :=
      Finset.sum_le_sum fun s _ => h.stratum_estimates s
    _ = h.collisionConstant * 𝒟.Xi ^ 5 *
          (𝒟.M ^ 2 * 𝒟.D ^ 2 / 𝒟.L) := by
      simp only [Finset.sum_const, Finset.card_univ,
        CollisionSectorData.card_collisionStratum]
      ring

/-- **ABSTRACT_COLLISION_IMPLICATION (target form).**  The direct scaling
hypothesis converts the raw collision estimate into the stated power saving. -/
theorem collision_sector_target_bound (𝒟 : CollisionSectorData)
    (h : CollisionSectorHypotheses 𝒟) :
    ‖𝒟.collisionSum‖ ≤
      (h.collisionConstant * h.C_scale) * 𝒟.Xi ^ 5 *
        𝒟.X ^ (-(1 : ℝ) / 9) * (𝒟.M * 𝒟.L ^ 4 / 𝒟.H) := by
  have hraw := collision_sector_raw_bound 𝒟 h
  have hconst : 0 ≤ h.collisionConstant := by
    rcases h.constants_nonneg with
      ⟨hE, _, hb, hd, hbd, hP, hQ, hA, hB, hAB, hL, _, hRA, hRB⟩
    unfold CollisionSectorHypotheses.collisionConstant
    exact mul_nonneg (mul_nonneg hE hL) (by positivity)
  have hXi : 0 ≤ 𝒟.Xi ^ 5 := pow_nonneg (le_trans (by norm_num) h.one_le_Xi) _
  calc
    ‖𝒟.collisionSum‖ ≤
        h.collisionConstant * 𝒟.Xi ^ 5 *
          (𝒟.M ^ 2 * 𝒟.D ^ 2 / 𝒟.L) := hraw
    _ ≤ h.collisionConstant * 𝒟.Xi ^ 5 *
          (h.C_scale * 𝒟.X ^ (-(1 : ℝ) / 9) *
            (𝒟.M * 𝒟.L ^ 4 / 𝒟.H)) := by
      exact mul_le_mul_of_nonneg_left h.target_scaling (mul_nonneg hconst hXi)
    _ = (h.collisionConstant * h.C_scale) * 𝒟.Xi ^ 5 *
          𝒟.X ^ (-(1 : ℝ) / 9) * (𝒟.M * 𝒟.L ^ 4 / 𝒟.H) := by
      ring

/-- Optional exponent audit behind the direct scaling assumption. -/
theorem collision_exponent_le_neg_one_ninth (a b : ℝ)
    (hab : 5 / 9 ≤ a + b) (hb : 5 / 18 ≤ b) :
    1 - a - 3 * b ≤ -(1 : ℝ) / 9 := by
  linarith

inductive CollisionClosureStatus where
  | machineChecked
  | notYetSupplied
  | outsideTheorem
  | open
  deriving DecidableEq, Repr

structure CollisionStatusEntry where
  label : String
  status : CollisionClosureStatus
  note : String := ""
  deriving Repr

/-- Conservative status ledger: only the abstract implication is closed. -/
def collisionSectorStatus : List CollisionStatusEntry :=
  [ ⟨"ABSTRACT_COLLISION_IMPLICATION", .machineChecked,
      "Conditional finite-sum theorem from explicit hypotheses"⟩
  , ⟨"CONCRETE_CLEAN_P3_INSTANTIATION", .notYetSupplied,
      "No claim that the clean high-P3 packet satisfies the interface"⟩
  , ⟨"TIME_DIAGONAL", .outsideTheorem, "Not represented by collisionSum"⟩
  , ⟨"ALL_DISTINCT_OFF_DIAGONAL", .open, "Outside this theorem"⟩
  , ⟨"TWIN_PRIME_TYPE_II_FCPT_RPA_CELS_CLOSURE", .open,
      "No downstream closure is claimed"⟩
  ]

end TwinPrimeProject
