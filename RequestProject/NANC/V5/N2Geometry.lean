/-
NANC V5 — THE N₂ EXCEPTIONAL REGION: GEOMETRY, SIEVE INTERFACE, COMPILER.

Contents.

* `FMTheorem82DependencyAudit` — a *metadata* record of how the boundedness
  hypothesis of the source's Theorem 8.2 is used.  It is data, never a proof
  about the paper.
* `N2RegionData` — abstract finite data for the exceptional factorization
  region: factorization dimension `k`, prime-factor lower bound, geometric
  mass, `H`-weight bound.
* `ShiftedPrimeN2UpperAtScale` — the required weighted upper bound.  UNINHABITED.
* `TwoLinearFormsUpperSieveData` / `TwoLinearFormsUpperSieve` — the upper-bound
  sieve for the pair of linear forms `n ↦ n`, `n ↦ M·n + 2`, with its
  hypotheses explicit.  UNINHABITED.
* `twoLinearForms_and_geometry_imply_n2Upper` — a genuine compiler theorem:
  pointwise sieve bounds on a factorization decomposition, plus a geometric
  summation input, give the N₂ upper bound.
-/
import Mathlib
import RequestProject.NANC.V5.Gate0Interfaces

namespace NANC.V5

open scoped BigOperators
open NANC.V4

/-! ### Theorem-8.2 boundedness-use audit (metadata only) -/

/-- A record of where the boundedness hypothesis of the source's Theorem 8.2 is
used.  Every field is a Prop *asserted by an external audit*; the record carries
its own provenance and is never evidence about the paper. -/
structure FMTheorem82DependencyAudit where
  /-- The boundedness hypothesis is used pointwise in the final `N₂` estimate. -/
  boundednessUsedInN2 : Prop
  /-- The boundedness hypothesis is used somewhere else as well. -/
  boundednessUsedElsewhere : Prop
  /-- Notes recording what was inspected. -/
  dependencyNotes : String
  /-- Provenance of the audit. -/
  provenance : Provenance

/-- The current audit record: the explicit pointwise use appears in the final `N₂`
estimate.  Whether that is the *only* (even indirect) use is an external-audit
assertion, not a Lean theorem, so both fields are carried abstractly. -/
def theorem82Audit (usedInN2 usedElsewhere : Prop) : FMTheorem82DependencyAudit where
  boundednessUsedInN2 := usedInN2
  boundednessUsedElsewhere := usedElsewhere
  dependencyNotes :=
    "Primary-source observation: an explicit pointwise use of the boundedness " ++
    "hypothesis appears in the final N2 estimate.  Any claim that this is the " ++
    "only (indirect) use remains external-audit metadata."
  provenance := provenanceOpusVerdict "Theorem 8.2 boundedness-use audit"

theorem theorem82Audit_not_leanEvidence (p q : Prop) :
    Provenance.IsLeanEvidence (theorem82Audit p q).provenance = false := rfl

/-- **Firewall.**  Knowing that the boundedness hypothesis is used pointwise in
`N₂` does not exclude further indirect uses: an audit record can assert the first
while the second also holds. -/
theorem n2Use_does_not_exclude_otherUses :
    ∃ A : FMTheorem82DependencyAudit, A.boundednessUsedInN2 ∧ A.boundednessUsedElsewhere :=
  ⟨theorem82Audit True True, trivial, trivial⟩

/-! ### The exceptional region -/

/-- Abstract finite data for the `N₂` exceptional factorization region. -/
structure N2RegionData where
  /-- The exceptional set. -/
  N2set : Finset ℕ
  /-- The factorization dimension `k`. -/
  k : ℕ
  /-- The lower bound imposed on the prime factors in the factorization. -/
  primeLowerBound : ℕ
  /-- The geometric mass of the region. -/
  geometricMass : ℝ
  /-- The bound imposed on the `H`-weight. -/
  Hbound : ℝ
  /-- The prime-side weight `a`. -/
  a : ℕ → ℝ
  /-- The `H`-weight. -/
  H : ℕ → ℝ
  a_nonneg : ∀ n, 0 ≤ a n
  geometricMass_nonneg : 0 ≤ geometricMass

/-- The weighted mass of the exceptional region, `∑_{n ∈ N₂} a_n |H(n)|`. -/
noncomputable def n2Weighted (R : N2RegionData) : ℝ := ∑ n ∈ R.N2set, R.a n * |R.H n|

theorem n2Weighted_nonneg (R : N2RegionData) : 0 ≤ n2Weighted R :=
  Finset.sum_nonneg fun n _ => mul_nonneg (R.a_nonneg n) (abs_nonneg _)

/-- **Required bound (UNINHABITED).**

    ∑_{n ∈ N₂} a_n · |H(n)|  ≤  C · (x / log x) · geometricMass  +  error.

No inhabitant is produced in this bank. -/
def ShiftedPrimeN2UpperAtScale (R : N2RegionData) (C x logx err : ℝ) : Prop :=
  n2Weighted R ≤ C * (x / logx) * R.geometricMass + err

/-- A factorization decomposition of the exceptional region into finitely many
pairwise disjoint pieces. -/
structure N2FactorizationDecomposition (R : N2RegionData) where
  /-- The index set of the decomposition. -/
  index : Finset ℕ
  /-- The pieces. -/
  piece : ℕ → Finset ℕ
  /-- The pieces cover the region. -/
  cover : R.N2set = index.biUnion piece
  /-- The pieces are pairwise disjoint. -/
  disjoint : (index : Set ℕ).PairwiseDisjoint piece

/-! ### The two-linear-forms upper sieve -/

/-- Input data for an upper-bound sieve applied to the pair of linear forms
`n ↦ n` and `n ↦ M·n + 2`, with all required hypotheses carried explicitly. -/
structure TwoLinearFormsUpperSieveData where
  /-- The multiplier `M` of the second form. -/
  M : ℕ
  /-- The sifting interval. -/
  J : Finset ℕ
  /-- The local (singular-series) factor entering the target. -/
  localFactor : ℝ
  /-- The sifting level. -/
  level : ℕ
  /-- The nonnegative weights attached to the interval. -/
  weight : ℕ → ℝ
  weight_nonneg : ∀ n, 0 ≤ weight n
  /-- Admissibility of the pair of linear forms. -/
  admissible : Prop
  /-- The length condition on the interval `J`. -/
  intervalLength : Prop
  /-- The gcd conditions on the coefficients. -/
  gcdCondition : Prop
  /-- The upper bound imposed on the singular factor. -/
  singularFactorBound : Prop

/-- The weighted count the sieve is supposed to bound: `n` and `M·n + 2` both prime. -/
noncomputable def twoLinearFormsCount (D : TwoLinearFormsUpperSieveData) : ℝ :=
  ∑ n ∈ D.J.filter (fun n => Nat.Prime n ∧ Nat.Prime (D.M * n + 2)), D.weight n

/-- **Upper-bound sieve interface (UNINHABITED).**  Under its four hypotheses, the
sieve would bound the weighted count by `target`.  The repository contains no
such sieve theorem, and no inhabitant is produced. -/
def TwoLinearFormsUpperSieve (D : TwoLinearFormsUpperSieveData) (target : ℝ) : Prop :=
  D.admissible → D.intervalLength → D.gcdCondition → D.singularFactorBound →
    twoLinearFormsCount D ≤ target

/-- **Compiler theorem.**  Pointwise sieve bounds along a factorization
decomposition, linked to the pieces of the exceptional region, together with a
geometric summation input, give the `N₂` upper bound.  All analytic content stays
in the hypotheses. -/
theorem twoLinearForms_and_geometry_imply_n2Upper {R : N2RegionData}
    (D : N2FactorizationDecomposition R) (S : ℕ → ℝ)
    (sieveData : ℕ → TwoLinearFormsUpperSieveData) {C x logx err : ℝ}
    (hlink : ∀ j ∈ D.index,
      ∑ n ∈ D.piece j, R.a n * |R.H n| = twoLinearFormsCount (sieveData j))
    (hsieve : ∀ j ∈ D.index, TwoLinearFormsUpperSieve (sieveData j) (S j))
    (hhyp : ∀ j ∈ D.index, (sieveData j).admissible ∧ (sieveData j).intervalLength ∧
      (sieveData j).gcdCondition ∧ (sieveData j).singularFactorBound)
    (hgeom : ∑ j ∈ D.index, S j ≤ C * (x / logx) * R.geometricMass + err) :
    ShiftedPrimeN2UpperAtScale R C x logx err := by
  have hsplit : n2Weighted R = ∑ j ∈ D.index, ∑ n ∈ D.piece j, R.a n * |R.H n| := by
    rw [n2Weighted, D.cover]
    exact Finset.sum_biUnion D.disjoint
  have hbound : ∑ j ∈ D.index, ∑ n ∈ D.piece j, R.a n * |R.H n| ≤ ∑ j ∈ D.index, S j := by
    refine Finset.sum_le_sum ?_
    intro j hj
    obtain ⟨h1, h2, h3, h4⟩ := hhyp j hj
    rw [hlink j hj]
    exact hsieve j hj h1 h2 h3 h4
  rw [ShiftedPrimeN2UpperAtScale, hsplit]
  exact hbound.trans hgeom

/-- Provenance: the sieve interface and the `N₂` bound are both open. -/
def n2InterfaceProvenance : Provenance where
  status := AuditStatus.uninhabited
  sourceName := "two-linear-forms upper sieve / N₂ shifted-prime upper bound"
  sourceVersion := "NANC V5"
  scope := "exceptional factorization region"
  notes := "Defined, never inhabited: no compatible sieve theorem is available here."

theorem n2InterfaceProvenance_not_leanEvidence :
    Provenance.IsLeanEvidence n2InterfaceProvenance = false := rfl

/-- **Firewall.**  Pointwise sieve bounds do not by themselves give the aggregate
`N₂` bound: here the exceptional mass is `1` while the geometric target is `0`. -/
theorem pointwiseSieve_not_uniformN2 :
    ∃ (R : N2RegionData) (C x logx err : ℝ),
      0 < n2Weighted R ∧ ¬ ShiftedPrimeN2UpperAtScale R C x logx err := by
  refine ⟨{ N2set := {1}, k := 1, primeLowerBound := 2, geometricMass := 0, Hbound := 1,
            a := fun _ => 1, H := fun _ => 1, a_nonneg := fun _ => by norm_num,
            geometricMass_nonneg := le_refl 0 }, 1, 1, 1, 0, ?_, ?_⟩
  · simp [n2Weighted]
  · intro h
    simp [ShiftedPrimeN2UpperAtScale, n2Weighted] at h
    linarith

end NANC.V5
