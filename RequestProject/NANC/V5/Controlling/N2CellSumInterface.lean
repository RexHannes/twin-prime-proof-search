/-
NANC V5 CONTROLLING LAYER — THE GATE-2 CONTROLLING INTERFACE
`FM-N2-CELLSUM-UPPER45`.

The controlling target of the Gate-2 endgame is an **aggregate** (cell-summed)
upper bound for the shifted-prime mass of the exceptional region `H₂`:

    ∑_{cells c} ∑_{n ∈ c} a_n · |H(n)|   ≤   (x / log x) · (geometricMass(H₂) + error).

It deliberately does **not** demand a pointwise bound for each individual cell:
the pointwise statement is strictly stronger, and this is proved below.

UNINHABITED here: `FMN2CellSumUpperAtScale` (`FM_N2_CELLSUM_UPPER45`),
`EpsilonUniformN2`, and the two-linear-forms sieve (which lives in V5).

LEAN-PROVED here: the deterministic compilers

    two-linear-forms sieve  →  prefix-cell decomposition
                            →  aggregate remainder control
                            →  FM_N2_CELLSUM_UPPER45,

the ε-uniform version of the same compiler, and the Theorem-8.3 mass insertion.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.Gate0Status

namespace NANC.V5.Controlling

open scoped BigOperators
open NANC.V4 NANC.V5

/-! ### Cell data for the exceptional region -/

/-- Abstract finite data describing the `H₂` cell decomposition at one scale. -/
structure N2CellData where
  /-- The shrinking parameter `ε`. -/
  eps : ℚ
  /-- The factorization dimension `k`. -/
  k : ℕ
  /-- The index set of the `H₂` cells. -/
  cells : Finset ℕ
  /-- The integers lying in a given cell. -/
  cellSet : ℕ → Finset ℕ
  /-- The prefix prime factors attached to a cell. -/
  prefixPrimes : ℕ → Finset ℕ
  /-- The final-prime interval `J` attached to a cell. -/
  J : ℕ → Finset ℕ
  /-- The shifted-prime weight. -/
  a : ℕ → ℝ
  /-- The `H`-weight. -/
  H : ℕ → ℝ
  /-- The geometric mass of the region. -/
  geometricMass : ℝ
  a_nonneg : ∀ n, 0 ≤ a n
  geometricMass_nonneg : 0 ≤ geometricMass

/-- The weighted mass of a single cell, `∑_{n ∈ c} a_n · |H(n)|`. -/
noncomputable def cellMass (D : N2CellData) (c : ℕ) : ℝ :=
  ∑ n ∈ D.cellSet c, D.a n * |D.H n|

theorem cellMass_nonneg (D : N2CellData) (c : ℕ) : 0 ≤ cellMass D c :=
  Finset.sum_nonneg fun n _ => mul_nonneg (D.a_nonneg n) (abs_nonneg _)

/-- The total, cell-summed mass of the exceptional region. -/
noncomputable def totalN2Mass (D : N2CellData) : ℝ := ∑ c ∈ D.cells, cellMass D c

theorem totalN2Mass_nonneg (D : N2CellData) : 0 ≤ totalN2Mass D :=
  Finset.sum_nonneg fun c _ => cellMass_nonneg D c

/-! ### The controlling interface -/

/-- **The Gate-2 controlling interface (UNINHABITED): `FM-N2-CELLSUM-UPPER45`.**

    total N₂ shifted-prime weighted mass  ≤  (x / log x) · (geometricMass + error).

Aggregate only: no pointwise cell bound is required. -/
def FMN2CellSumUpperAtScale (D : N2CellData) (x logx err : ℝ) : Prop :=
  totalN2Mass D ≤ (x / logx) * (D.geometricMass + err)

/-- The source-minimal name of the controlling interface. -/
abbrev FM_N2_CELLSUM_UPPER45 := FMN2CellSumUpperAtScale

/-- A **pointwise** short-cell bound: every individual cell obeys `bound c`. -/
def PointwiseCellUpper (D : N2CellData) (bound : ℕ → ℝ) : Prop :=
  ∀ c ∈ D.cells, cellMass D c ≤ bound c

/-- Pointwise cell bounds, together with a summation of the pointwise targets
against the geometric target, give the aggregate bound.  (Deterministic.) -/
theorem pointwise_and_summation_imp_cellSum {D : N2CellData} {bound : ℕ → ℝ} {x logx err : ℝ}
    (hp : PointwiseCellUpper D bound)
    (hsum : ∑ c ∈ D.cells, bound c ≤ (x / logx) * (D.geometricMass + err)) :
    FMN2CellSumUpperAtScale D x logx err :=
  le_trans (Finset.sum_le_sum fun c hc => hp c hc) hsum

/-- **Firewall.**  The pointwise statement is *strictly stronger* than the
controlling aggregate target: there is data satisfying the aggregate bound on
which a proposed pointwise bound fails. -/
theorem cellSum_does_not_give_pointwise :
    ∃ (D : N2CellData) (bound : ℕ → ℝ) (x logx err : ℝ),
      FMN2CellSumUpperAtScale D x logx err ∧ ¬ PointwiseCellUpper D bound := by
  classical
  refine ⟨{ eps := 0, k := 1, cells := {0}, cellSet := fun _ => {0},
            prefixPrimes := fun _ => ∅, J := fun _ => ∅, a := fun _ => 1, H := fun _ => 1,
            geometricMass := 1, a_nonneg := fun _ => by norm_num,
            geometricMass_nonneg := by norm_num },
          fun _ => 0, 1, 1, 0, ?_, ?_⟩
  · simp [FMN2CellSumUpperAtScale, totalN2Mass, cellMass]
  · intro h
    have := h 0 (by simp)
    simp [cellMass] at this
    linarith

/-! ### The compiler chain -/

/-- **Prefix-cell decomposition (deterministic link).**  Each cell mass is exactly
the weighted count that the two-linear-forms sieve is applied to. -/
def PrefixCellDecomposition (D : N2CellData)
    (sieveData : ℕ → TwoLinearFormsUpperSieveData) : Prop :=
  ∀ c ∈ D.cells, cellMass D c = twoLinearFormsCount (sieveData c)

/-- **Aggregate remainder control.**  The summed sieve targets are dominated by the
geometric target plus the admissible error. -/
def AggregateRemainderControl (D : N2CellData) (S : ℕ → ℝ) (x logx err : ℝ) : Prop :=
  ∑ c ∈ D.cells, S c ≤ (x / logx) * (D.geometricMass + err)

/-- All hypotheses of the two-linear-forms sieve hold for every cell. -/
def SieveHypothesesHold (D : N2CellData) (sieveData : ℕ → TwoLinearFormsUpperSieveData) : Prop :=
  ∀ c ∈ D.cells, (sieveData c).admissible ∧ (sieveData c).intervalLength ∧
    (sieveData c).gcdCondition ∧ (sieveData c).singularFactorBound

/-- **The Gate-2 deterministic compiler.**

    two-linear-forms upper sieve (per cell)
    +  prefix-cell decomposition
    +  aggregate remainder control
    ⟹  FM_N2_CELLSUM_UPPER45.

All analytic content remains in the hypotheses; the proof uses only finite sum
bounds and transitivity. -/
theorem twoLinearForms_chain_imp_cellSumUpper {D : N2CellData}
    {sieveData : ℕ → TwoLinearFormsUpperSieveData} {S : ℕ → ℝ} {x logx err : ℝ}
    (hdec : PrefixCellDecomposition D sieveData)
    (hsieve : ∀ c ∈ D.cells, TwoLinearFormsUpperSieve (sieveData c) (S c))
    (hhyp : SieveHypothesesHold D sieveData)
    (hrem : AggregateRemainderControl D S x logx err) :
    FMN2CellSumUpperAtScale D x logx err := by
  refine le_trans (Finset.sum_le_sum ?_) hrem
  intro c hc
  obtain ⟨h1, h2, h3, h4⟩ := hhyp c hc
  rw [hdec c hc]
  exact hsieve c hc h1 h2 h3 h4

/-! ### ε-uniformity -/

/-- **ε-uniformity of the `N₂` error (UNINHABITED).**  The V5 uniformity interface,
named for the controlling layer: the error term stays bounded as `ε ↓ 0` through
the admissible range. -/
def EpsilonUniformN2 (errOf : ℚ → ℝ) : Prop := N2UniformInEpsilon errOf

/-- The controlling target, uniformly over the admissible ε-range: one error
constant works for every admissible `ε`. -/
def FMN2CellSumUpperUniform (Dof : ℚ → N2CellData) (x logx : ℚ → ℝ) : Prop :=
  ∃ K : ℝ, ∀ eps : ℚ, EpsAdmissible eps →
    FMN2CellSumUpperAtScale (Dof eps) (x eps) (logx eps) K

/-- **The ε-uniform compiler.**  A cell-sum bound for each admissible `ε`, together
with ε-uniformity of the error family, gives the uniform controlling target.  The
uniformity hypothesis is genuinely used: without it the error constant could blow
up as `ε ↓ 0`. -/
theorem cellSum_and_epsUniform_imp_uniform {Dof : ℚ → N2CellData} {x logx errOf : ℚ → ℝ}
    (hnn : ∀ eps : ℚ, 0 ≤ x eps / logx eps)
    (hbd : ∀ eps : ℚ, EpsAdmissible eps →
      FMN2CellSumUpperAtScale (Dof eps) (x eps) (logx eps) (errOf eps))
    (huni : EpsilonUniformN2 errOf) :
    FMN2CellSumUpperUniform Dof x logx := by
  obtain ⟨K, hK⟩ := huni
  refine ⟨K, fun eps heps => le_trans (hbd eps heps) ?_⟩
  have hmono : (Dof eps).geometricMass + errOf eps ≤ (Dof eps).geometricMass + K := by
    have := hK eps heps; linarith
  exact mul_le_mul_of_nonneg_left hmono (hnn eps)

/-! ### Theorem 8.3 insertion -/

/-- **Deterministic insertion of the Theorem-8.3 geometric mass.**  If the external
Theorem-8.3 bound `geometricMass ≤ C·ε` holds for the mass function of the region,
the controlling bound becomes `(x/log x)·(C·ε + err)`. -/
theorem cellSum_with_theorem83 {D : N2CellData} {mass : ℚ → ℝ} {C x logx err : ℝ}
    (hnn : 0 ≤ x / logx)
    (hmass : FMTheorem83H2Mass mass C) (heps : EpsAdmissible D.eps)
    (hgeom : D.geometricMass = mass D.eps)
    (hcell : FMN2CellSumUpperAtScale D x logx err) :
    totalN2Mass D ≤ (x / logx) * (C * (D.eps : ℝ) + err) := by
  refine le_trans hcell (mul_le_mul_of_nonneg_left ?_ hnn)
  have := hmass D.eps heps
  rw [hgeom]
  linarith

/-! ### Status bookkeeping -/

/-- Status entry for the controlling interface. -/
def cellSumEntry : ControlEntry where
  name := "FM-N2-CELLSUM-UPPER45"
  status := ControlStatus.uninhabitedInterface
  notes := "The controlling aggregate upper bound.  Defined, never inhabited."

/-- Status entry for ε-uniformity. -/
def epsUniformEntry : ControlEntry where
  name := "ε-uniform N₂ error"
  status := ControlStatus.uninhabitedInterface
  notes := "Required by the endgame splice; a bound for each fixed ε is not enough."

/-- Status entry for Theorem 8.3. -/
def theorem83Entry : ControlEntry where
  name := "Ford–Maynard Theorem 8.3 (geometric mass of H₂ is O(ε))"
  status := ControlStatus.externallyPublished
  notes := "Cited, not formalized; the corresponding Prop has no inhabitant here."

/-- Status entry for the two-linear-forms sieve. -/
def twoLinearFormsEntry : ControlEntry where
  name := "two-linear-forms upper sieve for (t, M·t + 2)"
  status := ControlStatus.uninhabitedInterface
  notes := "No compatible sieve theorem exists in this repository; only the compiler is Lean."

theorem n2Entries_not_leanEvidence :
    ControlEntry.IsLeanEvidence cellSumEntry = false ∧
    ControlEntry.IsLeanEvidence epsUniformEntry = false ∧
    ControlEntry.IsLeanEvidence theorem83Entry = false ∧
    ControlEntry.IsLeanEvidence twoLinearFormsEntry = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end NANC.V5.Controlling
