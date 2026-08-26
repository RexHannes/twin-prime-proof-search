import RequestProject.NANC.Gate01Switch.Q5Equation

/-!
# Gate01Switch: the analytic interfaces and the finite implication chain

Every proposition in this module is an **explicit interface**: a named
predicate that this development never proves.  Nothing here manufactures an
inhabitant, and every theorem below takes the interfaces as *hypotheses*.

Interfaces:

* `PrimePowerSparseBound`      (in `PrimePowerStructure`);
* `RepeatedPrimeSparseBound`   (in `RepeatedPrime`);
* `Q5ShiftedProductAnalyticStatement`;
* `ActualSwitchedCoefficientDictionary`;
* `ActualSwitchedMainTermDictionary`;
* `Gate0SwitchedCoverageStatement`;
* `Gate1BSwitchedAnalyticStatement`;
* `Gate0ExhaustiveOperatorCoverageStatement`.

Proved here: only finite/logical implications, obtained from the exact
decompositions of the switched operator together with the triangle inequality.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open ArithmeticFunction Finset

/-! ## Explicit interfaces (never inhabited) -/

/-- **EXPLICIT INTERFACE.**  The Q5 shifted-product analytic statement: the
five-variable sum `𝔖_j` supported on `mn + 2 = dpr` differs from its main term
`𝔐_j` by at most `tol`.  The full analytic assertion lives in this
proposition; no `X^{o(1)}` is hard-coded, and no inhabitant is ever produced. -/
def Q5ShiftedProductAnalyticStatement (Sj Mj tol : ℝ) : Prop := |Sj - Mj| ≤ tol

/-- **EXPLICIT INTERFACE.**  The actual switched coefficient dictionary: the
assertion that the source fixed-cell coefficient `c` really has the shape
`κ (α * β) + E_j`.  The archive contains no such identity (see
`FixedCellConvolution`), so this is only ever a hypothesis. -/
def ActualSwitchedCoefficientDictionary (c : ℕ → ℝ) (kappa : ℝ) (a b Ej : ℕ → ℝ) : Prop :=
  R9CellConvolution c kappa a b Ej

/-- **EXPLICIT INTERFACE.**  The actual switched main-term dictionary: the
archived expected term, corrected by the cell error stratum, matches the Q5
main term `𝔐_j` to within `tol`. -/
def ActualSwitchedMainTermDictionary (expectedPart errPart Mj tol : ℝ) : Prop :=
  |expectedPart - errPart - Mj| ≤ tol

/-- **EXPLICIT INTERFACE.**  Gate 0 coverage for the switched branch: the
switched target is exactly the sum of the finitely many cell operators. -/
def Gate0SwitchedCoverageStatement {ι : Type*} (cells : Finset ι) (op : ι → ℝ)
    (total : ℝ) : Prop := total = ∑ i ∈ cells, op i

/-- **EXPLICIT INTERFACE.**  The Gate 1B switched analytic target. -/
def Gate1BSwitchedAnalyticStatement (total bound : ℝ) : Prop := |total| ≤ bound

/-- **EXPLICIT INTERFACE / SOURCE OPEN.**  The assertion that the direct (root)
and switched operators together exhaust the high-`P₃` packets.  This is *not*
asserted anywhere. -/
def Gate0ExhaustiveOperatorCoverageStatement (allPackets directPart switchedPart : ℝ) : Prop :=
  allPackets = directPart + switchedPart

/-! ## Finite implication chain -/

/-- Triangle-inequality bound for the exact three-way switched decomposition. -/
theorem switched_three_way_bound {Qset : Finset ℕ} {U V K : ℕ} {c E : ℕ → ℝ}
    {b₁ b₂ b₃ : ℝ} (hQ : ∀ q ∈ Qset, 0 < q)
    (hpp : PrimePowerSparseBound (higherPrimePowerSwitchedOperator Qset U V K c E) b₁)
    (hrep : RepeatedPrimeSparseBound (repeatedSwitchedOperator Qset U V K c E) b₂)
    (hgen : |genericSwitchedOperator Qset U V K c E| ≤ b₃) :
    |switchedOperator Qset U V K c E| ≤ b₁ + b₂ + b₃ := by
  rw [switchedOperator_three_way U V K c E hQ]
  calc |higherPrimePowerSwitchedOperator Qset U V K c E
          + repeatedSwitchedOperator Qset U V K c E
          + genericSwitchedOperator Qset U V K c E|
      ≤ |higherPrimePowerSwitchedOperator Qset U V K c E
          + repeatedSwitchedOperator Qset U V K c E|
        + |genericSwitchedOperator Qset U V K c E| := abs_add_le _ _
    _ ≤ (|higherPrimePowerSwitchedOperator Qset U V K c E|
          + |repeatedSwitchedOperator Qset U V K c E|)
        + |genericSwitchedOperator Qset U V K c E| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ b₁ + b₂ + b₃ := by
          exact add_le_add (add_le_add hpp hrep) hgen

/-- **`q5_and_sparse_strata_imply_switched_fixedCell`.**  Supplying

* the actual switched coefficient dictionary,
* the Q5 shifted-product analytic statement,
* the actual switched main-term dictionary,
* the prime-power sparse bound,
* the repeated-prime sparse bound,

yields the switched fixed-cell target.  This theorem proves **none** of its
premises. -/
theorem q5_and_sparse_strata_imply_switched_fixedCell {Qset : Finset ℕ} {U V K : ℕ}
    {c E a b Ej : ℕ → ℝ} {kappa Mj b₁ b₂ tolQ tolM : ℝ} (hQ : ∀ q ∈ Qset, 0 < q)
    (hdict : ActualSwitchedCoefficientDictionary c kappa a b Ej)
    (hq5 : Q5ShiftedProductAnalyticStatement
      (kappa * pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K (dconv a b)))
      Mj tolQ)
    (hmain : ActualSwitchedMainTermDictionary
      (pairSum (genericPart (divisorPairs Qset U V)) (expectedWeight E))
      (pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K Ej)) Mj tolM)
    (hpp : PrimePowerSparseBound (higherPrimePowerSwitchedOperator Qset U V K c E) b₁)
    (hrep : RepeatedPrimeSparseBound (repeatedSwitchedOperator Qset U V K c E) b₂) :
    |switchedOperator Qset U V K c E| ≤ b₁ + b₂ + (tolQ + tolM) := by
  refine switched_three_way_bound hQ hpp hrep ?_
  have hsplit := genericSwitched_R9_split Qset U V K c kappa a b Ej hdict E
  rw [hsplit]
  have h : kappa * pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K (dconv a b))
      + pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K Ej)
      - pairSum (genericPart (divisorPairs Qset U V)) (expectedWeight E)
      = (kappa * pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K (dconv a b)) - Mj)
        - (pairSum (genericPart (divisorPairs Qset U V)) (expectedWeight E)
            - pairSum (genericPart (divisorPairs Qset U V)) (coeffWeight K Ej) - Mj) := by
    ring
  rw [h]
  exact (abs_sub _ _).trans (add_le_add hq5 hmain)

/-- **`switched_cells_and_coverage_imply_gate1B`.**  Gate 0 coverage for the
switched branch plus a bound on each cell gives the Gate 1B target.  Again no
premise is proved here. -/
theorem switched_cells_and_coverage_imply_gate1B {ι : Type*} {cells : Finset ι}
    {op bnd : ι → ℝ} {total : ℝ}
    (hcov : Gate0SwitchedCoverageStatement cells op total)
    (hb : ∀ i ∈ cells, |op i| ≤ bnd i) :
    Gate1BSwitchedAnalyticStatement total (∑ i ∈ cells, bnd i) := by
  rw [Gate1BSwitchedAnalyticStatement, hcov]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)

/-- Even with both branches bounded, a Gate 0 *exhaustion* hypothesis is still
required to bound the whole high-`P₃` mass; it is supplied here as an explicit
premise and proved nowhere. -/
theorem direct_and_switched_bounds_imply_total {allPackets directPart switchedPart bd bs : ℝ}
    (hcov : Gate0ExhaustiveOperatorCoverageStatement allPackets directPart switchedPart)
    (hd : |directPart| ≤ bd) (hs : |switchedPart| ≤ bs) : |allPackets| ≤ bd + bs := by
  rw [hcov]
  exact (abs_add_le _ _).trans (add_le_add hd hs)

end Gate01Switch
end TwinPrimeProject
