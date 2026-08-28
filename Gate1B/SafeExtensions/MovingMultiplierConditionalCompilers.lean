/-
# Gate 1B v12 — conditional analytic compilers and the V10 leaf bridge

**Status: implications only.  No analytic input is constructed.**

Every theorem here has the shape

    (UNINHABITED analytic interface) + (explicit dictionary/pin hypotheses)
      ⟹ (project-local parent bound already present in the repository).

The project-local targets used are the v11 predicates

    TwinPrimeProject.Gate1BV11.ShiftedQuotientParentBound
    TwinPrimeProject.Gate1BV11.QK56FullCovarianceBound

and the v10/v11 leaf bundle

    TwinPrimeProject.Gate1BV11.V11AnalyticLeafBundle

whose four fields are *exactly* the four V10 analytic leaves
(`highPrimeLeaf`, `sameQLeaf`, `crossModLeaf`, `H9Leaf`) of
`TwinPrimeProject.Gate1BV10.Gate1BClosureInputs`.  **No type mismatch arises**
at that interface; the missing objects are the analytic inputs themselves.

V10 is not altered, and no V10 leaf is fabricated: each bridge below consumes an
uninhabited interface.

Contents:

* `qkCovarianceBound_to_shiftedQuotientParent`;
* `qkCovarianceBound_to_qk56FullCovariance`;
* `shiftMult4Bound_to_shiftedQuotientParent`;
* `v12_to_v10AnalyticLeaves` — the V10 four-leaf bridge;
* guards showing none of the conclusions is automatic.
-/
import Gate1B.SafeExtensions.QKSourceCharacterCovariance
import Gate1B.SafeExtensions.ShiftMultiplierSource
import RequestProject.NANC.Gate1B.V11PairModToV10Leaves

namespace Gate1B.SafeExtensions

open Finset TwinPrimeProject.Gate1BV11

/-- **QK COVARIANCE ⟹ SHIFTED-QUOTIENT PARENT.**  Conditional compiler: the
uninhabited covariance interface, a dictionary identifying the parent value with
the covariance, and a budget pin. -/
theorem qkCovarianceBound_to_shiftedQuotientParent
    {Ch : Type*} [Fintype Ch] [DecidableEq Ch]
    (D : QKSourceCharacterCovarianceData Ch) (target : ℝ) (Vp : ℂ) (X : ℝ) (s : ℚ)
    (hbound : QKSourceCharacterCovarianceBound D target)
    (hdict : Vp = D.qkCovariance)
    (hpin : target ≤ X ^ (1 - (s : ℝ))) :
    ShiftedQuotientParentBound Vp X s := by
  unfold ShiftedQuotientParentBound
  rw [hdict]
  exact le_trans hbound.covariance_le hpin

/-- **QK COVARIANCE FAMILY ⟹ QK5/6 FULL COVARIANCE PARENT.** -/
theorem qkCovarianceBound_to_qk56FullCovariance
    {Ch : Type*} [Fintype Ch] [DecidableEq Ch]
    (D : Fin 2 → QKSourceCharacterCovarianceData Ch) (target : Fin 2 → ℝ)
    (Vp : Fin 2 → ℂ) (X : ℝ) (s : ℚ)
    (hbound : ∀ k, QKSourceCharacterCovarianceBound (D k) (target k))
    (hdict : ∀ k, Vp k = (D k).qkCovariance)
    (hpin : ∀ k, target k ≤ X ^ (1 - (s : ℝ))) :
    QK56FullCovarianceBound Vp X s := by
  intro k
  rw [hdict k]
  exact le_trans (hbound k).covariance_le (hpin k)

/-- **SHIFTED FOUR-MULTIPLIER MOMENT ⟹ SHIFTED-QUOTIENT PARENT.** -/
theorem shiftMult4Bound_to_shiftedQuotientParent
    {R : Type*} [CommRing R] [DecidableEq R]
    (S : PhysicalFourMultiplierSource R) (phi : R → ℂ) (h1 h2 h3 h4 : R)
    (target : ℝ) (Vp : ℂ) (X : ℝ) (s : ℚ)
    (hbound : ShiftMult4CharacterBound S phi h1 h2 h3 h4 target)
    (hdict : Vp = S.shiftMult4CharacterMoment phi h1 h2 h3 h4)
    (hpin : target ≤ X ^ (1 - (s : ℝ))) :
    ShiftedQuotientParentBound Vp X s := by
  unfold ShiftedQuotientParentBound
  rw [hdict]
  exact le_trans hbound.moment_le hpin

/-- **V12 ⟹ V10 FOUR ANALYTIC LEAVES.**

From one uninhabited covariance interface per V10 leaf, the dictionary
identifying each leaf value with the real part of the corresponding covariance,
and the leaf budget pins, the four V10 analytic leaf fields follow with their
exact V10 types.  V10 itself is untouched, and the interfaces are never
supplied. -/
theorem v12_to_v10AnalyticLeaves
    {Ch : Type*} [Fintype Ch] [DecidableEq Ch]
    (D : TwinPrimeProject.Gate1BV10.Gate1BLeaf → QKSourceCharacterCovarianceData Ch)
    (target : TwinPrimeProject.Gate1BV10.Gate1BLeaf → ℝ)
    (leafValue leafBudget : TwinPrimeProject.Gate1BV10.Gate1BLeaf → ℝ) (X : ℝ) (s : ℚ)
    (hbound : ∀ l, QKSourceCharacterCovarianceBound (D l) (target l))
    (hdict : ∀ l, leafValue l = ((D l).qkCovariance).re)
    (hpin : ∀ l, target l ≤ X ^ (1 - (s : ℝ)))
    (hbudget : ∀ l, X ^ (1 - (s : ℝ)) ≤ leafBudget l) :
    V11AnalyticLeafBundle leafValue leafBudget := by
  refine v10AnalyticLeaves_of_parentBounds leafValue leafBudget X s
    (fun l => (D l).qkCovariance) ?_ hdict hbudget
  intro l
  exact qkCovarianceBound_to_shiftedQuotientParent (D l) (target l) ((D l).qkCovariance) X s
    (hbound l) rfl (hpin l)

/-! ### Guards -/

/-- **Guard F.**  A conditional analytic compiler is not a closure: the
conclusion of the bridge is not automatic. -/
theorem v12LeafBundle_not_automatic :
    ¬ Nonempty (V11AnalyticLeafBundle (fun _ => 2) (fun _ => 1)) :=
  leafBundle_not_automatic

/-- **Guard.**  The parent target itself is not automatic. -/
theorem shiftedQuotientParent_not_automatic :
    ¬ ShiftedQuotientParentBound 2 1 shiftedFixedMultiplierSaving :=
  shiftedQuotientParentBound_not_automatic

end Gate1B.SafeExtensions
