/-
# Gate-1A Δv4 §23 — the p/q face cascade is not load-bearing for the main
# clean block

§23 asks: once the five clean-block sectors of §25 are each bounded
(nonzero outer curvature, regular `Z = 0` axis, true-zero `Z = 0` axis,
`L = 0` firewall, generic `Z L ≠ 0`), is the whole clean full-conductor block
bounded *without* invoking separate `p₁, p₂, q₁, q₂` divisor-family savings?

The answer is yes, and it is a purely combinatorial consequence of the §25
partition: the literal statement below derives the clean-block bound from the
five sector bounds **only**.  There is no face hypothesis anywhere in its
signature, so no face lemma can be silently load-bearing in this derivation.

The old face lemmas are *not* deleted; they remain in
`Gate1A/…` as a fallback bank.
-/
import Mathlib
import Gate1A.Delta4.Partition

namespace Gate1A

namespace Delta4

instance : Fintype CleanSector :=
  ⟨{CleanSector.curvature, CleanSector.axisRegular, CleanSector.axisTrueZero,
      CleanSector.firewall, CleanSector.generic}, by intro x; cases x <;> decide⟩

/-- **§23 (`clean_block_bound_without_face_savings`).**  If every one of the
five §25 sectors carries mass at most `B t`, then the whole clean block
carries mass at most `∑ t, B t`.

The hypotheses mention only the sector classifier and the five sector bounds.
In particular no `p₁, p₂, q₁, q₂` divisor-family ("face") saving occurs in
the derivation. -/
theorem clean_block_bound_without_face_savings {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (sec : ι → CleanSector) (B : CleanSector → ℝ)
    (hsec : ∀ t : CleanSector, ∑ i ∈ s.filter (fun i => sec i = t), w i ≤ B t) :
    ∑ i ∈ s, w i ≤ ∑ t : CleanSector, B t := by
  classical
  have hfib : ∑ t : CleanSector, ∑ i ∈ s.filter (fun i => sec i = t), w i
      = ∑ i ∈ s, w i := Finset.sum_fiberwise s sec w
  rw [← hfib]
  exact Finset.sum_le_sum fun t _ => hsec t

/-- The specialised five-term form, with the sectors spelled out. -/
theorem clean_block_bound_five_sectors {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (sec : ι → CleanSector) (Ba Bb Bc Bd Be : ℝ)
    (hA : ∑ i ∈ s.filter (fun i => sec i = CleanSector.curvature), w i ≤ Ba)
    (hB : ∑ i ∈ s.filter (fun i => sec i = CleanSector.axisRegular), w i ≤ Bb)
    (hC : ∑ i ∈ s.filter (fun i => sec i = CleanSector.axisTrueZero), w i ≤ Bc)
    (hD : ∑ i ∈ s.filter (fun i => sec i = CleanSector.firewall), w i ≤ Bd)
    (hE : ∑ i ∈ s.filter (fun i => sec i = CleanSector.generic), w i ≤ Be) :
    ∑ i ∈ s, w i ≤ Ba + Bb + Bc + Bd + Be := by
  classical
  have key := clean_block_bound_without_face_savings s w sec
    (fun t => match t with
      | CleanSector.curvature => Ba
      | CleanSector.axisRegular => Bb
      | CleanSector.axisTrueZero => Bc
      | CleanSector.firewall => Bd
      | CleanSector.generic => Be)
    (by intro t; cases t <;> assumption)
  refine key.trans (le_of_eq ?_)
  show Finset.sum {CleanSector.curvature, CleanSector.axisRegular,
    CleanSector.axisTrueZero, CleanSector.firewall, CleanSector.generic} _ = _
  rw [show ({CleanSector.curvature, CleanSector.axisRegular, CleanSector.axisTrueZero,
        CleanSector.firewall, CleanSector.generic} : Finset CleanSector)
      = insert CleanSector.curvature (insert CleanSector.axisRegular
          (insert CleanSector.axisTrueZero
            (insert CleanSector.firewall {CleanSector.generic}))) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- Cascade bookkeeping label. -/
inductive CascadeStatus
  /-- the face cascade is needed for the derivation. -/
  | loadBearing
  /-- the face cascade is not needed for the main clean block. -/
  | nonLoadBearingForMainCleanBlock
  deriving DecidableEq, Repr

/-- `P_Q_FACE_CASCADE : NON_LOAD_BEARING_FOR_MAIN_CLEAN_BLOCK`.

The label records exactly what `clean_block_bound_without_face_savings`
proves: the clean-block bound is derivable from the five §25 sector bounds
alone.  It says nothing about whether those five sector bounds are themselves
already available — in this project sectors B–E are proved only in the
abstract forms of `Gate1A/Delta4/OuterAxis.lean`, `PBAxis.lean`,
`Projective.lean` and `Curvature.lean`, and the remaining analytic input is
carried explicitly by `Delta4OpenInterfaces`. -/
def pqFaceCascadeStatus : CascadeStatus :=
  CascadeStatus.nonLoadBearingForMainCleanBlock

theorem pq_face_cascade_non_load_bearing :
    pqFaceCascadeStatus = CascadeStatus.nonLoadBearingForMainCleanBlock := rfl

end Delta4

end Gate1A
