/-
# Gate1B / R11 / Frontier / CanonicalRootSync : alignment with the old `R_loc-top,3`  (P11)

Append-only module.  The banked theorem "the old `R_loc-top,3` frontier is still live and its
owner is independent" is tested against the canonical-root bridge.  Two things are **proved**,
and they answer the two halves of the question separately — nothing is preserved merely because
the old graph said so:

* `rlocTop3_owner_independent_of_canonical_root` — the owner is *not implied* by the canonical
  root: the canonical root identity is universally valid, while the owner fails in the sharpness
  instance of the existing bank.  So the canonical reassembly does **not** absorb it as a
  proposition;
* `rlocTop3_owner_offroute` — the owner is nevertheless *not consumed* by the canonical route to
  `R11`: it does not appear in the computed canonical-sync cut set.

The combined verdict is therefore `independentButOffRoute`: independent as a statement, absorbed
only in the weak sense that the canonical route does not call it.  The old reduction itself is
re-ascribed unchanged, so a regression would break this build.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.CutSetRecomputation

namespace Gate1B.R11.Frontier.CanonicalRootSync

open Gate1B.R11.Frontier.ResidueProj

/-! ## 1. The old reduction, unchanged -/

/-- **The old `R_loc-top,3` reduction is preserved verbatim.**  Re-ascription of the banked
theorem: the oscillation hypothesis plus the finite budget still yields `RLocTop3Bound`. -/
theorem rlocTop3_reduction_preserved {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    {lam : ℕ → ℚ} {Ds Ns : Finset ℕ} {K : (∀ i, α i) → ℕ → ℚ} {res : ∀ i, α i → ℕ}
    {eps Mw : ℚ} {l : List ι} (hl : l.Nodup) (hne : l ≠ []) (W : (∀ i, α i) → ℚ)
    (h : RowConsumerResidueOscillation lam Ds Ns K res eps)
    (hW : ∑ x, |W x| ≤ Mw) {xr L S0 C : ℝ}
    (hfinal : ((Mw * 2 ^ l.length * eps : ℚ) : ℝ) ≤ C * xr * L ^ (-S0)) :
    RLocTop3Bound lam Ds Ns K res l W xr L S0 C :=
  Gate1B.R11.Frontier.Latest.oldFrontier_reduction_still_valid hl hne W h hW hfinal

/-! ## 2. Independence from the canonical root -/

/-- **The owner is independent of the canonical root.**  The canonical root identity holds in
every instance, and the owner fails in the sharpness instance of the bank; hence no consequence
of the canonical root identity can be the owner. -/
theorem rlocTop3_owner_independent_of_canonical_root :
    (∀ (F : ℝ) (s : Finset ℕ) (g b : ℕ → ℝ), F = rootSum s g b + rootError F s g b)
      ∧ ¬ RowConsumerResidueOscillation (α := fun _ : Fin 1 => Fin 2) (fun _ => 1) {2} {0}
            sharpK sharpRes 0 :=
  ⟨canonical_root_identity, Gate1B.R11.Frontier.Latest.sharp_rowConsumer_oscillation_fails⟩

/-! ## 3. Off-route in the canonical-sync graph -/

/-- **The owner is not consumed by the canonical route.**  It is retained as a node and is absent
from the computed canonical-sync cut set. -/
theorem rlocTop3_owner_offroute :
    CNode.legacyRowConsumerResidueOscillation ∈ callNodes
      ∧ CNode.legacyRowConsumerResidueOscillation ∉ ccutSet CNode.r11Canonical := by
  decide +kernel

/-! ## 4. The recorded verdict -/

/-- The possible alignment verdicts for the old `R_loc-top,3` frontier. -/
inductive RLocTop3Alignment
  /-- absorbed by the canonical root as a proposition -/
  | absorbedByCanonicalRoot
  /-- independent as a proposition, and not consumed by the canonical route -/
  | independentButOffRoute
  /-- neither could be derived -/
  | unresolved
  deriving DecidableEq, Repr

/-- The verdict, justified by §2 and §3. -/
def rlocTop3Alignment : RLocTop3Alignment := RLocTop3Alignment.independentButOffRoute

/-- The verdict is **not** absorption: the old theorem is not weakened. -/
theorem rlocTop3_not_absorbed :
    rlocTop3Alignment ≠ RLocTop3Alignment.absorbedByCanonicalRoot := by decide

/-- The verdict is **not** unresolved: both halves are proved. -/
theorem rlocTop3_resolved : rlocTop3Alignment ≠ RLocTop3Alignment.unresolved := by decide

end Gate1B.R11.Frontier.CanonicalRootSync
