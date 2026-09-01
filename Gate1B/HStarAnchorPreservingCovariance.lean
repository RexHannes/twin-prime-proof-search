import Gate1B.HStarCenteredAdditiveProjector
import Gate1B.HStarTwoAnchorCounterguards

/-!
# Gate 1B · the **anchor-preserving centred covariance** object

A finite abstraction of the physical covariance of the HSTAR `k = 0`, `J = ∅`
reconstruction.  It is built directly on the physical two-anchor source, so the
two exact `+2` conditions are *preserved by construction*: the centred
projectors are evaluated at the residues `T i π i mod q i`, and these are
*proved* to be exactly `−2`.

**Nothing analytic appears here.**  The analytic bound for this object is the
uninhabited interface of
`Gate1B.HStarAnchorPreservingAnalyticInterface`.

## Contents

* §1 the moduli `q i = g e i wp i` as `ZMod` moduli and the exact `+2`
  residue theorem;
* §2 the covariance factors `Δ_{g e i wp i}(T i π i)` and the covariance object
  `anchorCovariance`;
* §3 the finite weighted family covariance;
* §4 the **source firewall**: the covariance may not be replaced by a free
  `H`-line object — the free `H`-line support contains configurations that are
  not the image of any physical source.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarAnchorCovariance

open Finset
open TwinPrimeProject.CurrentProgramme.HStarTwoAnchor
open TwinPrimeProject.CurrentProgramme.HStarCentered

/-! ## 1. The moduli and the exact `+2` residues -/

instance instNeZeroQ1 (S : HStarTwoAnchorSource) : NeZero S.q1 := ⟨S.q1_pos.ne'⟩

instance instNeZeroQ2 (S : HStarTwoAnchorSource) : NeZero S.q2 := ⟨S.q2_pos.ne'⟩

/-- **Anchor preservation, first copy.**  The residue of `T₁π₁` modulo
`q₁ = g e₁ wp₁` is exactly `−2`. -/
theorem residue1_eq_neg_two (S : HStarTwoAnchorSource) :
    ((S.T1 * S.pi1 : ℕ) : ZMod S.q1) = -2 := by
  have hzero : ((S.T1 * S.pi1 + 2 : ℕ) : ZMod S.q1) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr S.q1_dvd
  push_cast at hzero ⊢
  linear_combination hzero

/-- **Anchor preservation, second copy.**  The residue of `T₂π₂` modulo
`q₂ = g e₂ wp₂` is exactly `−2`. -/
theorem residue2_eq_neg_two (S : HStarTwoAnchorSource) :
    ((S.T2 * S.pi2 : ℕ) : ZMod S.q2) = -2 := by
  have hzero : ((S.T2 * S.pi2 + 2 : ℕ) : ZMod S.q2) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr S.q2_dvd
  push_cast at hzero ⊢
  linear_combination hzero

/-! ## 2. The covariance object -/

/-- The first exact centred factor `Δ_{g e₁ wp₁}(T₁π₁)`. -/
noncomputable def factor1 (S : HStarTwoAnchorSource) : ℂ :=
  centeredProjector S.q1 ((S.T1 * S.pi1 : ℕ) : ZMod S.q1)

/-- The second exact centred factor `Δ_{g e₂ wp₂}(T₂π₂)`. -/
noncomputable def factor2 (S : HStarTwoAnchorSource) : ℂ :=
  centeredProjector S.q2 ((S.T2 * S.pi2 : ℕ) : ZMod S.q2)

/-- **`AnchorPreservingCenteredCovariance`.**  The finite covariance object of
the physical source: the product of the two exact centred factors, the second
conjugated. -/
noncomputable def AnchorPreservingCenteredCovariance (S : HStarTwoAnchorSource) : ℂ :=
  factor1 S * (starRingEnd ℂ) (factor2 S)

/-- **The two `+2` projector conditions are preserved.**  Both centred factors
are evaluated exactly at the residue `−2`. -/
theorem covariance_evaluated_at_neg_two (S : HStarTwoAnchorSource) :
    AnchorPreservingCenteredCovariance S
      = centeredProjector S.q1 (-2) * (starRingEnd ℂ) (centeredProjector S.q2 (-2)) := by
  rw [AnchorPreservingCenteredCovariance, factor1, factor2, residue1_eq_neg_two,
    residue2_eq_neg_two]

/-- Explicit form of the factors: `1 − P_{q}(−2)` at the anchored residue. -/
theorem factor1_eq (S : HStarTwoAnchorSource) :
    factor1 S = 1 - unitPrincipal S.q1 (-2) := by
  rw [factor1, residue1_eq_neg_two, centeredProjector, if_pos rfl]

theorem factor2_eq (S : HStarTwoAnchorSource) :
    factor2 S = 1 - unitPrincipal S.q2 (-2) := by
  rw [factor2, residue2_eq_neg_two, centeredProjector, if_pos rfl]

/-! ## 3. The finite weighted family covariance -/

/-- The finite weighted covariance of a family of physical sources. -/
noncomputable def familyCovariance {n : ℕ} (S : Fin n → HStarTwoAnchorSource)
    (c : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, c i * AnchorPreservingCenteredCovariance (S i)

/-- Deterministic triangle bound for the family covariance. -/
theorem norm_familyCovariance_le {n : ℕ} (S : Fin n → HStarTwoAnchorSource)
    (c : Fin n → ℂ) (B : ℝ)
    (hB : ∀ i, ‖c i * AnchorPreservingCenteredCovariance (S i)‖ ≤ B) :
    ‖familyCovariance S c‖ ≤ (n : ℝ) * B := by
  classical
  calc ‖familyCovariance S c‖
      ≤ ∑ i : Fin n, ‖c i * AnchorPreservingCenteredCovariance (S i)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hB i
    _ = (n : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 4. Source firewall: no free `H`-line replacement -/

/-- The raw configuration of a physical source has defect exactly `2`. -/
theorem toRaw_defect_eq_two (S : HStarTwoAnchorSource) :
    S.toRaw.rawDefect1 = 2 := by
  rw [← TwoTRawConfig.anchor1_iff_defect1]
  exact S.toRaw_anchor1

/-- **FIREWALL.**  The anchor-preserving covariance may **not** be replaced by a
free `H`-line object: the support of the independent-`H` product contains a
configuration that is *not* the raw image of any physical two-anchor source. -/
theorem covariance_source_not_freeHLine :
    ∃ (c : TwoTRawConfig) (H : ℤ),
      AFactor c H * BFactor c H ≠ 0 ∧
        ∀ S : HStarTwoAnchorSource, S.toRaw ≠ c := by
  refine ⟨defectCountermodel, 2,
    (AFactor_mul_BFactor_ne_zero_iff _ _).2 defectCountermodel_differenceSystem,
    ?_⟩
  intro S hS
  have h2 : S.toRaw.rawDefect1 = 2 := toRaw_defect_eq_two S
  rw [hS, defectCountermodel_defects.1] at h2
  norm_num at h2

end HStarAnchorCovariance
end CurrentProgramme
end TwinPrimeProject
