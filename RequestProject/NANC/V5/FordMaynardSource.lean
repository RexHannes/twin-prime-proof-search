/-
NANC V5 — FORD–MAYNARD SOURCE METADATA.

Everything in this file is DATA.  Recording a bibliographic entry is not a
proof, and no Prop is inhabited here.

The only mathematical statements re-exported are the *exact rational* facts
already proved in V4:

    1/6 > 1663/10000
    1/6 - 1663/10000 = 11/30000
-/
import Mathlib
import RequestProject.NANC.V5.Provenance

namespace NANC.V5

open NANC.V4

/-- Bibliographic record of the Ford–Maynard sieve paper. -/
def fordMaynardPaper : Provenance where
  status := AuditStatus.externallyPublished
  sourceName := "Ford–Maynard, On the theory of prime-producing sieves"
  sourceVersion := "arXiv:2407.14368 (public version, 107 pp.)"
  scope := "Type I / Type II hypotheses, sieve-conversion Theorem 2.7, Theorems 8.2-8.3"
  notes := "Cited only.  No part of the 107-page analysis is formalized in this bank."

/-- The published Theorem-2.7(b) threshold, as the exact rational `1663/10000`.
This is the value the bank compares against; it is *not* replaced by any internal
numerical witness. -/
def publishedThreshold : ℚ := fmThreshold

theorem publishedThreshold_eq : publishedThreshold = 1663 / 10000 := rfl

/-- Metadata only: an internal numerical proof witness reported around `0.16623`
appears in discussions of the published threshold.  It is recorded as a *string*
here, deliberately, so that it can never be substituted for the published value
`1663/10000` in any Lean statement. -/
def internalNumericalWitnessNote : Provenance where
  status := AuditStatus.opusAudited
  sourceName := "internal numerical proof witness ≈ 0.16623"
  sourceVersion := "audit metadata"
  scope := "commentary on the published threshold 0.1663"
  notes := "Never substituted for the published threshold in any Lean statement."

theorem internalNumericalWitnessNote_not_leanEvidence :
    Provenance.IsLeanEvidence internalNumericalWitnessNote = false := rfl

/-- Re-export of the V4 exact rational margin (no duplicate proof). -/
theorem v5_margin : nu0 - publishedThreshold = 11 / 30000 := one_sixth_threshold_margin

/-- Re-export of the V4 exact rational comparison (no duplicate proof). -/
theorem v5_one_sixth_gt_threshold : publishedThreshold < nu0 := one_sixth_gt_fm_threshold

end NANC.V5
