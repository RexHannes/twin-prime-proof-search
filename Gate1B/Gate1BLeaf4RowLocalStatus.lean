import RequestProject.CurrentProgramme.StatusTypes
import Gate1B.Gate1BLeaf4FormalLocalTree

/-!
# Gate 1B · Leaf-4 row-local **status layer** (append-only, metadata only)

This module adds a *new, append-only* research-status layer.  It does not edit,
weaken, rename or overwrite any existing declaration, and it does not
re-interpret any previously banked finite-linear-algebra theorem as analytic
closure.

**Key distinction, enforced by the types below:**

```
kernel theorem bank  ≠  current research status.
```

`RowLocalStatus` is *metadata*.  No constructor asserts a mathematical truth,
and `rowLocalStatus_never_closed` / `rowLocalStatus_analytic_not_kernelProved`
are the Lean-level firewalls preventing a status constant from being read as a
proof.

## Frozen global research status recorded here

```
GATE1B                : OPEN.
LOWER-D               : OPEN.
HNE                   : NOT RUN.
h = 0 HIGH-HIGH       : ANALYTICALLY CLOSED MODULO PHYSICAL LOCAL-SOURCE
                        IDENTIFICATION.
LEAF 4                : ANALYTICALLY CLOSED MODULO LOCAL SOURCE DICTIONARY.
LEAVES 1-3            : NOT PROMOTED.
LOCAL TREE            : FORMALLY IDENTIFIED; PHYSICAL NORMALISATION
                        SOURCE-PINNED.

CURRENT FIRST SOURCE RESIDUAL :
  ORIGINAL-E(q) / Z_E(q) PHYSICAL-ROWLOCAL-DICTIONARY45.

EXACT REMAINING LEAF-4 ANALYTIC SAVING : NONE.
```

The last line means the Leaf-4 obstruction is **not** a missing power/log
saving; it is an exact source-normalisation / dictionary identity.  It is
**not** Gate 1B closure.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Gate1BRowLocal

open Status

/-! ## 1. The row-local research-status datatype (metadata only)

The pre-existing `ResearchStatus` of
`Gate1B.CurrentStatusGate1BPuncturedProductFourier` has only two constructors
and cannot express `analyticBanked`, `sourcePin`, `superseded` or `retracted`,
so a new, strictly larger metadata datatype is appended here.  The old one is
untouched and remains in use in its own layer. -/

/-- Row-local research status.  **Metadata only**: no constructor asserts that a
mathematical statement holds. -/
inductive RowLocalStatus where
  /-- Kernel-checked in this repository. -/
  | kernelProved
  /-- Closed in the external analytic research bank; **not** a Lean theorem. -/
  | analyticBanked
  /-- A deterministic implication exists; its antecedents are not supplied. -/
  | conditional
  /-- Blocked on an external source/dictionary identification. -/
  | sourcePin
  /-- Genuinely open. -/
  | openStatus
  /-- Once accurate, no longer the controlling frontier.  **Not** "false". -/
  | superseded
  /-- Withdrawn as a mechanism.  The underlying algebra, if any, stays banked. -/
  | retracted
  deriving DecidableEq, Repr, Inhabited

namespace RowLocalStatus

/-- The conservative `Status` a row-local status is allowed to occupy. -/
def toStatus : RowLocalStatus → Status
  | kernelProved => Status.provedAlgebraic
  | analyticBanked => Status.externallyAudited
  | conditional => Status.conditionalCompiler
  | sourcePin => Status.sourceOpen
  | openStatus => Status.open_
  | superseded => Status.supersededAsControllingFrontier
  | retracted => Status.falseRoute

/-- Whether the row records a kernel proof *in this repository*. -/
def isKernelProved : RowLocalStatus → Bool
  | kernelProved => true
  | _ => false

end RowLocalStatus

/-- **Firewall.**  No row-local status is `closed`. -/
theorem rowLocalStatus_never_closed (s : RowLocalStatus) : s.toStatus ≠ Status.closed := by
  cases s <;> decide

/-- **Firewall.**  Only `kernelProved` maps to a kernel-proved `Status`; every
analytic / conditional / source / open / superseded / retracted row does not. -/
theorem rowLocalStatus_analytic_not_kernelProved (s : RowLocalStatus)
    (h : s ≠ RowLocalStatus.kernelProved) : s.toStatus.isKernelProved = false := by
  cases s <;> simp_all [RowLocalStatus.toStatus, Status.isKernelProved]

/-- **Firewall.**  `analyticBanked` is *not* a Lean proof: an externally banked
analytic result is recorded as externally audited only. -/
theorem analyticBanked_not_kernelProved :
    RowLocalStatus.analyticBanked.toStatus.isKernelProved = false := by decide

/-- **Firewall.**  `retracted` never coincides with `kernelProved`: retracting an
analytic *mechanism* does not touch the algebra it was built from. -/
theorem retracted_ne_kernelProved :
    RowLocalStatus.retracted ≠ RowLocalStatus.kernelProved := by decide

/-! ## 2. Current status constants -/

/-- Punctured finite Fourier frame: kernel-proved (permanent bank). -/
def puncturedFourierFrameStatus : RowLocalStatus := RowLocalStatus.kernelProved

/-- Primitive determinant arithmetic: kernel-proved (permanent bank). -/
def primitiveDeterminantArithmeticStatus : RowLocalStatus := RowLocalStatus.kernelProved

/-- Product-Fourier exact algebra: kernel-proved (permanent bank). -/
def productFourierAlgebraStatus : RowLocalStatus := RowLocalStatus.kernelProved

/-- Product-Fourier **as a complete Gate-1B analytic closure mechanism**:
retracted.  The algebra above stays banked. -/
def productFourierClosureMechanismStatus : RowLocalStatus := RowLocalStatus.retracted

/-- Joint determinant-character / punctured-frame Gram as the source of the
missing `M^{-1/2}` analytic contraction: retracted. -/
def jointFrameAnalyticGainStatus : RowLocalStatus := RowLocalStatus.retracted

/-- `C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45` as *current first residual*:
superseded (historical only; not false). -/
def oldC4ShiftResidualStatus : RowLocalStatus := RowLocalStatus.superseded

/-- `HZERO-J4-ALPHA4-PRODUCTDIFF45`: analytically banked (the arithmetic kernel
is `Gate1BRowLocal.gate1B_leaf4_productDifference`). -/
def leaf4ProductDifferenceStatus : RowLocalStatus := RowLocalStatus.analyticBanked

/-- `HZERO-J4-ALPHA4-NONCOMMUTATIVE-MAJORTREE45`: analytically banked. -/
def leaf4NoncommutativeMajorTreeStatus : RowLocalStatus := RowLocalStatus.analyticBanked

/-- `HZERO-J4-ALPHA4-BEZOUTROW-NONRESONANT45`: analytically banked (CLOSED in
the research bank). -/
def leaf4NonresonantStatus : RowLocalStatus := RowLocalStatus.analyticBanked

/-- `HZERO-J4-ALPHA4-BEZOUTROW-CENTREDGRAM45`: analytically banked (closed at
formal tree level). -/
def leaf4CentredGramStatus : RowLocalStatus := RowLocalStatus.analyticBanked

/-- `ORIGINAL-E(q) / Z_E(q) PHYSICAL-ROWLOCAL-DICTIONARY45`: **source pin**, the
current first residual. -/
def physicalRowLocalDictionaryStatus : RowLocalStatus := RowLocalStatus.sourcePin

/-- Leaf 4: conditional (analytically closed modulo the local source
dictionary). -/
def leaf4Status : RowLocalStatus := RowLocalStatus.conditional

/-- `h = 0` high-high: conditional (analytically closed modulo the physical
local tree match). -/
def hZeroHighHighStatus : RowLocalStatus := RowLocalStatus.conditional

/-- Leaves 1-3, jointly: open / not promoted. -/
def leaves123Status : RowLocalStatus := RowLocalStatus.openStatus

/-- Leaf 1: open. -/
def leaf1Status : RowLocalStatus := RowLocalStatus.openStatus

/-- Leaf 2: open. -/
def leaf2Status : RowLocalStatus := RowLocalStatus.openStatus

/-- Leaf 3: open. -/
def leaf3Status : RowLocalStatus := RowLocalStatus.openStatus

/-- HNE: not run (recorded as open). -/
def hNeStatus : RowLocalStatus := RowLocalStatus.openStatus

/-- Lower-D: open. -/
def lowerDStatus : RowLocalStatus := RowLocalStatus.openStatus

/-- Gate 1B: OPEN. -/
def gate1BStatus : RowLocalStatus := RowLocalStatus.openStatus

/-! ## 3. Firewall theorems on the constants -/

/-- **Product-Fourier firewall.**  The algebra is banked *and* the closure
mechanism is retracted, simultaneously and without contradiction. -/
theorem productFourier_algebra_banked_mechanism_retracted :
    productFourierAlgebraStatus = RowLocalStatus.kernelProved ∧
      productFourierClosureMechanismStatus = RowLocalStatus.retracted ∧
      productFourierAlgebraStatus ≠ productFourierClosureMechanismStatus := by decide

/-- **Joint-frame firewall.**  The punctured frame is kernel-proved while the
claimed joint-frame `M^{-1/2}` analytic gain is retracted. -/
theorem puncturedFrame_banked_jointGain_retracted :
    puncturedFourierFrameStatus = RowLocalStatus.kernelProved ∧
      jointFrameAnalyticGainStatus = RowLocalStatus.retracted := by decide

/-- **Leaf-4 does not close Gate 1B.**  Leaf 4 is conditional, Gate 1B is open,
and the two statuses are distinct. -/
theorem leaf4_does_not_close_gate1B :
    leaf4Status = RowLocalStatus.conditional ∧ gate1BStatus = RowLocalStatus.openStatus ∧
      leaf4Status ≠ gate1BStatus ∧ gate1BStatus.isKernelProved = false := by decide

/-- **Leaves 1-3 remain open** and are not inferred from Leaf 4. -/
theorem leaves123_open :
    leaf1Status = RowLocalStatus.openStatus ∧ leaf2Status = RowLocalStatus.openStatus ∧
      leaf3Status = RowLocalStatus.openStatus ∧
      leaves123Status = RowLocalStatus.openStatus := by decide

/-- **HNE not run, Lower-D open.** -/
theorem hNe_lowerD_open :
    hNeStatus = RowLocalStatus.openStatus ∧ lowerDStatus = RowLocalStatus.openStatus := by decide

/-- **The current first residual is the physical row-local dictionary**, a source
pin; the old `C4SHIFT` label is only superseded (historical), not current. -/
theorem current_first_residual_is_rowLocal_dictionary :
    physicalRowLocalDictionaryStatus = RowLocalStatus.sourcePin ∧
      oldC4ShiftResidualStatus = RowLocalStatus.superseded ∧
      physicalRowLocalDictionaryStatus ≠ oldC4ShiftResidualStatus := by decide

/-- **No status constant of this layer is kernel-proved except the three
permanent algebra rows.** -/
theorem only_algebra_rows_kernelProved :
    puncturedFourierFrameStatus.isKernelProved = true ∧
      primitiveDeterminantArithmeticStatus.isKernelProved = true ∧
      productFourierAlgebraStatus.isKernelProved = true ∧
      leaf4Status.isKernelProved = false ∧
      hZeroHighHighStatus.isKernelProved = false ∧
      physicalRowLocalDictionaryStatus.isKernelProved = false ∧
      leaf4ProductDifferenceStatus.isKernelProved = false ∧
      leaf4NoncommutativeMajorTreeStatus.isKernelProved = false ∧
      leaf4NonresonantStatus.isKernelProved = false ∧
      leaf4CentredGramStatus.isKernelProved = false := by decide

/-! ## 4. Exact remaining Leaf-4 analytic saving

Recorded as data: the remaining Leaf-4 obstruction is **not** a missing
power/log saving. -/

/-- The exact remaining Leaf-4 analytic saving, as a literal string of the
research bank. -/
def leaf4RemainingAnalyticSaving : String := "NONE"

/-- The literal current first source residual. -/
def currentFirstSourceResidual : String :=
  "ORIGINAL-E(q)-/Z_E(q)-PHYSICAL-ROWLOCAL-DICTIONARY45"

/-- The superseded historical residual label. -/
def supersededFirstResidualLabel : String :=
  "C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45"

/-- **The two residual labels are distinct**; the historical one is not the
current one. -/
theorem residual_labels_distinct :
    currentFirstSourceResidual ≠ supersededFirstResidualLabel := by decide

end Gate1BRowLocal
end CurrentProgramme
end TwinPrimeProject
