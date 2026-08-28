import Mathlib
import RequestProject.CurrentProgramme.EndpointShiftedMAM

/-!
# The shifted-MAM fivefold operator socket

`SHIFTED-MAM-FIVEFOLD-OPERATOR45 : OPEN_ANALYTIC` — the current first exact
analytic residual.

The centered shifted packet is

```
C_h^♯ = C_h - M_h^can
```

with the canonical local term `M^can` kept **explicit** (never absorbed).  For a
*physical* shift kernel `η` (finite weights with an explicit `L¹` budget) the
socket asserts

```
‖ ∑_h η(h) C_h^♯ ‖ ≤ requiredBudget.
```

Also banked here:

* `PhysicalShiftKernel` — the concrete kernel data class, with the constructor
  `ofWeights` showing it contains every finite weight family (fixed-polylog
  inverse-DFT kernels, mid-`k` and top-`k` dyadic band kernels alike);
* the trivial-bound lemma `operator_trivial_bound`, which is the *natural-scale*
  estimate and carries **no** saving;
* the Motohashi failure slot: an arithmetic `β`-multiplier is source-coupled and
  is therefore not a smooth test-function slot
  (`betaMultiplier_not_sourceDecoupled`);
* non-vacuity firewalls.

No analytic estimate is proved; the socket is never inhabited.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace MAMOperator

open Finset ShiftedMAM

/-! ## 1. The centered shifted packet -/

/-- The canonical local (main) term attached to each shift. -/
abbrev CanonicalLocalTerm := ℤ → ℂ

/-- **`Csharp`** — the centered shifted packet `C_h^♯ = C_h - M_h^can`.  The
canonical local term stays explicit. -/
noncomputable def Csharp (S : ShiftedMAMSourceData) (M : CanonicalLocalTerm) (h : ℤ) : ℂ :=
  S.C h - M h

/-- Centering is exactly a subtraction: nothing is absorbed. -/
theorem Csharp_add_local (S : ShiftedMAMSourceData) (M : CanonicalLocalTerm) (h : ℤ) :
    Csharp S M h + M h = S.C h := by
  rw [Csharp]; ring

/-! ## 2. The physical shift-kernel class -/

/-- **`PhysicalShiftKernel`** — a finite family of shift weights with an explicit
`L¹` budget.  This class contains the fixed-polylog low-`k` inverse-DFT kernels
and the mid-`k` and top-`k` dyadic band kernels; it does *not* silently allow arbitrary
unbounded weights, since the `L¹` budget is part of the datum. -/
structure PhysicalShiftKernel where
  /-- The finite shift support. -/
  shiftSet : Finset ℤ
  /-- The weights. -/
  eta : ℤ → ℂ
  /-- The declared `L¹` budget. -/
  l1Budget : ℝ
  /-- The `L¹` bound. -/
  l1_bound : ∑ h ∈ shiftSet, ‖eta h‖ ≤ l1Budget

namespace PhysicalShiftKernel

/-- Every finite weight family is a physical kernel, with its own `L¹` norm as
budget.  This is what makes the class broad enough for all three `k`-regimes. -/
noncomputable def ofWeights (shiftSet : Finset ℤ) (eta : ℤ → ℂ) : PhysicalShiftKernel where
  shiftSet := shiftSet
  eta := eta
  l1Budget := ∑ h ∈ shiftSet, ‖eta h‖
  l1_bound := le_rfl

/-- The `L¹` budget of a kernel is nonnegative. -/
theorem l1Budget_nonneg (K : PhysicalShiftKernel) : 0 ≤ K.l1Budget :=
  le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) K.l1_bound

/-- The zero-shift kernel: the single shift `0` with weight `1`.  This is the
kernel that isolates the native packet. -/
noncomputable def zeroShift : PhysicalShiftKernel := ofWeights {0} (fun _ => 1)

@[simp] theorem zeroShift_shiftSet : zeroShift.shiftSet = {0} := rfl

end PhysicalShiftKernel

/-! ## 3. The analytic socket (uninhabited) -/

/-- **`ShiftedMAMFivefoldOperatorInput`.**

For every kernel of the given physical class, the `η`-weighted centered shifted
operator is at most `requiredBudget`.

`SHIFTED-MAM-FIVEFOLD-OPERATOR45 : OPEN_ANALYTIC`; never inhabited here. -/
structure ShiftedMAMFivefoldOperatorInput (S : ShiftedMAMSourceData)
    (M : CanonicalLocalTerm) where
  /-- The admissible physical kernel class. -/
  kernelClass : PhysicalShiftKernel → Prop
  /-- The required (saved) budget. -/
  requiredBudget : ℝ
  /-- The analytic assertion.  NOT SUPPLIED. -/
  bound : ∀ K : PhysicalShiftKernel, kernelClass K →
    ‖∑ h ∈ K.shiftSet, K.eta h * Csharp S M h‖ ≤ requiredBudget

/-- The natural-scale bound: `L¹` budget times the sup of the centered packets.
This is what one gets *for free*; it carries no saving, which is exactly why the
socket above is needed. -/
theorem operator_trivial_bound (S : ShiftedMAMSourceData) (M : CanonicalLocalTerm)
    (K : PhysicalShiftKernel) (cmax : ℝ) (hcmax0 : 0 ≤ cmax)
    (hcmax : ∀ h ∈ K.shiftSet, ‖Csharp S M h‖ ≤ cmax) :
    ‖∑ h ∈ K.shiftSet, K.eta h * Csharp S M h‖ ≤ K.l1Budget * cmax := by
  calc ‖∑ h ∈ K.shiftSet, K.eta h * Csharp S M h‖
      ≤ ∑ h ∈ K.shiftSet, ‖K.eta h * Csharp S M h‖ := norm_sum_le _ _
    _ = ∑ h ∈ K.shiftSet, ‖K.eta h‖ * ‖Csharp S M h‖ :=
        Finset.sum_congr rfl fun h _ => norm_mul _ _
    _ ≤ ∑ h ∈ K.shiftSet, ‖K.eta h‖ * cmax := by
        refine Finset.sum_le_sum fun h hh => ?_
        exact mul_le_mul_of_nonneg_left (hcmax h hh) (norm_nonneg _)
    _ = (∑ h ∈ K.shiftSet, ‖K.eta h‖) * cmax := by rw [Finset.sum_mul]
    _ ≤ K.l1Budget * cmax := mul_le_mul_of_nonneg_right K.l1_bound hcmax0

/-- The socket controls the native (zero-shift) centered packet whenever the
zero-shift kernel is admissible. -/
theorem operator_controls_native (S : ShiftedMAMSourceData) (M : CanonicalLocalTerm)
    (I : ShiftedMAMFivefoldOperatorInput S M)
    (hzero : I.kernelClass PhysicalShiftKernel.zeroShift) :
    ‖Csharp S M 0‖ ≤ I.requiredBudget := by
  have h := I.bound PhysicalShiftKernel.zeroShift hzero
  rw [PhysicalShiftKernel.zeroShift_shiftSet, Finset.sum_singleton] at h
  simpa [PhysicalShiftKernel.zeroShift, PhysicalShiftKernel.ofWeights] using h

/-! ## 4. Non-vacuity firewalls -/

/-- Any inhabitant of the socket with a nonempty admissible class forces a
nonnegative budget. -/
theorem operatorInput_budget_nonneg (S : ShiftedMAMSourceData) (M : CanonicalLocalTerm)
    (I : ShiftedMAMFivefoldOperatorInput S M) (K : PhysicalShiftKernel)
    (hK : I.kernelClass K) : 0 ≤ I.requiredBudget :=
  le_trans (norm_nonneg _) (I.bound K hK)

/-- **`operatorInput_not_automatic`.**  With a negative budget and the zero-shift
kernel admissible, the socket is provably empty.  No compiler can manufacture
its own analytic antecedent. -/
theorem operatorInput_not_automatic (S : ShiftedMAMSourceData) (M : CanonicalLocalTerm) :
    IsEmpty {I : ShiftedMAMFivefoldOperatorInput S M //
      I.requiredBudget = -1 ∧ I.kernelClass PhysicalShiftKernel.zeroShift} := by
  constructor
  rintro ⟨I, hb, hK⟩
  have := operatorInput_budget_nonneg S M I _ hK
  rw [hb] at this
  norm_num at this

/-! ## 5. The Motohashi failure slot -/

/-- A multiplier is *source-decoupled* (a smooth test-function slot) if it
depends on the `v`-variable only. -/
def IsSourceDecoupled (m : ℤ → ℤ → ℤ → ℤ → ℂ) : Prop :=
  ∃ F : ℤ → ℂ, ∀ u ell h v, m u ell h v = F v

/-- The shifted `β`-multiplier, as an abstract source-coupled object: it may
depend on `u`, `ℓ` and the shift `h` as well as on `v`. -/
def betaMultiplier (beta : ℤ → ℂ) (u ell h v : ℤ) : ℂ :=
  beta ((u * v + 2) / ell + u * h)

/-- **`betaMultiplier_not_sourceDecoupled`.**  An arithmetic `β`-multiplier is
*not* definitionally a smooth test-function slot: there is a `β` whose
multiplier genuinely depends on the source variables.

`MOTOHASHI-SHIFTED-MAM-DICTIONARY45 : FAIL AT SOURCE-COUPLED OPERATOR SLOT`.
This does **not** claim that every `β`-multiplier is analytically nonsmooth. -/
theorem betaMultiplier_not_sourceDecoupled :
    ∃ beta : ℤ → ℂ, ¬ IsSourceDecoupled (betaMultiplier beta) := by
  refine ⟨fun z => (z : ℂ), ?_⟩
  rintro ⟨F, hF⟩
  have h0 := hF 0 1 0 0
  have h1 := hF 1 1 1 0
  simp [betaMultiplier] at h0 h1
  rw [← h1] at h0
  norm_num at h0

/-- Consequently, the dictionary "scalar Motohashi source `b₅(v)·F(v)`" cannot be
matched slot-for-slot against the shifted source multiplier. -/
theorem motohashi_dictionary_slot_mismatch :
    ∃ (m : ℤ → ℤ → ℤ → ℤ → ℂ), ¬ IsSourceDecoupled m :=
  ⟨_, (betaMultiplier_not_sourceDecoupled).choose_spec⟩

end MAMOperator
end CurrentProgramme
end TwinPrimeProject
