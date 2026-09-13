/-
# Gate1B / R11 / Frontier / Latest : `R_rest`, the `−3 log M` chamber, and D3

Append-only module.  **Exact algebra and explicit firewalls only.**  Nothing here asserts that
D3 is absent, and no open proposition is inhabited.

* §1 the exact mask / rest split of the global core, and the selected-principal reassembly
  identity (mask, complement, no double charge);
* §2 the raw chamber carrying the coefficient `−3 log M`: it is *nonzero* for every `M ≠ 1`,
  so it cannot be silently dropped; its allowed statuses are an explicit enumeration and it is
  assigned the status it currently has;
* §3 the D1/D2/D3 decomposition object, the deterministic consequence of `D3 = 0`, and the
  firewall `d3_zero_not_automatic`: a decomposition with `D3 ≠ 0` exists, so the absence of D3
  must be *proved*, never assumed.
-/
import Gate1B.R11.Frontier.Latest.GlobalCoreAggregation

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. Masks and the rest -/

section Masks

variable {R : Type*} [CommRing R]

/-- The masked part of the global core. -/
def coreMasked (S : Finset ℕ) (g H : ℕ → R) (p : ℕ → Prop) [DecidablePred p] : R :=
  globalCore (S.filter p) g H

/-- `R_rest`: the complement of the mask. -/
def coreRest (S : Finset ℕ) (g H : ℕ → R) (p : ℕ → Prop) [DecidablePred p] : R :=
  globalCore (S.filter (fun M => ¬ p M)) g H

/-- **Exact reassembly**: masked part plus rest is the whole core; nothing is lost and nothing is
charged twice. -/
theorem core_eq_masked_add_rest (S : Finset ℕ) (g H : ℕ → R) (p : ℕ → Prop) [DecidablePred p] :
    globalCore S g H = coreMasked S g H p + coreRest S g H p :=
  globalCore_mask_split S g H p

/-- The mask and the rest are supported on disjoint sets. -/
theorem masked_rest_disjoint (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    Disjoint (S.filter p) (S.filter (fun M => ¬ p M)) :=
  mask_disjoint S p

end Masks

/-! ## 2. The `−3 log M` chamber -/

/-- The coefficient carried by the five-prime raw chamber. -/
noncomputable def chamberCoefficient (M : ℝ) : ℝ := -3 * Real.log M

/-- **The chamber is not negligible**: its coefficient is nonzero for every `M > 1`, so the
chamber needs an explicit owner and cannot be dropped. -/
theorem chamberCoefficient_ne_zero {M : ℝ} (hM : 1 < M) : chamberCoefficient M ≠ 0 := by
  have hlog : 0 < Real.log M := Real.log_pos hM
  unfold chamberCoefficient
  intro h
  nlinarith

/-- The allowed statuses of the chamber. -/
inductive ChamberStatus
  /-- The chamber has been removed from the source. -/
  | removed
  /-- The chamber is cancelled against the principal term. -/
  | principalCancelled
  /-- The chamber is routed to an existing family. -/
  | routedToFamily
  /-- The chamber is an open D3 owner. -/
  | d3Open
  deriving DecidableEq, Repr

/-- The current status of the five-prime raw chamber carrying `−3 log M`: it is an open D3
owner.  (It is *not* recorded as removed, cancelled or routed, because no such proof exists in
this repository.) -/
def chamberStatus : ChamberStatus := ChamberStatus.d3Open

/-- The chamber is not recorded as removed. -/
theorem chamber_not_removed : chamberStatus ≠ ChamberStatus.removed := by decide

/-- The chamber is not recorded as principal-cancelled. -/
theorem chamber_not_principalCancelled : chamberStatus ≠ ChamberStatus.principalCancelled := by
  decide

/-! ## 3. D1 / D2 / D3 -/

/-- A decomposition of the source into its D1, D2 and D3 parts. -/
structure SourceDecomposition where
  /-- The total source. -/
  total : ℝ
  /-- The D1 part. -/
  d1 : ℝ
  /-- The D2 part. -/
  d2 : ℝ
  /-- The D3 part. -/
  d3 : ℝ
  /-- The exact splitting identity. -/
  split : total = d1 + d2 + d3

/-- If (and only if) `D3` really vanishes does the source reduce to `D1 + D2`. -/
theorem total_eq_d1_add_d2_iff_d3_zero (S : SourceDecomposition) :
    S.total = S.d1 + S.d2 ↔ S.d3 = 0 := by
  constructor
  · intro h
    have := S.split
    linarith
  · intro h
    rw [S.split, h, add_zero]

/-! ## 4. The deterministic reduction of `R_rest` to its chambers -/

/-- **Chamber reduction for `R_rest`.**  If the rest is the finite sum of its chambers and each
chamber is individually bounded, the rest is bounded by the sum of the chamber budgets.  This is
the exact deterministic step that reduces the open node `R_rest` to a chamber-by-chamber
ownership question. -/
theorem rest_abs_le_of_chamber_bounds {ι : Type*} (C : Finset ι) (rest : ℝ) (chamber b : ι → ℝ)
    (hrest : rest = ∑ i ∈ C, chamber i) (hb : ∀ i ∈ C, |chamber i| ≤ b i) :
    |rest| ≤ ∑ i ∈ C, b i := by
  rw [hrest]
  calc |∑ i ∈ C, chamber i| ≤ ∑ i ∈ C, |chamber i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ C, b i := Finset.sum_le_sum hb

/-- **The single-unowned-chamber form.**  If every chamber except one vanishes, the rest is
exactly that chamber; so once all other chambers are removed, routed or principal-cancelled, the
whole of `R_rest` is carried by the surviving chamber — currently the five-prime raw chamber with
coefficient `−3 log M`. -/
theorem rest_eq_single_chamber {ι : Type*} [DecidableEq ι] (C : Finset ι) (rest : ℝ)
    (chamber : ι → ℝ) (i₀ : ι) (hi₀ : i₀ ∈ C) (hrest : rest = ∑ i ∈ C, chamber i)
    (hzero : ∀ i ∈ C, i ≠ i₀ → chamber i = 0) :
    rest = chamber i₀ := by
  rw [hrest]
  exact Finset.sum_eq_single_of_mem i₀ hi₀ (fun i hi hne => hzero i hi hne)

/-- **D3 firewall.**  A source decomposition with `D3 ≠ 0` exists, so `D3 = 0` is a claim that
must be proved; it is never a default.  In this repository it is neither proved nor refuted, and
the ledger records D3 as OPEN. -/
theorem d3_zero_not_automatic : ∃ S : SourceDecomposition, S.d3 ≠ 0 :=
  ⟨⟨1, 0, 0, 1, by norm_num⟩, by norm_num⟩

end Gate1B.R11.Frontier.Latest
