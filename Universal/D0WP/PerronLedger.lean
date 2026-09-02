/-
# Universal / D0WP — Perron / nuclear `L¹` ledger interface

**Status of this module: KERNEL_PROVED conditional arithmetic; the ledger itself
is a SOURCE_PIN and is not inhabited from prose metadata.**

The ledger records only *structural finite facts* about the Perron / nuclear
decomposition:

* a bounded number of separator variables;
* each separator carries `L^{O(1)}` mass;
* a polylog number of dyadic cells;
* no `X^δ` mass anywhere (this is exactly what the two bounds above say).

Conditionally on those structural facts we prove `∃ C_P, totalMass ≤ L^{C_P}`.
A numerical `C_P` is not required and none is claimed.  No inhabitant of
`PerronNuclearLedger` is constructed here.
-/
import Mathlib

namespace Universal.D0WP

open Finset

/-- The structural data of a Perron / nuclear decomposition. -/
structure PerronSourceData where
  /-- The polylog parameter `L = log X`. -/
  L : ℝ
  /-- The number of dyadic cells. -/
  cellCount : ℝ
  /-- The number of separator variables. -/
  separatorCount : ℕ
  /-- The mass of each separator. -/
  sepMass : ℕ → ℝ

/-- Total `L¹` mass of the decomposition. -/
noncomputable def PerronSourceData.totalMass (d : PerronSourceData) : ℝ :=
  d.cellCount * ∏ i ∈ Finset.range d.separatorCount, d.sepMass i

/-- **SOURCE PIN (UNINHABITED here).**  A certificate that the physical source's
Perron / nuclear decomposition really has the recorded structural shape. -/
structure PerronNuclearLedger (d : PerronSourceData) where
  /-- Exponent bounding each separator mass. -/
  cSep : ℝ
  /-- Exponent bounding the number of cells. -/
  cCells : ℝ
  /-- `L ≥ 1`. -/
  L_ge_one : 1 ≤ d.L
  /-- Separator masses are nonnegative. -/
  sepMass_nonneg : ∀ i, 0 ≤ d.sepMass i
  /-- Each separator has at most `L^{cSep}` mass. -/
  sepMass_le : ∀ i, d.sepMass i ≤ d.L ^ cSep
  /-- The cell count is nonnegative. -/
  cellCount_nonneg : 0 ≤ d.cellCount
  /-- There are at most `L^{cCells}` dyadic cells. -/
  cellCount_le : d.cellCount ≤ d.L ^ cCells

/-- The pin, as a proposition. -/
def PerronNuclearLedgerPin (d : PerronSourceData) : Prop := Nonempty (PerronNuclearLedger d)

/-- **CONDITIONAL TOTAL-MASS BOUND (kernel-proved).**  The structural ledger
forces a polylog total mass; the exponent is explicit in the proof but no
numerical value is asserted. -/
theorem perron_totalMass_le {d : PerronSourceData} (P : PerronNuclearLedger d) :
    ∃ C : ℝ, d.totalMass ≤ d.L ^ C := by
  have hL0 : (0:ℝ) < d.L := lt_of_lt_of_le zero_lt_one P.L_ge_one
  refine ⟨P.cCells + P.cSep * d.separatorCount, ?_⟩
  have hprod : ∏ i ∈ Finset.range d.separatorCount, d.sepMass i
      ≤ ∏ _i ∈ Finset.range d.separatorCount, d.L ^ P.cSep := by
    refine Finset.prod_le_prod (fun i _ => P.sepMass_nonneg i) (fun i _ => P.sepMass_le i)
  have hpow : ∏ _i ∈ Finset.range d.separatorCount, d.L ^ P.cSep
      = d.L ^ (P.cSep * d.separatorCount) := by
    rw [Finset.prod_const, Finset.card_range, ← Real.rpow_natCast (d.L ^ P.cSep)
      d.separatorCount, ← Real.rpow_mul (le_of_lt hL0)]
  have hprod' : ∏ i ∈ Finset.range d.separatorCount, d.sepMass i
      ≤ d.L ^ (P.cSep * d.separatorCount) := by rw [← hpow]; exact hprod
  have hprodnn : (0:ℝ) ≤ ∏ i ∈ Finset.range d.separatorCount, d.sepMass i :=
    Finset.prod_nonneg (fun i _ => P.sepMass_nonneg i)
  calc d.totalMass = d.cellCount * ∏ i ∈ Finset.range d.separatorCount, d.sepMass i := rfl
    _ ≤ d.L ^ P.cCells * d.L ^ (P.cSep * d.separatorCount) := by
        apply mul_le_mul P.cellCount_le hprod' hprodnn
        exact le_of_lt (Real.rpow_pos_of_pos hL0 _)
    _ = d.L ^ (P.cCells + P.cSep * d.separatorCount) := (Real.rpow_add hL0 _ _).symm

/-- The ledger is a genuine obligation: some source data admit no ledger. -/
theorem perronLedger_not_automatic :
    ∃ d : PerronSourceData, ¬ PerronNuclearLedgerPin d := by
  refine ⟨⟨1, 2, 0, fun _ => 0⟩, ?_⟩
  rintro ⟨P⟩
  have h := P.cellCount_le
  simp only [Real.one_rpow] at h
  norm_num at h

end Universal.D0WP
