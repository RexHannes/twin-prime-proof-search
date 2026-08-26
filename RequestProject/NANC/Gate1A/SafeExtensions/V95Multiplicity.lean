/-
# NANC Gate 1A v9.5 — packet multiplicity ledger

Ordered prime factorizations, Heath–Brown / Vaughan labels, Mellin partitions
and routing labels can all send several *analytic* packet occurrences to one
*physical* geometric row.  This file banks the finite ledger of that
multiplicity:

* `packetCopies e` is the analytic decomposition fibre over the physical row
  `e`;
* `multiplicity_energy_le` is the exact cost of assembling the fibres: with a
  uniform fibre bound `D`, the assembled energy is at most `D` times the
  occurrence energy;
* `multiplicity_not_from_injectivity` records that geometric injectivity of the
  *row map* says nothing about the number of analytic copies, so multiplicity
  may never be inferred from geometry alone.

Nothing analytic is asserted: an `X^{o(1)}` multiplicity must be supplied as an
explicit certificate field, never as a theorem.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V95

open Finset

variable {Occ Row : Type*} [Fintype Occ] [Fintype Row] [DecidableEq Row]

/-- The analytic decomposition fibre of a physical row: the packet occurrences
mapping to it. -/
def packetCopies (rowOf : Occ → Row) (e : Row) : Finset Occ :=
  univ.filter fun o => rowOf o = e

omit [Fintype Row] in
theorem mem_packetCopies {rowOf : Occ → Row} {o : Occ} {e : Row} :
    o ∈ packetCopies rowOf e ↔ rowOf o = e := by
  simp [packetCopies]

/-- The fibres partition the occurrences. -/
theorem sum_over_packetCopies (rowOf : Occ → Row) (f : Occ → ℝ) :
    ∑ e : Row, ∑ o ∈ packetCopies rowOf e, f o = ∑ o, f o :=
  Finset.sum_fiberwise univ rowOf f

/-- **Multiplicity energy ledger.**  With every analytic fibre of size at most
`D`, assembling the occurrences into physical rows costs at most a factor
`D`. -/
theorem multiplicity_energy_le (rowOf : Occ → Row) (f : Occ → ℂ) (D : ℕ)
    (hD : ∀ e : Row, (packetCopies rowOf e).card ≤ D) :
    ∑ e : Row, ‖∑ o ∈ packetCopies rowOf e, f o‖ ^ 2 ≤ D * ∑ o, ‖f o‖ ^ 2 := by
  have hfibre : ∀ e : Row,
      ‖∑ o ∈ packetCopies rowOf e, f o‖ ^ 2
        ≤ (D : ℝ) * ∑ o ∈ packetCopies rowOf e, ‖f o‖ ^ 2 := by
    intro e
    have htri : ‖∑ o ∈ packetCopies rowOf e, f o‖ ≤ ∑ o ∈ packetCopies rowOf e, ‖f o‖ :=
      norm_sum_le _ _
    have hsq : ‖∑ o ∈ packetCopies rowOf e, f o‖ ^ 2
        ≤ (∑ o ∈ packetCopies rowOf e, ‖f o‖) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖∑ o ∈ packetCopies rowOf e, f o‖ := norm_nonneg _
      nlinarith [htri, h0]
    refine hsq.trans ?_
    refine (sq_sum_le_card_mul_sum_sq (s := packetCopies rowOf e) (f := fun o => ‖f o‖)).trans ?_
    have hcard : ((packetCopies rowOf e).card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD e
    have hnn : (0 : ℝ) ≤ ∑ o ∈ packetCopies rowOf e, ‖f o‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    exact mul_le_mul_of_nonneg_right hcard hnn
  calc ∑ e : Row, ‖∑ o ∈ packetCopies rowOf e, f o‖ ^ 2
      ≤ ∑ e : Row, (D : ℝ) * ∑ o ∈ packetCopies rowOf e, ‖f o‖ ^ 2 :=
        Finset.sum_le_sum fun e _ => hfibre e
    _ = (D : ℝ) * ∑ e : Row, ∑ o ∈ packetCopies rowOf e, ‖f o‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (D : ℝ) * ∑ o, ‖f o‖ ^ 2 := by
        rw [sum_over_packetCopies rowOf fun o => ‖f o‖ ^ 2]

/-- A **multiplicity certificate**: the uniform fibre bound is data, supplied
with a proof, never inferred. -/
structure PacketMultiplicityCertificate (Occ Row : Type*) [Fintype Occ] [Fintype Row]
    [DecidableEq Row] where
  rowOf : Occ → Row
  /-- The uniform analytic multiplicity. -/
  D : ℕ
  fibre_card_le : ∀ e : Row, (packetCopies rowOf e).card ≤ D

/-- The certificate yields the assembly cost. -/
theorem PacketMultiplicityCertificate.energy_le
    (C : PacketMultiplicityCertificate Occ Row) (f : Occ → ℂ) :
    ∑ e : Row, ‖∑ o ∈ packetCopies C.rowOf e, f o‖ ^ 2 ≤ C.D * ∑ o, ‖f o‖ ^ 2 :=
  multiplicity_energy_le C.rowOf f C.D C.fibre_card_le

/-! ## Firewall -/

/-- **Multiplicity is not a geometric quantity.**  Distinct analytic
occurrences may share a physical row even when each occurrence is "geometrically
one edge": here two occurrences map to a single row, so the analytic
multiplicity is `2` although the row set has one element.  Multiplicity must
therefore be certified, not inferred from geometric injectivity. -/
theorem multiplicity_not_from_injectivity :
    (packetCopies (fun _ : Fin 2 => (0 : Fin 1)) 0).card = 2 := by
  decide

end TwinPrimeProject.NANC.Gate1A.V95
