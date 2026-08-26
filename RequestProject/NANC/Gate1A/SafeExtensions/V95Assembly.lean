/-
# NANC Gate 1A v9.5 — source assembly, nuclear cost, and the local/global firewall

Three finite blocks.

**A. Source partition.**  If the packet set splits into a generic part and an
exceptional part *disjointly*, the source is the exact sum of the two
contributions.  If disjointness is not proved, the identity is false — the
countermodel `no_silent_double_counting` forbids assuming it.

**B. Generic nuclear assembly.**  Generic packets that factor as
`a_P · D_P · U_P · Template` assemble with nuclear cost `∑_P |a_P| C_P`.

**C. Local repair ≠ global closure.**  A sector whose local algebra is
completely proved (an exact local value such as `-1/p`) can still have an
unbounded weighted global tally.  No closure certificate may accept local
repair alone.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V95

open Finset

/-! ## A. Source partition -/

/-- **Exact source assembly.**  A disjoint packet partition gives the exact
splitting of the source into generic and exceptional contributions. -/
theorem actualSource_eq_generic_add_exceptions {P : Type*} [DecidableEq P]
    (allPackets generic exceptional : Finset P) (contrib : P → ℂ)
    (hdisj : Disjoint generic exceptional) (hunion : generic ∪ exceptional = allPackets) :
    ∑ p ∈ allPackets, contrib p
      = (∑ p ∈ generic, contrib p) + ∑ p ∈ exceptional, contrib p := by
  rw [← hunion, Finset.sum_union hdisj]

/-- **No silent double counting.**  Without a disjointness proof the assembly
identity is false: overlapping generic and exceptional lists double count. -/
theorem no_silent_double_counting :
    ∃ (allPackets generic exceptional : Finset (Fin 1)) (contrib : Fin 1 → ℂ),
      generic ∪ exceptional = allPackets ∧
      ∑ p ∈ allPackets, contrib p
        ≠ (∑ p ∈ generic, contrib p) + ∑ p ∈ exceptional, contrib p := by
  refine ⟨univ, univ, univ, fun _ => 1, by simp, ?_⟩
  simp

/-! ## B. Generic nuclear assembly -/

variable {E : Type*} [NormedAddCommGroup E]

/-- **Generic nuclear assembly.**  If every generic packet contribution is
bounded by `|a_P| · C_P · ‖Template(P)‖`, the templates are uniformly bounded
by `S`, and the nuclear cost `∑_P |a_P| C_P` is at most `C_total`, then the
assembled generic contribution is bounded by `C_total · S`.

The unitary relabelling `U_P` and the diagonal multiplier `D_P` of the adapter
are exactly what makes the pointwise hypothesis `hop` available; no property of
them beyond that bound is used. -/
theorem genericPackets_nuclearAssembly {P : Type*} [Fintype P] {T : Type*}
    (contribution : P → E) (a : P → ℂ) (C : P → ℝ) (tmpl : P → T) (template : T → E)
    (Ctotal S : ℝ) (hC : ∀ p, 0 ≤ C p)
    (hop : ∀ p, ‖contribution p‖ ≤ ‖a p‖ * C p * ‖template (tmpl p)‖)
    (hsup : ∀ t, ‖template t‖ ≤ S)
    (hcost : ∑ p, ‖a p‖ * C p ≤ Ctotal) (hS : 0 ≤ S) :
    ‖∑ p, contribution p‖ ≤ Ctotal * S := by
  have hstep : ∀ p : P, ‖contribution p‖ ≤ (‖a p‖ * C p) * S := by
    intro p
    refine (hop p).trans ?_
    exact mul_le_mul_of_nonneg_left (hsup (tmpl p))
      (mul_nonneg (norm_nonneg _) (hC p))
  calc ‖∑ p, contribution p‖ ≤ ∑ p, ‖contribution p‖ := norm_sum_le _ _
    _ ≤ ∑ p, (‖a p‖ * C p) * S := Finset.sum_le_sum fun p _ => hstep p
    _ = (∑ p, ‖a p‖ * C p) * S := by rw [Finset.sum_mul]
    _ ≤ Ctotal * S := mul_le_mul_of_nonneg_right hcost hS

/-! ## C. Local repair is not global closure -/

/-- `LocalRepairComplete`: the local algebra of a sector is exactly known. -/
def LocalRepairComplete {α : Type*} (localValue exactValue : α → ℝ) : Prop :=
  ∀ x, localValue x = exactValue x

/-- `PacketTargetClosed`: the *weighted global* packet tally meets the target. -/
def PacketTargetClosed {α : Type*} [Fintype α] (w localValue : α → ℝ) (target : ℝ) : Prop :=
  ∑ x, w x * |localValue x| ≤ target

/-- **Local/global firewall.**  For every target there is a sector whose local
algebra is exactly the Ramanujan value `-1/p` (so `LocalRepairComplete` holds
with room to spare) and whose weighted global tally exceeds the target.  A
closure certificate may therefore never accept `LocalRepairComplete` in place
of `PacketTargetClosed`. -/
theorem localRepair_does_not_imply_targetClosed (target : ℝ) :
    ∃ (w localValue : Fin 1 → ℝ),
      LocalRepairComplete localValue (fun _ => -(1 / 2 : ℝ)) ∧
      (∀ x, 0 ≤ w x) ∧
      ¬ PacketTargetClosed w localValue target := by
  refine ⟨fun _ => 2 * |target| + 2, fun _ => -(1 / 2 : ℝ), fun _ => rfl,
    fun _ => by positivity, ?_⟩
  simp only [PacketTargetClosed, Finset.univ_unique, Finset.sum_singleton, not_le]
  have h : |(-(1 / 2 : ℝ))| = 1 / 2 := by norm_num
  rw [h]
  have := le_abs_self target
  linarith

end TwinPrimeProject.NANC.Gate1A.V95
