import RequestProject.NANC.Gate01Switch.GenericSwitched
import Gate1B.SafeExtensions.FullNineANOVA
import RequestProject.NANC.Gate1B.V10CanonicalZeroMode

/-!
# V10 · Gate 1B — the packet census and the abstract reassembly compiler

## Part A — the census

The packet index is recorded as **DATA** (`PacketLabel`), not as hypotheses: a
defect subset `J ⊆ Fin 9`, a switched-census face (higher prime power / repeated
prime / generic), an additive-frequency face (zero / nonzero) and a unit face
(unit / nonunit).

For every face family that is a *literal finite partition already present in the
bank* we prove pairwise disjointness and exhaustion:

* switched census : `higherPrimePowerPart ∪ repeatedPart ∪ genericPart = S`
  (the bank's own `primePart` / `repeatedPart` / `genericPart` filters), plus the
  exact operator split `switchedOperator_three_way`;
* additive frequency : `{0} ∪ (univ.erase 0) = univ` in `ZMod q`;
* unit face : `filter IsUnit ∪ filter ¬IsUnit = univ` in `ZMod q`;
* defect subset : the Full-Nine ANOVA expansion (`Gate1B.SafeExtensions.fullNine_anova`)
  exhausts the powerset of `Fin 9`.

**No q-pair face (same-q / shared-g / cross-coprime) is introduced**: those are
named in the research ledger but are not literal finite partitions in the bank,
so inventing them here is forbidden.

## Part B — the reassembly compiler

`norm_sum_le_of_packet_budget` and `norm_rawSource_le_of_packet_budget` are
generic finite budget compilers: the packet values and the budgets are arbitrary
supplied data (`packetValue` is *not* defined from `budget`, and `globalBudget`
is *not* defined as the left-hand side).  Hostile tests show the leaf bounds are
load bearing and that an empty packet family certifies nothing.
-/

namespace TwinPrimeProject
namespace Gate1BV10

open Finset Gate01Switch

/-! ## Part A.1 — the packet label type (DATA) -/

/-- The switched census face. -/
inductive CensusFace
  | higherPrimePower
  | repeatedPrime
  | generic
  deriving DecidableEq, Repr

/-- The additive-frequency face. -/
inductive FreqFace
  | zeroFrequency
  | nonzeroFrequency
  deriving DecidableEq, Repr

/-- The unit face. -/
inductive UnitFace
  | unit
  | nonunit
  deriving DecidableEq, Repr

/-- **The packet index, as data.**  A defect subset of the nine coordinates, a
switched-census face, an additive-frequency face and a unit face. -/
structure PacketLabel where
  /-- The ANOVA defect subset `J ⊆ Fin 9`. -/
  defect : Finset (Fin 9)
  /-- Higher prime power / repeated prime / generic. -/
  census : CensusFace
  /-- Zero or nonzero additive frequency. -/
  freq : FreqFace
  /-- Unit or nonunit residue. -/
  unitFace : UnitFace
  deriving DecidableEq

/-- The defect order of a packet. -/
def PacketLabel.defectOrder (p : PacketLabel) : ℕ := p.defect.card

/-! ## Part A.2 — the switched census is a literal partition -/

variable (S : Finset (ℕ × ℕ))

theorem hpp_disjoint_repeated :
    Disjoint (higherPrimePowerPart S) (repeatedPart S) :=
  (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
    (primePart_disjoint_higherPrimePowerPart S).symm)

theorem hpp_disjoint_generic :
    Disjoint (higherPrimePowerPart S) (genericPart S) :=
  (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
    (primePart_disjoint_higherPrimePowerPart S).symm)

theorem repeated_disjoint_generic :
    Disjoint (repeatedPart S) (genericPart S) :=
  repeatedPart_disjoint_genericPart S

/-- **Census exhaustion**: the three faces cover the whole divisor-pair set. -/
theorem census_union :
    higherPrimePowerPart S ∪ repeatedPart S ∪ genericPart S = S := by
  have haux : primePart S = repeatedPart S ∪ genericPart S :=
    (Finset.filter_union_filter_not_eq _ (primePart S)).symm
  rw [Finset.union_assoc, ← haux, Finset.union_comm]
  exact primePart_union_higherPrimePowerPart S

/-- The census union, in the form `HPP ∪ (REP ∪ GEN) = S`. -/
theorem census_union' :
    higherPrimePowerPart S ∪ (repeatedPart S ∪ genericPart S) = S := by
  rw [← Finset.union_assoc]
  exact census_union S

/-! ## Part A.3 — the frequency and unit faces are literal partitions -/

variable {q : ℕ} [NeZero q]

theorem freq_disjoint :
    Disjoint ({0} : Finset (ZMod q)) ((Finset.univ : Finset (ZMod q)).erase 0) := by
  classical
  simp

theorem freq_union :
    ({0} : Finset (ZMod q)) ∪ ((Finset.univ : Finset (ZMod q)).erase 0)
      = (Finset.univ : Finset (ZMod q)) := by
  classical
  ext a
  by_cases h : a = 0 <;> simp [h]

theorem unit_disjoint :
    Disjoint ((Finset.univ : Finset (ZMod q)).filter (fun n => IsUnit n))
      ((Finset.univ : Finset (ZMod q)).filter (fun n => ¬ IsUnit n)) := by
  classical
  exact Finset.disjoint_filter_filter_not _ _ _

theorem unit_union :
    ((Finset.univ : Finset (ZMod q)).filter (fun n => IsUnit n))
      ∪ ((Finset.univ : Finset (ZMod q)).filter (fun n => ¬ IsUnit n))
      = (Finset.univ : Finset (ZMod q)) := by
  classical
  exact Finset.filter_union_filter_not_eq _ _

/-! ## Part A.4 — the defect face: Full-Nine census -/

/-- **Full-Nine census** (the bank's ANOVA identity, reused verbatim):
`∏ (f i + δ i) = ∑_{J ⊆ Fin 9} δ_J f_{Jᶜ}`. -/
theorem fullNine_census (f d : Fin 9 → ℝ) :
    ∏ i : Fin 9, (f i + d i)
      = ∑ J ∈ (Finset.univ : Finset (Fin 9)).powerset,
          (∏ j ∈ J, d j) * ∏ i ∈ Finset.univ \ J, f i :=
  Gate1B.SafeExtensions.fullNine_anova f d

/-- Every defect subset occurs exactly once in the census. -/
theorem fullNine_census_index (J : Finset (Fin 9)) :
    J ∈ (Finset.univ : Finset (Fin 9)).powerset := by
  simp

/-! ## Part B — the abstract reassembly compiler -/

variable {P : Type*} [Fintype P]

/-- **Packet budget compiler.**  Face-by-face norm bounds assemble. -/
theorem norm_sum_le_of_packet_budget (packetValue : P → ℂ) (budget : P → ℝ)
    (h : ∀ p, ‖packetValue p‖ ≤ budget p) :
    ‖∑ p, packetValue p‖ ≤ ∑ p, budget p :=
  le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => h p)

/-- **`norm_rawSource_le_of_packet_budget`.**  If the raw source is the packet
sum, every packet respects its budget, and the budgets fit inside the global
budget, then the raw source respects the global budget.

`packetValue`, `budget`, `rawSource` and `globalBudget` are arbitrary supplied
data; none is defined in terms of another. -/
theorem norm_rawSource_le_of_packet_budget (rawSource : ℂ) (packetValue : P → ℂ)
    (budget : P → ℝ) (globalBudget : ℝ)
    (hsource : rawSource = ∑ p, packetValue p)
    (hpacket : ∀ p, ‖packetValue p‖ ≤ budget p)
    (hbudget : ∑ p, budget p ≤ globalBudget) :
    ‖rawSource‖ ≤ globalBudget := by
  rw [hsource]
  exact le_trans (norm_sum_le_of_packet_budget packetValue budget hpacket) hbudget

/-! ## Part B.2 — hostile tests -/

/-- **Hostile test 3.**  Without the leaf bounds the compiler proves nothing: a
packet family can exceed its budgets. -/
theorem packet_budget_needs_leaf_bounds :
    ∃ (v : Fin 1 → ℂ) (b : Fin 1 → ℝ), ¬ ‖∑ p, v p‖ ≤ ∑ p, b p := by
  refine ⟨fun _ => 1, fun _ => 0, ?_⟩
  simp

/-- **Hostile test 5.**  An empty packet family certifies nothing: its packet sum
is `0`, so it cannot be the source decomposition of a nonzero raw source. -/
theorem empty_packet_family_certifies_nothing (packetValue : Fin 0 → ℂ)
    (rawSource : ℂ) (hsource : rawSource = ∑ p, packetValue p) :
    rawSource = 0 := by
  simpa using hsource

/-- **Hostile test 5'.**  In particular a nonzero physical source admits no
empty-packet decomposition. -/
theorem nonzero_source_has_no_empty_decomposition :
    ¬ ∃ packetValue : Fin 0 → ℂ, (1 : ℂ) = ∑ p, packetValue p := by
  rintro ⟨v, hv⟩
  simp at hv

/-- The compiler is not self-certifying: the conclusion for one budget family
does not produce the packet bounds. -/
theorem packet_compiler_not_self_certifying :
    ∃ (v : Fin 2 → ℂ) (b : Fin 2 → ℝ),
      ‖∑ p, v p‖ ≤ ∑ p, b p ∧ ¬ ‖v 0‖ ≤ b 0 := by
  refine ⟨![1, -1], ![0, 2], ?_, ?_⟩
  · simp [Fin.sum_univ_two]
  · simp

end Gate1BV10
end TwinPrimeProject
