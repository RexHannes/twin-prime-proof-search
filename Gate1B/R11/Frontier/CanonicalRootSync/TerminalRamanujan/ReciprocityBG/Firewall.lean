/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
the firewalls of this layer  (B11)

Append-only module.  It states, in kernel-checked form, what this layer does **not** prove.

* the exact arithmetic dictionary (CRT phase normalisation, reciprocity, Möbius provenance,
  dual-frequency split, allocation counting) is unconditional;
* the external analytic inputs are ordinary propositions, all of them refutable by explicit
  data, hence not theorems and not axioms;
* no Bourgain–Garaev theorem is created, assumed or approximated anywhere in this directory;
* the canonical `j = 2` owner and the terminal EP-M2 owner stay open, the canonical cut is
  unchanged, and no twin-prime statement is claimed anywhere.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Bridge
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Reciprocity
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.ComplementCost

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. The dictionary is unconditional -/

/-- **The exact dictionary needs no analytic input.**  The CRT congruences, the phase
factorisation in `ℚ/ℤ`, the reciprocity identity, the exact Möbius provenance and the exact
dual-frequency split all hold with no hypothesis beyond their stated algebraic ones. -/
theorem dictionary_unconditional :
    (∀ C γ s : ℤ, shiftedJ C γ s ≡ -s [ZMOD C])
      ∧ (∀ (e z z' k : ℤ), z' = z + e * k → z' - z = e * k)
      ∧ (∀ (D : DualData) (Nlow : ℝ → ℕ) (x : ℝ),
          D.fullDualRow x = D.lowDualRow Nlow x + D.highDualRow Nlow x) :=
  ⟨fun _ _ _ => J_modEq_C, fun _ _ _ _ h => source_relation_retains_e h,
    fun D Nlow x => dual_row_split D Nlow x⟩

/-! ## 2. The analytic inputs are open propositions, not theorems -/

/-- **All external inputs of this layer are open.**  Each is refuted by explicit data, so none
of them has been silently upgraded, and none is an axiom. -/
theorem external_inputs_open :
    (∃ D : DualData, ¬ LowDualBourgainGaraevBound D 0)
      ∧ (∃ D : DualData, ¬ HighDualJointAverageBound D 0)
      ∧ (∃ Mtop : ℝ → ℝ, ¬ EPM2TopBound Mtop 0)
      ∧ (∃ DB : ℝ → ℝ, ¬ J2ResidualCenteredBound DB 0) :=
  ⟨lowDualBourgainGaraevBound_open, highDualJointAverageBound_open,
    terminal_owner_still_open, j2_owner_still_open⟩

/-- **The averaging firewall.**  A fixed-frequency atom bound is strictly weaker than the joint
average the consumer needs. -/
theorem averaging_firewall :
    ∃ D : DualData, FixedFrequencyAtomBound D 0 ∧ ¬ HighDualJointAverageBound D 0 :=
  atoms_do_not_imply_joint

/-- **The realisation firewall.**  The single remaining exact identification below EP-M2 cannot
be dispensed with. -/
theorem realisation_firewall :
    indexSetRealisation toyData ∧ chartInjectivity toyData ∧ maskRealisation toyData
      ∧ sourceSupportRealisation toyData ∧ sourceWeightRealisation toyData
      ∧ normalisationRealisation toyData
      ∧ ¬ epM2RowIdentification toyData
      ∧ ¬ epM2Realisation toyData.canonicalFamily toyData.epM2Family :=
  epM2RowIdentification_load_bearing

/-- **The `C`-factor firewall of the phase normalisation** and **the source-relation firewall**
of the reciprocity step, together. -/
theorem phase_firewalls :
    (CongMod1 (phaseLHS 1 1 3 0 1 1) (phaseRHS 1 1 1 3 0 1 0 1)
      ∧ ¬ CongMod1 (phaseLHS 1 1 3 0 1 1)
          (-(((2 * 1 * 0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) - ((2 * 1 * 0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)))
      ∧ (∀ k : ℤ, recipPhase 1 (2 * 1) 1 1 1 - recipPhase 1 (2 * 1) 1 1 2
          ≠ ((2 * 1 * k : ℤ) : ℚ) / ((1 * 1 * 1 * 1 * 2 : ℤ) : ℚ)) :=
  ⟨C_factor_not_removable, reduction_needs_source_relation.2⟩

/-! ## 3. Nothing is claimed beyond the conditional bridge -/

/-- **The bridge is conditional.**  Even with the whole dictionary available, the canonical
`j = 2` owner is not a theorem. -/
theorem layer_claims_nothing_unconditional :
    (∀ (D : DualData) (Nlow : ℝ → ℕ) (x : ℝ),
        D.fullDualRow x = D.lowDualRow Nlow x + D.highDualRow Nlow x)
      ∧ ∃ DB : ℝ → ℝ, ¬ J2ResidualCenteredBound DB 0 :=
  ⟨fun D Nlow x => dual_row_split D Nlow x, j2_owner_still_open⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
