import RequestProject.NANC.Gate1B.V11PrimeExtremaTwistFirewall
import RequestProject.NANC.Gate1B.V11SourceMultiplierStructure
import RequestProject.NANC.Gate1B.V11GeneratedTypeIIReassembly
import RequestProject.NANC.Gate1B.V11V10Compatibility

/-!
# V11 · Gate 1B — counterguards A–F

Finite countermodels that permanently block the six false upgrades:

* **A** generated class ≠ arbitrary 1-bounded functions;
* **B** pure Mellin control ≠ `P⁻`/`P⁺` twist control;
* **C** fixed-multiplier operator bounds ≠ moving multiplier-family bound;
* **D** ℓ² multiplier energy ≠ coherent source-multiplier cancellation;
* **E** the conditional generated-Type-II compiler ≠ a Ford–Maynard theorem;
* **F** generated analytic leaves ≠ Gate-1B closure without the V10 source pins.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-! ## Ramp facts used by counterguard A -/

/-- Below the plateau the window is `1`. -/
theorem rampR_of_le (a b n : ℕ) (h : n ≤ a) : rampR a b n = 1 := by
  unfold rampR; simp [h]

/-- Above the support the window is `0`. -/
theorem rampR_of_ge (a b n : ℕ) (h : ¬ n ≤ a) (h2 : b ≤ n) : rampR a b n = 0 := by
  unfold rampR; simp [h, h2]

/-- Strictly inside the ramp the window is `< 1`. -/
theorem rampR_lt_one (a b n : ℕ) (h : ¬ n ≤ a) (h2 : ¬ b ≤ n) : rampR a b n < 1 := by
  unfold rampR
  rw [if_neg h, if_neg h2]
  have han : (a : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_not_ge h
  have hnb : (n : ℝ) < (b : ℝ) := by exact_mod_cast lt_of_not_ge h2
  rw [div_lt_one (by linarith)]
  linarith

/-! ## Counterguard A — the generated class is a genuine restriction -/

/-- **COUNTERGUARD A.**  There is a 1-bounded coefficient sequence that is not
the semantics of *any* admissible generated atom.  Hence "generated" is a real
restriction, not a synonym for "arbitrary 1-bounded". -/
theorem counterguard_A_generatedAtoms_are_not_all_unitBounded :
    ∃ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) ∧
      ∀ a : GenAtom, a.Admissible → ∃ n, f n ≠ semAtom a n := by
  classical
  refine ⟨fun n => if n = 3 ∨ n = 5 then 1 else 0, ?_, ?_⟩
  · intro n; by_cases h : n = 3 ∨ n = 5 <;> simp [h]
  · intro a ha
    cases a with
    | mobius => exact ⟨1, by norm_num [semAtom]⟩
    | constant c =>
        rcases eq_or_ne c 0 with rfl | hc
        · exact ⟨3, by norm_num [semAtom]⟩
        · exact ⟨1, by simpa [semAtom] using Ne.symm hc⟩
    | boxCutoff lo hi =>
        by_cases h3 : lo ≤ 3 ∧ 3 ≤ hi
        · by_cases h5 : lo ≤ 5 ∧ 5 ≤ hi
          · refine ⟨4, ?_⟩
            have h4 : lo ≤ 4 ∧ 4 ≤ hi :=
              ⟨le_trans h3.1 (by norm_num), le_trans (by norm_num) h5.2⟩
            norm_num [semAtom, h4]
          · exact ⟨5, by norm_num [semAtom, h5]⟩
        · exact ⟨3, by norm_num [semAtom, h3]⟩
    | smoothWeight p q =>
        have hpq : p < q := ha
        by_cases h1 : 1 ≤ p
        · refine ⟨1, ?_⟩
          rw [semAtom, rampR_of_le p q 1 h1]
          norm_num
        · have hp0 : p = 0 := by omega
          subst hp0
          refine ⟨3, ?_⟩
          have hne : rampR 0 q 3 ≠ 1 := by
            by_cases hq : q ≤ 3
            · rw [rampR_of_ge 0 q 3 (by norm_num) hq]; norm_num
            · exact ne_of_lt (rampR_lt_one 0 q 3 (by norm_num) hq)
          rw [semAtom]
          norm_num
          intro hcontra
          exact hne (by exact_mod_cast hcontra.symm)
    | mellinTwist t => exact ⟨1, by norm_num [semAtom]⟩
    | perfectPowerPullback k =>
        refine ⟨1, ?_⟩
        have hne : ((Finset.range 2).filter (fun m => m ^ k = 1)).Nonempty := ⟨1, by simp⟩
        rw [semAtom, if_pos hne]
        norm_num

/-! ## Counterguard B — pure Mellin ≠ prime-extrema -/

/-- **COUNTERGUARD B (coordinate form).** -/
theorem counterguard_B_mellin_ne_primeExtrema :
    ¬ ∀ (ι : Type) (_ : Fintype ι) (M : TwistCoordinateModel ι) (c : ι → ℂ),
        (∀ i, ‖c i‖ ≤ 1) → M.mellinValue c = 0 → ‖M.extremaValue c‖ ≤ 1 :=
  mellinControl_does_not_imply_primeExtremaControl

/-- **COUNTERGUARD B (semantic form).**  In *any* realisation the `P±` twist is
not a nonzero scalar multiple of the separating Mellin twist. -/
theorem counterguard_B_semantic (E : PrimeExtremaRealisation) (a b : PrimeExtremaAtom)
    (c : ℂ) (hc : c ≠ 0) :
    (fun n => semPrimeExtremaAtom E a n * semPrimeExtremaAtom E b n)
      ≠ (fun n => c * semAtom (.mellinTwist (Real.pi / Real.log 2)) n) := fun h =>
  hc (primeExtremaTwist_is_not_a_mellinTwist E a b c h)

/-! ## Counterguard C — fixed multiplier ≠ moving family -/

/-- **COUNTERGUARD C.** -/
theorem counterguard_C_fixed_ne_moving :
    ¬ ∀ (K : ℕ) (F : FiniteOperatorFamily K 1),
        (∀ t, ‖F.pairing t‖ ≤ 1) → (∑ t, ‖F.A t‖ ^ 2 ≤ 1) → ‖F.value‖ ≤ 1 :=
  fixedMultiplierBounds_do_not_control_movingFamily

/-! ## Counterguard D — ℓ² energy ≠ coherent cancellation -/

/-- **COUNTERGUARD D.**  Two families with identical pairings and identical
multiplier moduli; the aligned one loses `√(2K)`.  Rank-one structure does not
help either. -/
theorem counterguard_D_l2Energy_ne_coherence (K : ℕ) (hK : 0 < K) :
    (∀ t, (antiAlignedFamily K).pairing t = (alignedFamily (2 * K)).pairing t) ∧
    (∀ t, ‖(antiAlignedFamily K).A t‖ = ‖(alignedFamily (2 * K)).A t‖) ∧
    ‖(alignedFamily (2 * K)).value‖ = Real.sqrt ((2 * K : ℕ) : ℝ) :=
  l2Energy_does_not_determine_familyValue K hK

/-- **COUNTERGUARD D′.**  Rank-one source structure gives no moving-family
saving. -/
theorem counterguard_D_rankOne_no_saving (K : ℕ) (hK : 0 < K) :
    (∀ t, ‖(alignedFamily K).pairing t‖ ≤ 1) ∧
    (∑ t, ‖(alignedFamily K).A t‖ ^ 2 ≤ 1) ∧
    Nonempty (SourceRankOne (Fin K) (Fin K) (Fin 1) (alignedFamily K).A) ∧
    ‖(alignedFamily K).value‖ = Real.sqrt K :=
  rankOne_does_not_give_movingFamily_saving K hK

/-! ## Counterguard E — the compiler is not a theorem about Ford–Maynard -/

/-- **COUNTERGUARD E.**  The generated Type-II conclusion can fail, so the
compiler's analytic hypotheses are load-bearing and the compiler is not, by
itself, any unconditional statement. -/
theorem counterguard_E_compiler_is_not_a_theorem :
    ¬ FMPerronGeneratedTypeIIAtScale toyData ∧
      ∀ Packet : Type, ∀ _ : Fintype Packet,
        ¬ Nonempty (GeneratedTypeIIReassembly toyData Packet) :=
  ⟨fmPerronGeneratedTypeII_toy_fails, fun Packet _ => no_reassembly_for_toyData Packet⟩

/-! ## Counterguard F — leaves ≠ Gate-1B closure -/

/-- **COUNTERGUARD F.** -/
theorem counterguard_F_leaves_ne_closure :
    Nonempty (V11AnalyticLeafBundle (fun _ => 0) (fun _ => 0)) ∧
      ¬ Gate1BDet2.Gate1BClosed 2 1 0 :=
  leaves_alone_do_not_close_gate1B

end Gate1BV11
end TwinPrimeProject
