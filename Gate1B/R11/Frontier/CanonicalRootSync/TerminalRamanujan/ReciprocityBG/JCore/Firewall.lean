/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : firewalls  (J12)

Append-only module.  Everything here is a kernel-checked *negative* statement: what the JCORE
algebra does **not** give.

* §1 the second-factor firewall: a finite fixture with two legal values of `e` whose source
  factors agree while the second reciprocal factors differ, so source-factor cancellation alone
  does not give JCORE phase cancellation;
* §2 the external-analysis firewall: no external analytic theorem is imported or assumed, and the
  exact algebra of this directory does not imply any JCORE budget;
* §3 the non-claims: `JCoreOffCleanBound` is not proved, `EPM2TopBound` is not inhabited,
  `J2ResidualCenteredBound` is not analytically proved, R11 / HSTAR / Gate1B are not closed, and
  no twin-prime statement is made anywhere.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.Bridge

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. Exponentials separate phases -/

/-- `e(a) = e(b)` exactly when `a ≡ b (mod 1)`: the additive character is faithful on the
circle. -/
theorem ee_eq_iff_congMod1 (a b : ℚ) : ee a = ee b ↔ CongMod1 a b := by
  constructor
  · intro h
    have hb : ee b ≠ 0 := by
      unfold ee
      exact Complex.exp_ne_zero _
    have h1 : ee (a - b) = 1 := by
      have hmul : ee (a - b) * ee b = ee a := by rw [← ee_add]; congr 1; ring
      rw [h] at hmul
      exact mul_right_cancel₀ hb (by rw [one_mul]; exact hmul)
    obtain ⟨k, hk⟩ := (ee_eq_one_iff (a - b)).mp h1
    exact ⟨k, hk⟩
  · exact ee_congr

/-! ## 2. The second-factor firewall -/

/-- **Source-factor cancellation does not give JCORE phase cancellation.**  Finite fixture:
`z = 3`, `A_s = 1`, `c = 5`, `B_c = 1`, label `k = 1`, and the two legal values `e = 1`, `e = 4`.
Both `e`-values have `1` as inverse modulo `3`, so the two source factors are *equal*; the second
reciprocal factors are the inverses of `3 + e` modulo `5`, namely `4` and `3`, and they differ —
already in `ℚ / ℤ`, hence as exponentials. -/
theorem second_factor_not_determined_by_source :
    IsInverseMod 1 1 3 ∧ IsInverseMod 4 1 3
      ∧ IsInverseMod (3 + 1 * 1) 4 5 ∧ IsInverseMod (3 + 4 * 1) 3 5
      ∧ sourcePhase 1 1 3 = sourcePhase 1 1 3
      ∧ ee (crtPhase 1 4 5) ≠ ee (crtPhase 1 3 5) := by
  refine ⟨by unfold IsInverseMod; decide, by unfold IsInverseMod; decide,
    by unfold IsInverseMod; decide, by unfold IsInverseMod; decide, rfl, ?_⟩
  rw [Ne, ee_eq_iff_congMod1]
  rintro ⟨k, hk⟩
  unfold crtPhase at hk
  norm_num at hk
  have hk5 : (1 : ℤ) = 5 * k := by
    have h5 : (1 : ℚ) = 5 * (k : ℚ) := by linarith [hk]
    exact_mod_cast h5
  omega

/-! ## 3. The external-analysis firewall -/

/-- **The exact JCORE algebra implies no budget.**  Every identity of this directory holds for
arbitrary abstract coefficient families, and there are families violating each owner: no analytic
conclusion follows from the algebra. -/
theorem jCore_algebra_implies_no_budget :
    (∀ (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ),
        jExpand O Iset F = jEqual O Iset F + jOffClean O Iset F + jOffOverlap O Iset F)
      ∧ (∃ JCl : ℝ → ℝ, ¬ JCoreOffCleanBound JCl 0)
      ∧ (∃ J : ℝ → ℝ, ¬ JCoreBound J 0) :=
  ⟨jExpand_three_way, jCoreOffCleanBound_open, ⟨fun x => x, identity_not_budgeted 1⟩⟩

/-- **The determinant algebra implies no cancellation.**  `Δ ≠ 0` off the equal-frequency class
is exact, but it does not bound anything: the clean off-diagonal owner stays open. -/
theorem delta_nonvanishing_is_not_a_bound :
    (∀ i j : Core, 0 < i.u → 0 < i.v → 0 < j.u → 0 < j.v →
        UnequalRationalFrequency i j → Delta i j ≠ 0)
      ∧ (∃ JCl : ℝ → ℝ, ¬ JCoreOffCleanBound JCl 0) :=
  ⟨fun _ _ hiu hiv hju hjv h => delta_ne_zero_of_unequal hiu hiv hju hjv h,
    jCoreOffCleanBound_open⟩

/-! ## 4. The non-claims -/

/-- **The non-claims of this run, in kernel-checked form.**  None of the terminal objects is
closed: the clean off-diagonal JCORE owner, the EP-M2 terminal owner and the canonical `j = 2`
owner are all still refutable by explicit families, and the general-label combined conductor is
not established. -/
theorem jCore_non_claims :
    (∃ JCl : ℝ → ℝ, ¬ JCoreOffCleanBound JCl 0)
      ∧ (∃ JOv : ℝ → ℝ, ¬ SourceCoreOverlapBudget JOv 0)
      ∧ (∃ JEq : ℝ → ℝ, ¬ JCoreEqualBudget JEq 0)
      ∧ (∃ Mtop : ℝ → ℝ, ¬ EPM2TopBound Mtop 0)
      ∧ (∃ DB : ℝ → ℝ, ¬ J2ResidualCenteredBound DB 0) :=
  ⟨jCoreOffCleanBound_open, sourceCoreOverlapBudget_open, jCoreEqualBudget_open,
    terminal_owner_still_open, j2_owner_still_open⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
