/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : the JCORE analytic owners  (J10)

Append-only module.  The three JCORE analytic propositions are ordinary propositions in the
repository's existing `ScalarBudget` style.  **None of them is inhabited**, none is an axiom, and
no external analytic theorem (Bourgain–Garaev, Weil, Wu–Xi, Shen, Bettin–Chandee,
Blomer–Pascadi, Milićević–Qin–Wu) is imported, assumed or named as a theorem anywhere.

Proved here: the purely deterministic reassembly

```
JCoreEqualBudget + SourceCoreOverlapBudget + JCoreOffCleanBound  ⇒  JCoreBound,
```

given the exact three-way split of the corresponding real families (which is the family-level
image of `jExpand_three_way`).

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.CanonicalRoot
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.FactorisationData

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. The owners -/

/-- **`JCoreEqualBudget`** — the equal-rational-frequency part of the JCORE moment obeys the
required budget.  EXTERNAL_ANALYTIC / OPEN — stated, never inhabited, not an axiom. -/
def JCoreEqualBudget (JEq : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget JEq (S0 + 2)

/-- **`SourceCoreOverlapBudget`** — the payment for the complement of the clean source/core
support `(z, vṽ) = 1`.  EXTERNAL_ANALYTIC / OPEN — stated, never inhabited, not an axiom. -/
def SourceCoreOverlapBudget (JOv : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget JOv (S0 + 2)

/-- **`JCoreOffCleanBound`** — *the* terminal JCORE analytic owner: the clean off-diagonal
(unequal-frequency, `(z, vṽ) = 1`) part of the JCORE moment obeys the required budget.
EXTERNAL_ANALYTIC / OPEN — stated, never inhabited, not an axiom. -/
def JCoreOffCleanBound (JCl : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget JCl (S0 + 2)

/-- **`JCoreOffBound`** — the whole off-diagonal part obeys the required budget. -/
def JCoreOffBound (JOff : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget JOff (S0 + 2)

/-- **`JCoreBound`** — the JCORE moment obeys the required budget. -/
def JCoreBound (J : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget J (S0 + 2)

/-! ## 2. Deterministic reassembly -/

/-- **`SourceCoreOverlapBudget` + `JCoreOffCleanBound` ⇒ `JCoreOffBound`**, given the exact
clean/overlap split of the families.  No monotonicity under deleting terms is used: the split is
an identity. -/
theorem jCoreOffBound_of_clean_and_overlap {JOff JCl JOv : ℝ → ℝ} {S0 : ℕ}
    (hsplit : ∀ x, JOff x = JCl x + JOv x)
    (hcl : JCoreOffCleanBound JCl S0) (hov : SourceCoreOverlapBudget JOv S0) :
    JCoreOffBound JOff S0 :=
  scalarBudget_congr hsplit (scalarBudget_add hcl hov)

/-- **The JCORE reassembly**: the three owners plus the exact three-way split give `JCoreBound`.
Every arrow is deterministic; all analytic content sits in the three hypotheses. -/
theorem jCoreBound_of_owners {J JEq JCl JOv : ℝ → ℝ} {S0 : ℕ}
    (hsplit : ∀ x, J x = JEq x + JCl x + JOv x)
    (heq : JCoreEqualBudget JEq S0) (hcl : JCoreOffCleanBound JCl S0)
    (hov : SourceCoreOverlapBudget JOv S0) :
    JCoreBound J S0 :=
  scalarBudget_congr hsplit (scalarBudget_add (scalarBudget_add heq hcl) hov)

/-! ## 3. The owners are open and load-bearing -/

/-- The clean off-diagonal owner is not a theorem. -/
theorem jCoreOffCleanBound_open : ∃ JCl : ℝ → ℝ, ¬ JCoreOffCleanBound JCl 0 :=
  ⟨fun x => x, identity_not_budgeted 1⟩

/-- The overlap owner is not a theorem. -/
theorem sourceCoreOverlapBudget_open : ∃ JOv : ℝ → ℝ, ¬ SourceCoreOverlapBudget JOv 0 :=
  ⟨fun x => x, identity_not_budgeted 1⟩

/-- The equal-frequency owner is not a theorem. -/
theorem jCoreEqualBudget_open : ∃ JEq : ℝ → ℝ, ¬ JCoreEqualBudget JEq 0 :=
  ⟨fun x => x, identity_not_budgeted 1⟩

/-- **The clean off-diagonal owner is load-bearing**: the other two owners alone do not give
`JCoreBound`. -/
theorem jCore_needs_clean_owner :
    ∃ (J JEq JCl JOv : ℝ → ℝ), (∀ x, J x = JEq x + JCl x + JOv x)
      ∧ JCoreEqualBudget JEq 0 ∧ SourceCoreOverlapBudget JOv 0
      ∧ ¬ JCoreOffCleanBound JCl 0 ∧ ¬ JCoreBound J 0 :=
  ⟨fun x => x, fun _ => 0, fun x => x, fun _ => 0, fun x => by ring,
    zero_budgeted 2, zero_budgeted 2, identity_not_budgeted 1, identity_not_budgeted 1⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
