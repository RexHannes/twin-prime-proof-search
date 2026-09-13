/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the Pascadi / Yang / Wright
firewall  (T12)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

No external analytic theorem is formalised from an informal range description.  What is allowed,
and what is done here:

* exponent / range predicates are defined;
* exact rational inequalities about them are proved (e.g. `.624 < 5/8`);
* a purely structural terminal hypothesis `TerminalTriplyFactorableHypothesis` is defined,
  its structural consequence (the small-complement relation) is proved;
* it is proved that the structural hypothesis **does not** imply the terminal analytic owner —
  so no `PascadiBound`-style theorem is created, assumed, or silently used, and the
  factorable-modulus adapter stays outside the proved route.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ComplementaryQuotient
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TerminalOwner

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. Exponent / range predicates (interface level only) -/

/-- The Pascadi window as a rational predicate on the conductor exponent. -/
def inPascadiWindow (θ : ℚ) : Prop := 4 / 7 < θ ∧ θ < 5 / 8

/-- The recorded chamber exponent `.624` lies in the Pascadi window: an exact rational fact
about exponents, and nothing more. -/
theorem chamber_624_in_window : inPascadiWindow (624 / 1000) := by
  constructor <;> norm_num

/-- `.624 < 5/8`, isolated as requested. -/
theorem chamber_624_lt_five_eighths : (624 : ℚ) / 1000 < 5 / 8 := by norm_num

/-- The previously banked open `j = 2` box exponent `.621` also sits in the window. -/
theorem chamber_621_in_window : inPascadiWindow (621 / 1000) := by
  constructor <;> norm_num

/-! ## 2. The structural terminal hypothesis -/

/-- **`TerminalTriplyFactorableHypothesis`** — the *structural* terminal hypothesis: the cutoff
is `q₀ = Q_max / R_cut` in the integer sense.  This is a support statement about the terminal
band; it carries no analytic content and is never used as an analytic input. -/
def TerminalTriplyFactorableHypothesis (q0 Qmax Rcut : ℕ) : Prop :=
  0 < q0 ∧ Qmax ≤ q0 * Rcut

/-- The structural hypothesis yields exactly the small-complement relation, and nothing else. -/
theorem terminal_factorable_small_complement {q0 Qmax Rcut : ℕ}
    (h : TerminalTriplyFactorableHypothesis q0 Qmax Rcut) {q m : ℕ}
    (hm : 0 < m) (hq : q0 < q) (hqm : q * m ≤ Qmax) : m < Rcut :=
  terminal_small_complement hm h.2 hq hqm

/-- **The firewall.**  The structural terminal hypothesis is satisfiable, yet it does not imply
the terminal analytic owner: there is no proved adapter
`TerminalTriplyFactorableHypothesis → EPM2TopBound`, and none is assumed. -/
theorem factorable_structure_does_not_imply_topBound :
    (∃ q0 Qmax Rcut : ℕ, TerminalTriplyFactorableHypothesis q0 Qmax Rcut)
      ∧ (∃ Mtop : ℝ → ℝ, ¬ EPM2TopBound Mtop 0) :=
  ⟨⟨1, 1, 1, by norm_num [TerminalTriplyFactorableHypothesis]⟩,
    ⟨fun x => x, identity_not_budgeted 1⟩⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
