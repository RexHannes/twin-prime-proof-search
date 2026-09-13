/-
# Gate1B / R11 / Frontier / CanonicalRootSync : fixture reconciliation  (P7)

Append-only module.  Exact rational arithmetic only; nothing analytic is asserted or inhabited.

Two historical fixtures are reconciled with the retained K = 5, `j = 2` physical constraints.

**A. the old `q = x^{.619}` fixture** — recorded as `fixture619` — is **formally nonphysical**:
its atoms exceed `(1 − η)/5`.  The numerical inequalities it used to pass are exhibited: it
satisfies the *relaxed* condition set `pascadiRevokedRelaxed`, i.e. the set in which the
second-atom capacity row is loosened — the row that the revoked global `e ≤ x^σ` assumption used
to supply.  The relaxation is proved to destroy the firewall (`relaxed_has_no_four_sevenths_ceiling`),
so passing it says nothing.

**B. the `q = x^{.563}` fixture** — recorded as `fixture563` — **passes** the physical exponent
constraints, and is moreover literally Pascadi-callable at a positive slack.  This remains an
exponent/interface statement only: no analytic theorem is supplied or inhabited.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.OpenBoxCertificate

namespace Gate1B.R11.Frontier.CanonicalRootSync

/-! ## A. the old `q = x^{.619}` fixture -/

/-- The old fixture at level exponent `.619`: a small block and two large atoms. -/
def fixture619 : K5Packet := ⟨19/1000, 3/10, 3/10⟩

/-- Its total exponent is `619/1000`. -/
theorem fixture619_theta : fixture619.theta = 619/1000 := by
  norm_num [K5Packet.theta, fixture619]

/-- **The old fixture is formally nonphysical for K = 5, `j = 2`**: its atoms exceed the physical
ceiling `(1 − η)/5`. -/
theorem fixture619_nonphysical : ¬ PhysicalK5 fixture619 := by
  refine not_physical_of_atom_large (p := fixture619) ?_
  norm_num [fixture619]

/-- The exact defect: `a > (1 − η)/5`. -/
theorem fixture619_atom_exceeds : (1 - fixture619.eta)/5 < fixture619.a := by
  norm_num [fixture619]

/-- **The revoked relaxation.**  The same three rows with the second-atom capacity row loosened
from `2/7` to `1` — the loosening that the revoked global `e ≤ x^σ` assumption used to justify. -/
def pascadiRevokedRelaxed : PascadiConditions :=
  { pascadiLiteral with rhsConst := ![6/7, 1, 1/2], rhsSlack := ![6, 6, 1] }

/-- The old fixture *does* satisfy the relaxed numerical inequalities — which is why it once
looked callable. -/
theorem fixture619_relaxed_holds :
    pascadiRevokedRelaxed.holdsAt 0 fixture619.eta fixture619.a fixture619.b := by
  intro i
  fin_cases i <;> norm_num [pascadiRevokedRelaxed, pascadiLiteral, fixture619]

/-- **The relaxation destroys the firewall.**  The relaxed condition set admits a nonnegative
triple with `θ > 4/7`, so no `4/7` capacity ceiling can be derived from it: a numerical pass
against the relaxed rows carries no capacity information. -/
theorem relaxed_has_no_four_sevenths_ceiling :
    ∃ x y z : ℚ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ pascadiRevokedRelaxed.holdsAt 0 x y z
      ∧ 4/7 < x + y + z := by
  refine ⟨19/1000, 3/10, 3/10, by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  intro i
  fin_cases i <;> norm_num [pascadiRevokedRelaxed, pascadiLiteral]

/-- And the old fixture is **not** callable against the *literal* rows: the historical pass was a
pass against the revoked relaxation only. -/
theorem fixture619_not_literally_callable : ¬ PascadiCallable 0 fixture619 := by
  rintro (h | h | h | h | h | h) <;>
    [exact absurd (h 1) (by norm_num [pascadiLiteral, fixture619]);
     exact absurd (h 1) (by norm_num [pascadiLiteral, fixture619]);
     exact absurd (h 1) (by norm_num [pascadiLiteral, fixture619]);
     exact absurd (h 1) (by norm_num [pascadiLiteral, fixture619]);
     exact absurd (h 1) (by norm_num [pascadiLiteral, fixture619]);
     exact absurd (h 1) (by norm_num [pascadiLiteral, fixture619])]

/-! ## B. the `q = x^{.563}` fixture -/

/-- The `q = x^{.563}` fixture: block `η = 283/1000`, atoms `a = b = 7/50`. -/
def fixture563 : K5Packet := ⟨283/1000, 7/50, 7/50⟩

/-- Its total exponent is `563/1000`. -/
theorem fixture563_theta : fixture563.theta = 563/1000 := by
  norm_num [K5Packet.theta, fixture563]

/-- **The `.563` fixture passes the physical exponent constraints.** -/
theorem fixture563_physical : PhysicalK5 fixture563 := by
  norm_num [PhysicalK5, fixture563]

/-- It is below the Pascadi capacity ceiling — consistent with the firewall. -/
theorem fixture563_below_ceiling : fixture563.theta < 4/7 := by
  rw [fixture563_theta]; norm_num

/-- It is above the Wright interface region, so Wright does not cover it. -/
theorem fixture563_above_wright {epsW : ℚ} (h : 0 ≤ epsW) : ¬ WrightRegion epsW fixture563 := by
  unfold WrightRegion
  rw [fixture563_theta]
  push_neg
  linarith

/-- It is moreover **literally Pascadi-callable** at slack `ε_P = 1/2000`: the exponent geometry
of this fixture is compatible with the literal three-atom architecture.  This is an
exponent/interface statement only — no analytic theorem is supplied here. -/
theorem fixture563_callable : PascadiCallable (1/2000) fixture563 := by
  refine Or.inl ?_
  intro i
  fin_cases i <;> norm_num [pascadiLiteral, fixture563]

/-- **The reconciliation.**  The `.619` fixture is nonphysical, the `.563` fixture is physical
and callable, and the open box of `OpenBoxCertificate` is physical, uncovered and above the
capacity ceiling: exactly the three regimes the latest analytic state distinguishes. -/
theorem fixture_reconciliation :
    ¬ PhysicalK5 fixture619 ∧ PhysicalK5 fixture563 ∧ PascadiCallable (1/2000) fixture563
      ∧ PhysicalK5 openBox ∧ ¬ PascadiCallable (1/2000) openBox :=
  ⟨fixture619_nonphysical, fixture563_physical, fixture563_callable, openBox_physical,
    openBox_not_pascadiCallable (by norm_num)⟩

end Gate1B.R11.Frontier.CanonicalRootSync
